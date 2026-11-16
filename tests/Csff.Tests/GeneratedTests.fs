module Csff.Tests.GeneratedTests

open System
open System.Diagnostics
open Csff.Conformance
open Csff.Lexer
open Csff.Printer
open Expecto
open FsCheck
open FsCheck.FSharp
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Text

let private legacyShrinkSource source =
    let root = GeneratedOutput.parse source

    let removable (node: SyntaxNode) =
        let parent =
            if isNull node.Parent then
                ""
            else
                node.Parent.GetType().Name

        let kind = node.GetType().Name

        parent = "CompilationUnitSyntax"
        || parent = "BlockSyntax"
        || parent = "ClassDeclarationSyntax"
        || parent = "StructDeclarationSyntax"
        || parent = "NamespaceDeclarationSyntax"
        || kind = "UsingDirectiveSyntax"

    let nodes = root.DescendantNodes() |> Seq.filter removable |> Seq.toArray

    seq {
        for node in root.DescendantNodes() do
            match node with
            | :? BlockSyntax as block ->
                let start = block.OpenBraceToken.Span.End
                let finish = block.CloseBraceToken.Span.Start

                if finish >= start then
                    yield source.Substring(start, finish - start)
            | :? AttributeListSyntax ->
                yield source.Remove(node.FullSpan.Start, node.FullSpan.Length)
            | :? ParameterListSyntax as parameters when parameters.Parameters.Count > 0 ->
                let start = parameters.OpenParenToken.Span.End
                let finish = parameters.CloseParenToken.Span.Start
                yield source.Remove(start, finish - start)
            | _ -> ()

        for node in root.DescendantNodes() |> Seq.sortByDescending (fun node -> node.Span.Length) do
            if node :? ExpressionSyntax && node.Span.Length > 1 then
                yield source.Remove(node.Span.Start, node.Span.Length).Insert(node.Span.Start, "x")

        for trivia in root.DescendantTrivia() do
            if
                trivia.IsKind(SyntaxKind.WhitespaceTrivia)
                || trivia.IsKind(SyntaxKind.EndOfLineTrivia)
            then
                yield source.Remove(trivia.Span.Start, trivia.Span.Length)

        for token in root.DescendantTokens() do
            if token.IsKind(SyntaxKind.IdentifierToken) && token.Text.Length > 1 then
                yield
                    source.Remove(token.Span.Start, token.Span.Length).Insert(token.Span.Start, "x")

        for parent in nodes |> Array.groupBy (fun n -> n.Parent) |> Array.map snd do
            for count in [ parent.Length / 2; 1 ] |> List.distinct do
                if count > 0 then
                    for start in 0..count .. parent.Length - count do
                        let spans =
                            parent[start .. start + count - 1]
                            |> Array.map (fun n -> n.FullSpan)
                            |> Array.sortByDescending (fun s -> s.Start)

                        let mutable candidate = source

                        for span in spans do
                            candidate <- candidate.Remove(span.Start, span.Length)

                        yield candidate
    }
    |> Seq.filter (fun candidate ->
        candidate.Length < source.Length
        && not (
            (GeneratedOutput.parse candidate).GetDiagnostics()
            |> Seq.exists (fun d -> d.Severity = DiagnosticSeverity.Error)
        ))
    |> Seq.distinct

let private siblingHalf width =
    let source = "class C{\n" + String.replicate width "int x=0;\n" + "}\n"
    let root = GeneratedOutput.parse source
    let declaration = root.DescendantNodes() |> Seq.head :?> ClassDeclarationSyntax

    let spans =
        declaration.Members
        |> Seq.take (width / 2)
        |> Seq.map (fun node -> node.FullSpan)
        |> Seq.toArray

    source, spans

let private candidateAllocation source spans =
    for _ in 1..3 do
        GeneratedOutput.removeSiblingSpans source spans |> GC.KeepAlive

    Array.init 3 (fun _ ->
        let before = GC.GetAllocatedBytesForCurrentThread()
        GeneratedOutput.removeSiblingSpans source spans |> GC.KeepAlive
        GC.GetAllocatedBytesForCurrentThread() - before)
    |> Array.sort
    |> fun bytes -> bytes[1]

type PerturbedCase =
    {
        Path: string
        Source: string
        Edits: Perturbation list
        Options: PrinterOptions
    }

let private configurations =
    [|
        yield! OutputConfigurations.all |> List.map snd
        yield
            { PrinterOptions.Default with
                EndOfLine = EndOfLine.CrLf
            }
    |]

let private editGenerator =
    gen {
        let! kind = Gen.elements Perturbations.kinds
        let! position = Gen.choose (0, 100000)
        let! amount = Gen.choose (0, 5)

        return
            {
                Kind = kind
                Position = position
                Amount = amount
            }
    }

let private perturbGenerator seeds kind =
    gen {
        let! path, source = seeds
        let! length = Gen.choose (1, 12)
        let! generatedEdits = Gen.listOfLength length editGenerator

        let edits =
            generatedEdits
            |> List.map (fun edit ->
                match kind with
                | Some value -> { edit with Kind = value }
                | None -> edit)

        let! options = Gen.elements configurations

        return
            {
                Path = path
                Source = source
                Edits = edits
                Options = options
            }
    }

let private shrinkPerturbed (case: PerturbedCase) =
    seq {
        let editsArb = ArbMap.arbitrary<Perturbation list> ArbMap.defaults

        for edits in editsArb.Shrinker case.Edits do
            yield { case with Edits = edits }

        for source in GeneratedOutput.shrinkSource (Perturbations.apply case.Source case.Edits) do
            yield
                { case with
                    Source = source
                    Edits = []
                }

        if case.Options <> PrinterOptions.Default then
            yield
                { case with
                    Options = PrinterOptions.Default
                }
    }

type GrammarInput =
    {
        Grammar: GrammarCase
        Options: PrinterOptions
    }

let private rawGenerator =
    gen {
        let! quotes = Gen.choose (3, 6)
        let! multiline = Gen.elements [ false; true ]
        let! utf8 = Gen.elements [ false; true ]
        let! count = Gen.choose (1, 4)

        let! lines =
            Gen.listOfLength
                count
                (Gen.elements [ "a"; "hello world"; "日本語"; "a \" b"; "{ }"; "    indentation" ])

        return RawString(quotes, multiline, utf8, lines)
    }

let rec private interpolationGenerator depth =
    gen {
        let! raw = Gen.elements [ false; true ]
        let! dollars = if raw then Gen.choose (1, 3) else Gen.constant 1
        let! quotes = if raw then Gen.choose (3, 5) else Gen.constant 1

        let! multiline =
            if raw then
                Gen.elements [ false; true ]
            else
                Gen.constant false

        let! inner =
            if depth = 0 then
                Gen.choose (0, 1000) |> Gen.map Number
            else
                Gen.oneof
                    [
                        rawGenerator
                        interpolationGenerator (depth - 1)
                        Gen.choose (0, 1000) |> Gen.map Number
                    ]

        return Interpolated(dollars, quotes, multiline, inner)
    }

let rec private patternGenerator depth =
    let relational =
        gen {
            let! op = Gen.elements [ ">"; "<"; ">="; "<=" ]
            let! n = Gen.choose (0, 1000)
            return Relation(op, n)
        }

    let atom =
        Gen.oneof [ Gen.choose (0, 1000) |> Gen.map Constant; Gen.constant Null; relational ]

    if depth = 0 then
        atom
    else
        Gen.oneof
            [
                atom
                patternGenerator (depth - 1) |> Gen.map Negated
                patternGenerator (depth - 1) |> Gen.map GeneratedPattern.Property
                gen {
                    let! left = patternGenerator (depth - 1)
                    let! right = patternGenerator (depth - 1)
                    let! op = Gen.elements [ "and"; "or" ]
                    return Combined(op, left, right)
                }
                gen {
                    let! count = Gen.choose (0, 3)
                    let! patterns = Gen.listOfLength count (patternGenerator (depth - 1))
                    let! rest = Gen.elements [ false; true ]
                    return ListPattern(patterns, rest)
                }
            ]

let private grammarFamilies =
    [
        "raw strings"
        "nested interpolation"
        "patterns"
        "directives"
        "ignore"
        "trivia splits"
    ]

let private triviaSplitGenerator =
    gen {
        let! site = Gen.elements GrammarCases.triviaSites

        let! frame =
            GrammarCases.triviaFrames
            |> List.filter (GrammarCases.admitsTrivia site)
            |> Gen.elements

        let! payload = Gen.elements GrammarCases.triviaPayloads
        let! context = Gen.elements GrammarCases.triviaContexts
        return TriviaSplit(site, frame, payload, context)
    }

let private grammarCaseGenerator family =
    gen {
        return!
            match family with
            | "raw strings" ->
                gen {
                    let! count = Gen.choose (1, 4)
                    let! expressions = Gen.listOfLength count rawGenerator
                    return RawStrings expressions
                }
            | "nested interpolation" -> interpolationGenerator 3 |> Gen.map Interpolation
            | "patterns" ->
                gen {
                    let! count = Gen.choose (1, 4)
                    let! patterns = Gen.listOfLength count (patternGenerator 3)
                    return Patterns patterns
                }
            | "directives" ->
                gen {
                    let! count = Gen.choose (1, 4)

                    let! conditions =
                        Gen.listOfLength
                            count
                            (Gen.elements
                                [
                                    "true"
                                    "false"
                                    "TRUE"
                                    "True"
                                    "FALSE"
                                    "ACTIVE"
                                    "!ACTIVE"
                                    "ACTIVE && (OTHER || SECOND)"
                                    "ACTIVE == !OTHER"
                                    "OTHER != SECOND"
                                ])

                    let! nested = Gen.elements [ false; true ]
                    return Directives(conditions, nested)
                }
            | "ignore" ->
                gen {
                    let! range = Gen.elements [ false; true ]
                    let! statements = Gen.elements [ false; true ]
                    let! count = Gen.choose (1, 5)
                    return Ignore(range, statements, count)
                }
            | "trivia splits" -> triviaSplitGenerator
            | _ -> invalidArg (nameof family) family
    }

let private grammarGenerator family =
    gen {
        let! grammar = grammarCaseGenerator family
        let! options = Gen.elements configurations
        return { Grammar = grammar; Options = options }
    }

let private seedGenerator =
    gen {
        let! family = Gen.elements grammarFamilies
        let! grammar = grammarCaseGenerator family
        let rendered = GrammarCases.render grammar

        let seed =
            match grammar with
            | TriviaSplit _ -> rendered
            | _ -> GeneratedOutput.format PrinterOptions.Default rendered

        return $"generated/{family}.cs", seed
    }

let private shrinkGrammar case =
    seq {
        for grammar in GrammarCases.shrink case.Grammar do
            yield { case with Grammar = grammar }

        if case.Options <> PrinterOptions.Default then
            yield
                { case with
                    Options = PrinterOptions.Default
                }
    }

let private checkGrammar (checker: TokenPreservation.Checker) case =
    let source = GrammarCases.render case.Grammar

    match GeneratedOutput.checkSyntax source with
    | Ok() -> ()
    | Error error -> failtest $"{error}\nOptions: {case.Options}\nReproducer:\n{source}"

    let first = GeneratedOutput.format case.Options source

    match checker.Check(case.Options, "grammar.cs", source, first) with
    | Ok() -> ()
    | Error error -> failtest $"{error}\nOptions: {case.Options}\nReproducer:\n{source}"

    Expect.equal (GeneratedOutput.format case.Options first) first $"Grammar idempotency:\n{source}"

let private grammarProperty family =
    let checker = TokenPreservation.Checker()
    Prop.forAll (Arb.fromGenShrink (grammarGenerator family, shrinkGrammar)) (checkGrammar checker)

let private expectOk result =
    match result with
    | Ok() -> ()
    | Error error -> failtest error

let private checkPerturbed (checker: TokenPreservation.Checker) (case: PerturbedCase) =
    let source = Perturbations.apply case.Source case.Edits
    Perturbations.requireEquivalent case.Source source

    match GeneratedOutput.checkSyntax source with
    | Ok() -> ()
    | Error error ->
        failtest
            $"{error}\nSeed: {case.Path}\nOptions: {case.Options}\nEdits: {case.Edits}\nReproducer:\n{source}"

    let formatted = GeneratedOutput.format case.Options source

    match checker.Check(case.Options, case.Path, source, formatted) with
    | Ok() -> ()
    | Error error ->
        failtest
            $"{error}\nSeed: {case.Path}\nOptions: {case.Options}\nEdits: {case.Edits}\nReproducer:\n{source}"

let private checkIdempotent (checker: TokenPreservation.Checker) (case: PerturbedCase) =
    let source = Perturbations.apply case.Source case.Edits
    Perturbations.requireEquivalent case.Source source
    let first = GeneratedOutput.format case.Options source

    match checker.Check(case.Options, case.Path, source, first) with
    | Ok() -> ()
    | Error error -> failtest $"{error}\nOptions: {case.Options}\nReproducer:\n{source}"

    let second = GeneratedOutput.format case.Options first
    Expect.equal second first $"Options: {case.Options}\nReproducer:\n{source}"

let private perturbProperty seeds kind check =
    let checker = TokenPreservation.Checker()
    Prop.forAll (Arb.fromGenShrink (perturbGenerator seeds kind, shrinkPerturbed)) (check checker)

let private config cases seed =
    let elapsed = Stopwatch()

    { FsCheckConfig.defaultConfig with
        maxTest = cases
        replay = Some(seed, 11400714819323198485UL, None)
        receivedArgs =
            fun configuration name count arguments ->
                async {
                    if not elapsed.IsRunning then
                        elapsed.Start()

                    do! FsCheckConfig.defaultConfig.receivedArgs configuration name count arguments
                }
        finishedTest =
            fun configuration name data ->
                async {
                    elapsed.Stop()
                    do! FsCheckConfig.defaultConfig.finishedTest configuration name data

                    printfn
                        "%s: %d generated cases, %d shrinks, %.3fs"
                        name
                        data.NumberOfTests
                        data.NumberOfShrinks
                        elapsed.Elapsed.TotalSeconds
                }
    }

let private labelledConfigurations =
    OutputConfigurations.all
    @ [
        "width 100, CRLF",
        { PrinterOptions.Default with
            EndOfLine = EndOfLine.CrLf
        }
    ]

let private anyGrammarCase =
    Arb.fromGenShrink (
        gen {
            let! family = Gen.elements grammarFamilies
            return! grammarCaseGenerator family
        },
        GrammarCases.shrink
    )

let private reproducer (source: string) label error =
    failtest $"{error}\nConfiguration: {label}\nReproducer:\n{source}"

let private roundTripProperty =
    let buffer = TokenBuffer()

    Prop.forAll anyGrammarCase (fun case ->
        let source = GrammarCases.render case

        match RoundTrip.check "generated.cs" source buffer with
        | Ok() -> ()
        | Error error -> reproducer source "unformatted" error

        for label, options in labelledConfigurations do
            match
                RoundTrip.check "formatted.cs" (GeneratedOutput.format options source) buffer
            with
            | Ok() -> ()
            | Error error -> reproducer source label error)

let private tokenOracleProperty =
    let buffer = TokenBuffer()

    Prop.forAll anyGrammarCase (fun case ->
        let source = GrammarCases.render case

        match RoslynOracle.check "generated.cs" source buffer with
        | Ok() -> ()
        | Error error -> reproducer source "unformatted" error

        for label, options in labelledConfigurations do
            match
                RoslynOracle.check "formatted.cs" (GeneratedOutput.format options source) buffer
            with
            | Ok() -> ()
            | Error error -> reproducer source label error)

let private everyConfigurationProperty =
    let checker = TokenPreservation.Checker()

    Prop.forAll anyGrammarCase (fun case ->
        let source = GrammarCases.render case

        match GeneratedOutput.checkSyntax source with
        | Ok() -> ()
        | Error error -> reproducer source "unformatted" error

        for label, options in labelledConfigurations do
            let first = GeneratedOutput.format options source

            match GeneratedOutput.checkSyntax first with
            | Ok() -> ()
            | Error error -> reproducer source label error

            match checker.Check(options, "generated.cs", source, first) with
            | Ok() -> ()
            | Error error -> reproducer source label error

            Expect.equal
                (GeneratedOutput.format options first)
                first
                $"Idempotent at {label}:\n{source}")

let private lineEndingProperty =
    let buffer = TokenBuffer()

    Prop.forAll anyGrammarCase (fun case ->
        let source = GrammarCases.render case

        for label, options in labelledConfigurations do
            let formatted = GeneratedOutput.format options source
            Lexer.lex formatted buffer

            let expected = if options.EndOfLine = EndOfLine.CrLf then "\r\n" else "\n"

            for index in 0 .. buffer.TriviaCount - 1 do
                let trivia = buffer.Trivia index

                if trivia.Kind = TriviaKind.EndOfLineTrivia then
                    Expect.equal
                        (formatted.Substring(trivia.Start, trivia.Length))
                        expected
                        $"End-of-line trivia at offset {trivia.Start}, {label}:\n{source}")

let private triviaSplitVerdict (checker: TokenPreservation.Checker) options source =
    let checkSyntax candidate =
        try
            GeneratedOutput.checkSyntax candidate
        with error ->
            Error error.Message

    match checkSyntax source with
    | Error error -> Some("the generated case is not valid C#: " + error)
    | Ok() ->
        let formatted = GeneratedOutput.format options source

        match checkSyntax formatted with
        | Error error -> Some("the formatted output is not valid C#: " + error)
        | Ok() ->
            match checker.Check(options, "trivia-split.cs", source, formatted) with
            | Error error -> Some("formatting changed the token stream: " + error)
            | Ok() ->
                let second = GeneratedOutput.format options formatted

                if second <> formatted then
                    Some(
                        "formatting is not idempotent:\nfirst pass:\n"
                        + formatted
                        + "second pass:\n"
                        + second
                    )
                else
                    None

type TriviaSplitInput =
    {
        Case: GrammarCase
        Options: PrinterOptions
    }

let private triviaSplitWidthGenerator =
    gen {
        let! case = triviaSplitGenerator
        let! width = Gen.choose (16, 160)
        let! useTabs = Gen.elements [ false; true ]
        let! endOfLine = Gen.elements [ EndOfLine.Lf; EndOfLine.CrLf ]

        return
            {
                Case = case
                Options =
                    { PrinterOptions.Default with
                        Width = width
                        UseTabs = useTabs
                        EndOfLine = endOfLine
                    }
            }
    }

let private shrinkTriviaSplitWidth (input: TriviaSplitInput) =
    seq {
        for case in GrammarCases.shrink input.Case do
            yield { input with Case = case }

        if input.Options.UseTabs then
            yield
                { input with
                    Options = { input.Options with UseTabs = false }
                }

        if input.Options.EndOfLine <> EndOfLine.Lf then
            yield
                { input with
                    Options =
                        { input.Options with
                            EndOfLine = EndOfLine.Lf
                        }
                }

        let width = input.Options.Width

        if width <> PrinterOptions.Default.Width then
            let step = (PrinterOptions.Default.Width - width) / 2

            let candidates =
                if step = 0 then
                    [ PrinterOptions.Default.Width ]
                else
                    [ PrinterOptions.Default.Width; width + step ]

            for candidate in List.distinct candidates do
                if candidate <> width then
                    yield
                        { input with
                            Options = { input.Options with Width = candidate }
                        }
    }

let private triviaSplitWidthProperty =
    let checker = TokenPreservation.Checker()

    Prop.forAll
        (Arb.fromGenShrink (triviaSplitWidthGenerator, shrinkTriviaSplitWidth))
        (fun input ->
            let source = GrammarCases.render input.Case

            match triviaSplitVerdict checker input.Options source with
            | None -> ()
            | Some error ->
                failtest
                    $"{error}\nCase: {input.Case}\nOptions: {input.Options}\nReproducer:\n{source}")

let private triviaSplitCells () =
    seq {
        for site in GrammarCases.triviaSites do
            for frame in GrammarCases.triviaFrames do
                if GrammarCases.admitsTrivia site frame then
                    for payload in GrammarCases.triviaPayloads do
                        for context in GrammarCases.triviaContexts do
                            yield TriviaSplit(site, frame, payload, context)
    }

let private triviaSplitBand = [ 16..64 ]

let private nullableConfigurations =
    { PrinterOptions.Default with
        Width = 20
    }
    :: Array.toList configurations

let private checkNullable source =
    GeneratedOutput.checkSyntax source |> expectOk

    for options in nullableConfigurations do
        let formatted = GeneratedOutput.format options source
        GeneratedOutput.checkSyntax formatted |> expectOk

        TokenPreservation.Checker().Check(options, "nullable-context.cs", source, formatted)
        |> expectOk

        Expect.equal
            (GeneratedOutput.format options formatted)
            formatted
            $"Idempotent: {source} / {options}"

let private nullableCombinations () =
    seq {
        for name in [ "int"; "T"; "G<G<int>>" ] do
            for suffix in [ "?"; "?[]"; "?[,]" ] do
                let t = name + suffix
                let creation = "new " + t + (if suffix = "?" then "()" else "{}")

                let asHead = if suffix = "?" then "o as " + t else "(o as " + t + ")"
                let heads = [ "(o is " + t + ")"; "o is " + name; asHead; creation; "(" + t + ")o" ]

                let heads =
                    if suffix = "?" then
                        heads
                    else
                        ("(o is " + t + " value)") :: heads

                for head in heads do
                    for arm in
                        [
                            "[]"
                            "[1,2]"
                            "items?[0]"
                            "items?[0]?[1]"
                            "() => 1"
                            "static int? () => 1"
                            "static List<int>? () => flag ? [1,2] : []"
                            "o is string?[] value ? F<int,int>() : 0"
                        ] do
                        yield "x=" + head + " ? " + arm + " : [];"
                        yield "x=flag ? " + head + " ? " + arm + " : [] : null;"
                        yield "x=flag ? [] : " + head + " ? " + arm + " : [];"

                yield t + " value = flag ? items?[0] : null;"
                yield "class C { " + t + " M(" + t + " value) => flag ? (" + t + ")value : null; }"
                yield "var f = " + t + " () => flag ? [1,2] : [];"
                yield "x=o switch { (" + t + " value) => items?[0], _ => [] };"
    }

let private generated =
    testList
        "generated"
        [
            for index, family in List.indexed grammarFamilies do
                testPropertyWithConfig
                    (config 2000 (uint64 (834 + index)))
                    ($"grammar campaign / {family}")
                    (grammarProperty family)
            test "a comment run that already spans lines measures as it did on one line" {
                for source in
                    [
                        "x switch{_=>// p\n/*a*//*b*/0,};"
                        "x switch{_=>// p\n/*a*//*b*//*c*/0,};"
                        "x switch{{x:not// p\n/*a*//*b*/(not(<=x))}=>0,_=>0,};"
                        "x switch{{x:not// p\n/*p*//*a*//*b*/([>=x])}/*a*//*b*/=>0,_=>0,};"
                    ] do
                    GeneratedOutput.checkSyntax source |> expectOk

                    for label, options in labelledConfigurations do
                        let once = GeneratedOutput.format options source

                        TokenPreservation.Checker().Check(options, "regression.cs", source, once)
                        |> expectOk

                        Expect.equal
                            (GeneratedOutput.format options once)
                            once
                            $"Idempotent at {label}:\n{source}"
            }
            test "blank lines before a directive hold still across passes" {
                let build (comment: string) (blanks: int) =
                    "#if false\nclass A1{int a=1;}\n#else\nclass x{}"
                    + comment
                    + "\n"
                    + String.replicate blanks "\n"
                    + "#endif\n"

                for blanks in 0..3 do
                    let plain = build "" blanks
                    GeneratedOutput.checkSyntax plain |> expectOk

                    for comment in [ "/*p*/"; "// p"; "/*p*//*q*/" ] do
                        let source = build comment blanks
                        GeneratedOutput.checkSyntax source |> expectOk

                        for label, options in labelledConfigurations do
                            let once = GeneratedOutput.format options source

                            TokenPreservation
                                .Checker()
                                .Check(options, "regression.cs", source, once)
                            |> expectOk

                            Expect.equal
                                (GeneratedOutput.format options once)
                                once
                                $"Idempotent at {label}, {blanks} blank line(s), {comment}."

                        let blankLines (text: string) =
                            text.Split '\n'
                            |> Array.filter (fun line -> line.Length = 0)
                            |> Array.length

                        Expect.equal
                            (blankLines (GeneratedOutput.format PrinterOptions.Default source))
                            (blankLines (GeneratedOutput.format PrinterOptions.Default plain))
                            $"A trailing comment keeps the same blank lines as none, {blanks} given."
            }
            test "an ignore marker followed by whitespace is still a marker" {
                let template (trailing: string) =
                    "class C\n{\n    // csff-ignore-start"
                    + trailing
                    + "\n    int  x =  1;\n    // csff-ignore-end"
                    + trailing
                    + "\n    int y=2;\n}\n"

                let single (trailing: string) =
                    "class C\n{\n    // csff-ignore"
                    + trailing
                    + "\n    int  x =  1;\n    int y=2;\n}\n"

                for build in [ template; single ] do
                    let plain = build ""
                    GeneratedOutput.checkSyntax plain |> expectOk

                    for trailing in [ " "; "\t"; " \t"; "  " ] do
                        let source = build trailing
                        GeneratedOutput.checkSyntax source |> expectOk

                        for label, options in labelledConfigurations do
                            let once = GeneratedOutput.format options source

                            TokenPreservation
                                .Checker()
                                .Check(options, "regression.cs", source, once)
                            |> expectOk

                            Expect.equal
                                once
                                (GeneratedOutput.format options plain)
                                $"Trailing whitespace after the marker is not part of it, at {label}."

                            Expect.equal
                                (GeneratedOutput.format options once)
                                once
                                $"Idempotent at {label}:\n{source}"

                        Expect.stringContains
                            (GeneratedOutput.format PrinterOptions.Default source)
                            "int  x =  1;"
                            $"The ignored region is reproduced verbatim:\n{source}"
            }
            test "perturbations protect literal interiors and ignore spans" {
                let protectedPieces =
                    [
                        "@\"first\n    second\""
                        "\"\"\"\n    first\n      second\n    \"\"\""
                        "$$\"\"\"\n    value {{1 + 2}}\n    \"\"\""
                        "// csff-ignore\nint  ignored =  1;"
                        "// csff-ignore-start\nint  a =  1;\nint  b =  2;\n"
                    ]

                let source =
                    "class C{\nstring v="
                    + protectedPieces[0]
                    + ";\nstring r="
                    + protectedPieces[1]
                    + ";\nstring i="
                    + protectedPieces[2]
                    + ";\n"
                    + protectedPieces[3]
                    + "\n"
                    + protectedPieces[4]
                    + "// csff-ignore-end\nint last=0;\n}\n"

                GeneratedOutput.requireValid source

                for kind in Perturbations.kinds do
                    for position in 0..80 do
                        for amount in 0..5 do
                            let perturbed =
                                Perturbations.applyOne
                                    source
                                    {
                                        Kind = kind
                                        Position = position
                                        Amount = amount
                                    }

                            Perturbations.requireEquivalent source perturbed

                            for piece in protectedPieces do
                                Expect.stringContains
                                    perturbed
                                    piece
                                    "Protected text must survive byte for byte."
            }
            test "perturbation protection follows the trimmed ignore marker" {
                for trailing in [ ""; " "; "\t"; " \t" ] do
                    let ignored = "int  ignored =  1;"

                    let ranged =
                        "class C{\n// csff-ignore-start"
                        + trailing
                        + "\n"
                        + ignored
                        + "\n// csff-ignore-end"
                        + trailing
                        + "\nint after=0;\n}\n"

                    let single =
                        "class C{\n// csff-ignore"
                        + trailing
                        + "\n"
                        + ignored
                        + "\nint after=0;\n}\n"

                    for source in [ ranged; single ] do
                        GeneratedOutput.requireValid source

                        for kind in Perturbations.kinds do
                            for position in 0..40 do
                                for amount in 0..5 do
                                    let perturbed =
                                        Perturbations.applyOne
                                            source
                                            {
                                                Kind = kind
                                                Position = position
                                                Amount = amount
                                            }

                                    Perturbations.requireEquivalent source perturbed

                                    Expect.stringContains
                                        perturbed
                                        ignored
                                        $"The ignored field survives byte for byte after {kind} in:\n{source}"

                        Expect.stringContains
                            (GeneratedOutput.format PrinterOptions.Default source)
                            "int after = 0;"
                            $"Text after the marker is still formatted:\n{source}"
            }
            test "perturbation leaves csff-ignore line leading indentation untouched" {
                let ignoreIndents (source: string) =
                    source.Split([| "\r\n"; "\n"; "\r" |], StringSplitOptions.None)
                    |> Array.choose (fun line ->
                        let trimmed = line.TrimStart([| ' '; '\t' |])

                        if trimmed.StartsWith("// csff-ignore", StringComparison.Ordinal) then
                            Some(
                                line.Substring(0, line.Length - trimmed.Length),
                                trimmed.TrimEnd([| ' '; '\t' |])
                            )
                        else
                            None)

                for eol in [ "\n"; "\r\n"; "\r" ] do
                    let templates =
                        [
                            "class C{"
                            + eol
                            + "// csff-ignore"
                            + eol
                            + "int  ignored =  1;"
                            + eol
                            + "int after=0;"
                            + eol
                            + "}"
                            + eol
                            "class C{"
                            + eol
                            + "// csff-ignore - reason"
                            + eol
                            + "int  ignored =  1;"
                            + eol
                            + "}"
                            + eol
                            "class C{"
                            + eol
                            + "    // csff-ignore"
                            + eol
                            + "    int  ignored =  1;"
                            + eol
                            + "}"
                            + eol
                            "class C{"
                            + eol
                            + "// csff-ignore-start"
                            + eol
                            + "int  ignored =  1;"
                            + eol
                            + "// csff-ignore-end"
                            + eol
                            + "int after=0;"
                            + eol
                            + "}"
                            + eol
                            "class C{"
                            + eol
                            + "[A]"
                            + eol
                            + "// csff-ignore"
                            + eol
                            + "int  ignored =  1;"
                            + eol
                            + "}"
                            + eol
                        ]

                    for source in templates do
                        GeneratedOutput.requireValid source
                        let expectedMarkers = ignoreIndents source

                        for kind in Perturbations.kinds do
                            for position in 0..40 do
                                for amount in 0..5 do
                                    let perturbed =
                                        Perturbations.applyOne
                                            source
                                            {
                                                Kind = kind
                                                Position = position
                                                Amount = amount
                                            }

                                    Perturbations.requireEquivalent source perturbed

                                    Expect.equal
                                        (ignoreIndents perturbed)
                                        expectedMarkers
                                        $"Ignore marker line indent changed for {kind} pos={position} amt={amount}:\n{perturbed}"

                let unignored = "class C\n{\n  int x = 1;\n}\n"

                let reindented =
                    Perturbations.applyOne
                        unignored
                        {
                            Kind = Reindent
                            Position = 0
                            Amount = 1
                        }

                Expect.stringContains
                    reindented
                    "\n   {"
                    "Column-0 tokens outside csff-ignore ranges must remain reindentable."
            }
            test "blank-line deletion removes its indentation before a block comment" {
                for eol in [ "\n"; "\r\n"; "\r" ] do
                    for comment in [ "/* body"; "/** body" ] do
                        let source = eol + eol + "    " + comment + eol + "     */" + eol

                        let trailing =
                            Perturbations.applyOne
                                source
                                {
                                    Kind = TrailingWhitespace
                                    Position = 1
                                    Amount = 3
                                }

                        let edited =
                            Perturbations.applyOne
                                trailing
                                {
                                    Kind = BlankLines
                                    Position = 1
                                    Amount = 0
                                }

                        Expect.equal
                            edited
                            (source.Substring(eol.Length))
                            "Deleting a blank line must not prepend its spaces and tabs to the comment."

                        Perturbations.requireEquivalent source edited

                        Expect.equal
                            (GeneratedOutput.format PrinterOptions.Default edited)
                            (GeneratedOutput.format PrinterOptions.Default source)
                            "The comment's continuation lines keep their relative indentation."
            }
            test "blank-line deletion removes leading and final whitespace-only lines" {
                for eol in [ "\n"; "\r\n"; "\r" ] do
                    for source, expected, position in
                        [
                            " \t" + eol + "class C{}", "class C{}", 0
                            "class C{}" + eol + " \t" + eol, "class C{}" + eol, 1
                        ] do
                        let edited =
                            Perturbations.applyOne
                                source
                                {
                                    Kind = BlankLines
                                    Position = position
                                    Amount = 0
                                }

                        Expect.equal edited expected "The entire whitespace-only line is removed."
                        Perturbations.requireEquivalent source edited
            }
            test "perturbations change ordinary trivia for every family" {
                let source = "class C\n{\n  int x = 1;\n\n}\n"

                for kind in Perturbations.kinds do
                    let edited =
                        Perturbations.applyOne
                            source
                            {
                                Kind = kind
                                Position = 0
                                Amount = 1
                            }

                    Expect.notEqual edited source $"{kind} must exercise an actual edit."
                    Perturbations.requireEquivalent source edited
            }
            test "invalid generated syntax fails instead of being discarded" {
                Expect.throws
                    (fun () -> GeneratedOutput.requireValid "class {")
                    "A faulty generator must fail."
            }
            test "source shrinking preserves the complete ordered candidate sequence" {
                let sources =
                    [
                        ""
                        "class C{}"
                        "class C{int x;}"
                        "class C{int x;int x;int x;int x;int x;}"
                        "using A;using B;using C;class C{}struct S{}"
                        "namespace N{using A;using B;class A{}class B{}class C{}}"
                        "namespace N;using A;using B;class A{}class B{}"
                        "struct S{int a;int b;int c;int d;}"
                        "class C{void M(){int a=1;int b=2;int c=3;int d=4;return;}}"
                        "class C{[A]void M(int first,int second){if(true){Call();Other();}}}"
                        "// header\nclass C{\n// first\nint a; // trailing\n/* second */ int b;\nint c;\n}\n"
                        "#nullable enable\nusing A;\n#pragma warning disable\nusing B;\nclass C{}\n"
                        "class C{\n#if true\nint a;\nint b;\n#else\nint disabled;\n#endif\nint c;\nint d;\n}\n"
                        "class C{\n#region Fields\nint a;\nint b;\n#endregion\nint c;\n}\n"
                    ]

                for original in sources do
                    for source in [ original; original.Replace("\n", "\r\n") ] |> List.distinct do
                        GeneratedOutput.requireValid source
                        let expected = legacyShrinkSource source |> Seq.toArray
                        let actual = GeneratedOutput.shrinkSource source |> Seq.toArray

                        Expect.equal
                            actual
                            expected
                            $"Candidate order and exact trivia for {source}"

                        Expect.equal actual (Array.distinct actual) "Candidates remain distinct."

                        for candidate in actual do
                            Expect.isLessThan
                                candidate.Length
                                source.Length
                                "Every shrink is shorter."

                            GeneratedOutput.requireValid candidate
            }
            test "coarse sibling deletions preserve gaps and validate non-overlapping spans" {
                let source = "0123456789"

                for spans in
                    [
                        [||]
                        [| TextSpan(0, 10) |]
                        [| TextSpan(7, 3); TextSpan(0, 2); TextSpan(4, 1) |]
                        [| TextSpan(2, 2); TextSpan(4, 2) |]
                        [| TextSpan(0, 0); TextSpan(5, 0); TextSpan(10, 0) |]
                    ] do
                    let expected =
                        spans
                        |> Array.sortByDescending (fun span -> span.Start)
                        |> Array.fold
                            (fun (candidate: string) span ->
                                candidate.Remove(span.Start, span.Length))
                            source

                    Expect.equal
                        (GeneratedOutput.removeSiblingSpans source spans)
                        expected
                        "Batching retains exactly the same source gaps."

                for spans in [ [| TextSpan(2, 3); TextSpan(4, 2) |]; [| TextSpan(9, 2) |] ] do
                    Expect.throwsT<ArgumentException>
                        (fun () -> GeneratedOutput.removeSiblingSpans source spans |> ignore)
                        "Invalid sibling spans cannot reach the copy."
            }
            test "coarse half-removal candidate allocation scales with retained source" {
                let smallSource, smallSpans = siblingHalf 128
                let largeSource, largeSpans = siblingHalf 1024
                let smallBytes = candidateAllocation smallSource smallSpans
                let largeBytes = candidateAllocation largeSource largeSpans

                printfn
                    "coarse half-removal allocation: 128 siblings=%d bytes; 1024 siblings=%d bytes"
                    smallBytes
                    largeBytes

                Expect.isLessThan
                    largeBytes
                    (12L * smallBytes)
                    "Eight times the siblings stays near linear allocation, including range sorting."
            }
            test "source shrinking removes unrelated members" {
                let source = "class C{int keep=1;int remove=2;void M(){return;}}"
                let candidates = GeneratedOutput.shrinkSource source |> Seq.toList

                Expect.isTrue
                    (candidates
                     |> List.exists (fun candidate ->
                         candidate.Contains "keep" && not (candidate.Contains "remove")))
                    "Shrink real syntax, not only the seed."

                for candidate in candidates do
                    GeneratedOutput.requireValid candidate
            }
            test "collection lambdas and neighboring shapes preserve tokens" {
                let sources =
                    [
                        "x=new x{x,x(x,()=>// p\nx),};"
                        "x=new x{x,new x(x,()=>// p\nx),};"
                        "x=new[]{x,new x(x,()=>// p\nx),};"
                    ]

                let neighbors =
                    [
                        "x(x,()=>// p\nx);"
                        "x=new x{x,x(x,()=>/* p */x),};"
                        "x=new x{x,x(x,()=>\n// p\nx),};"
                        "x=new x{x,x(x,()=>// p\nx)};"
                        "x=new x{x(x,()=>// p\nx),};"
                        "x=new x{x,x(()=>// p\nx),};"
                        "x=new x{x,x(x,a=>// p\nx),};"
                        "x=new x{x,x(x,()=>// p\n{}),};"
                        "x=new x{x,x(x,()=>// p\nx),x,};"
                        "x=new x{x,x(()=>x,()=>// p\nx),};"
                    ]

                for source, options in
                    List.allPairs (sources @ neighbors) (Array.toList configurations) do
                    GeneratedOutput.checkSyntax source |> expectOk
                    let formatted = GeneratedOutput.format options source
                    let checker = TokenPreservation.Checker()
                    checker.Check(options, "lambda-divergence.cs", source, formatted) |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options formatted)
                        formatted
                        "The divergence remains idempotent."

                for source, options in List.allPairs sources (Array.toList configurations) do
                    let formatted = GeneratedOutput.format options source
                    let newline = if options.EndOfLine = EndOfLine.CrLf then "\r\n" else "\n"
                    let swallowed = formatted.Replace("// p" + newline, "// p")
                    let checker = TokenPreservation.Checker()

                    Expect.isError
                        (checker.Check(options, "swallowed.cs", source, swallowed))
                        "Swallowing code into the line comment must fail."

                    Expect.isError
                        (checker.Check(
                            options,
                            "lambda-mutation.cs",
                            source,
                            formatted.Replace("new x", "new y")
                        ))
                        "The divergence cannot hide another token change in the same shape."
            }
            test "allows ref struct keeps its token separators" {
                let sources =
                    [
                        "class C<T> where T:allows ref struct{}"
                        "class C{void M<T>()where T:allows ref struct{}}"
                        "class C<T> where T:struct,allows ref struct{}"
                        "class C<T> where T:I,allows ref struct{}"
                        "class C<T> where T:new(),allows ref struct{}"
                        "class C<T,U> where T:allows ref struct where U:allows ref struct{}"
                        "struct S<T> where T:allows ref struct{}"
                        "interface I<T> where T:allows ref struct{}"
                        "delegate void D<T>()where T:allows ref struct;"
                    ]

                let neighbors =
                    [
                        "class C<T> where T:new(){}"
                        "class C<T> where T:class?{}"
                        "class C<T> where T:class{}"
                        "class C<T> where T:struct{}"
                        "class C<T> where T:notnull{}"
                        "class C{void M<T>()where T:default{}}"
                        "class C<T> where T:I{}"
                        "class C:B,I{}"
                    ]

                for source, options in
                    List.allPairs (sources @ neighbors) (Array.toList configurations) do
                    GeneratedOutput.checkSyntax source |> expectOk
                    let formatted = GeneratedOutput.format options source

                    TokenPreservation.Checker().Check(options, "regression.cs", source, formatted)
                    |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options formatted)
                        formatted
                        "Constraint printing is idempotent."

                for source, options in List.allPairs sources (Array.toList configurations) do
                    Expect.stringContains
                        (GeneratedOutput.format options source)
                        "allows ref struct"
                        "The anti-constraint keeps single spaces between its keywords."

                for source, options in List.allPairs neighbors (Array.toList configurations) do
                    let formatted = GeneratedOutput.format options source

                    Expect.isFalse
                        (formatted.Contains "new ( )" || formatted.Contains "class ?")
                        "Neighbouring constraints gain no separator."
            }
            test "conditional arms and attributed lambdas keep every token" {
                let sources =
                    [
                        "x=b?()=>F():()=>G();"
                        "x=b?(y)=>F():(z)=>G();"
                        "x=b?()=>F():G();"
                        "x=b?()=>1:()=>2;"
                        "x=y is C?new object?[0]:y;"
                        "x=y is C?new object?[]{}:y;"
                        "x=[A]static()=>0;"
                        "x=[A]async()=>0;"
                        "x=[A]static async()=>0;"
                        "x=b?static int?()=>1:static int?()=>null;"
                        "x=b?int?()=>1:()=>null;"
                        "x=b?string?()=>null:null;"
                        "x=b?static T?()=>1:null;"
                        "x=b?T?[,]()=>null:()=>null;"
                        "x=b?T?[]()=>null:null;"
                        "x=b?ref readonly int?()=>ref y:null;"
                    ]

                let neighbors =
                    [
                        "x=b?y=>F():z=>G();"
                        "x=b?(()=>F()):(()=>G());"
                        "x=y is C?new object[0]:y;"
                        "x=y is null?null:z;"
                        "x=y is C?a:b;"
                        "x=y is C c?a:b;"
                        "x=c?a:b;"
                        "x=a?b?c:d:e;"
                        "x=a?b:c?d:e;"
                        "x=a?[1]:[2];"
                        "x=a?.B;"
                        "x=[A]()=>0;"
                        "x=static()=>0;"
                        "x=[A][B]static()=>0;"
                        "x=[A]static int()=>0;"
                        "x=T?()=>1;"
                        "x=b?T()=>1:null;"
                        "x=b?(T?()=>1):null;"
                    ]

                for source, options in
                    List.allPairs (sources @ neighbors) (Array.toList configurations) do
                    GeneratedOutput.checkSyntax source |> expectOk
                    let formatted = GeneratedOutput.format options source

                    TokenPreservation.Checker().Check(options, "regression.cs", source, formatted)
                    |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options formatted)
                        formatted
                        "The repaired shapes are idempotent."

                for options in configurations do
                    Expect.isError
                        (TokenPreservation
                            .Checker()
                            .Check(
                                options,
                                "-arm.cs",
                                "x=b?()=>F():()=>G();",
                                "x = b? () => F();\n"
                            ))
                        "Discarding the false arm must fail."
            }
            test "nullable function pointer lambda returns keep conditional arms" {
                for source in
                    [
                        "unsafe class C { object M(bool flag) => flag ? delegate*<int, void>[]? () => null : null; }"
                        "x=flag?delegate* unmanaged[Cdecl]<int,void>[]?()=>null:null;"
                        "x=flag?delegate*<int,void>[,]?()=>null:null;"
                        "x=flag?delegate*<int,void>[][]?()=>null:null;"
                        "x=a?b?[1]:delegate*<int,void>[]?()=>null:null;"
                        "x=flag?delegate*<int,void>[]?()=>F(other?[0]):null;"
                        "x=flag?null:delegate*<int,void>[]?()=>null;"
                        "x=flag?delegate*<int,void>[]()=>null:null;"
                    ] do
                    checkNullable source
            }
            test "nullable contexts differ like the pinned Roslyn oracle" {
                for source in nullableCombinations () do
                    checkNullable source
            }
            test "nullable qualifiers follow their type contexts" {
                for source in
                    [
                        "x=o is T ? async value => value : null;"
                        "x=o is T ? await F() : null;"
                        "x=o is T ? from value in values select value : null;"
                        "x=o is T ? value with { P = 1 } : null;"
                        "x=o as T ? items?[0] : null;"
                        "x=o as T ? () => 1 : null;"
                        "x=o is T? value;"
                        "x=F(o is T? value);"
                        "x=o is { P: T? value };"
                        "T? value; T?[] values; T?[,] matrix;"
                        "x=(T?)value; x=(T?[])value; x=(T?[,])value;"
                        "x=new T?(); x=new T?{}; x=new T?[0];"
                        "x=flag ? static T? () => (items?[0]) : null;"
                    ] do
                    checkNullable source
            }
            test "named conditional indexers keep argument colons" {
                for source in
                    [
                        "x = F(items?[index: 0]);"
                        "x=items?[index:0];"
                        "x=F(items?[row:flag?0:1,column:2]);"
                        "x=flag?items?[index:0]:other?[index:1];"
                        "x=F(items?[index:F(other?[index:1])]?.P);"
                        "x=items?[index:0]?[index:1];"
                        "x=items?[index:0]==true?[1]:[2];"
                        "x=flag?[1,2]:[3,4];"
                        "x=flag?[1].Length:[2].Length;"
                        "x=flag?[A(index:0)]()=>1:null;"
                    ] do
                    checkNullable source
            }
            test "interpolation holes suspend query keywords" {
                for source in
                    [
                        "var q = from o in values select $\"{(o is T ? select() : new T())}\";"
                        "var q=from o in values select $@\"{(o is T?select():new T())}\";"
                        "var q=from o in values select $\"\"\"{(o is T?select():new T())}\"\"\";"
                        "var q=from o in values select $\"{(o is T?select():new T())}{(o is T?group():new T())}\";"
                        "var q=from o in values select $\"{o,(o is T?select():0)}\";"
                        "var q=from o in values select $\"{(o is T?select():0):D}\";"
                        "var q=from o in values select $\"{F($\"{(o is T?select():new T())}\")}\";"
                        "var q=from o in values select $\"{(from p in values where p is T? select p)}{(o is T?select():new T())}\";"
                        "var q=from o in values let s=$\"{(o is T?select():new T())}\" where o is T? select s;"
                    ] do
                    checkNullable source
            }
            test "nullable query operands stop at clause keywords" {
                for source in
                    [
                        "var q = from o in values select o as int? into n select n;"
                        "var q = from o in values let n = o as int? select n;"
                        "var q = from o in values let n = o as int? where n != null select n;"
                        "var q = from o in values let n = o as int? join p in values on n equals p select n;"
                        "var q = from o in values join p in o as int[]? on p equals 1 select p;"
                        "var q = from o in values join p in values on o as int? equals p as int? into matches select matches;"
                        "var q = from o in values let n = o as int? orderby n select n;"
                        "var q = from o in values orderby o as int? ascending, o as int? descending select o;"
                        "var q = from o in values let n = o as int? group n by o as int? into ns select ns;"
                        "var q = from o in values group o as int? by o as int? into ns select ns;"
                        "var q = from o in values where o is T? select o;"
                        "x=o as T ? select() : n;"
                        "x=o is T ? into[0] : n;"
                        "var q = from o in values select o as T ? @into[0] : n;"
                        "var q = from o in values select o is T ? @select[0] : n;"
                        "var q = from o in values let n = o is T ? values?[0] : 1 select n;"
                        "var q = from o in values select o is T ? from p in values select p : null;"
                    ] do
                    checkNullable source
            }
            test "nullable query designations stop at clause keywords" {
                for source in
                    [
                        "var q = from o in values where o is T? n select n;"
                        "var q = from o in values where o is T? n from p in values select p;"
                        "var q = from o in values where o is T? n let p = n select p;"
                        "var q = from o in values where o is T? n where n != null select n;"
                        "var q = from o in values where o is T? n join p in values on n equals p select n;"
                        "var q = from o in values where o is T? n orderby n select n;"
                        "var q = from o in values where o is T? n group n by n;"
                        "var q = from o in values select o is T? n into b select b;"
                        "var q = from o in values orderby o is T? n ascending, o is T? m descending select o;"
                        "var q = from o in values group o is T? n by o is T? m into g select g;"
                        "var q = from o in values where o is not T? n select o;"
                        "var q = from o in values where o is T? with select with;"
                    ] do
                    checkNullable source
            }
            test "recovery keeps interpolation hole conditionals" {
                for source in
                    [
                        "x=a?b?[0]==true?F<int,int>():$\"{F(c?[1]:[2])}\":null;"
                        "class C { static string F<A,B>() => \"\"; static string F(int[] values) => \"\"; void M(bool a, bool c, bool?[] b) { string? x; x = a ? b?[0] == true ? F<int,int>() : $\"{F(c ? [1] : [2])}\" : null; } }"
                        "x=a?b?[0]==true?F<int,int>():$@\"{F(c?[1]:[2])}\":null;"
                        "x=a?b?[0]==true?F<int,int>():$\"\"\"{F(c?[1]:[2])}\"\"\":null;"
                        "x=a?b?[0]==true?F<int,int>():$\"{F(c?[1]:[2])}{F(d?[3]:[4])}\":null;"
                        "x=a?b?[0]==true?F<int,int>():$\"{value,F(c?[1]:[2])}\":null;"
                        "x=a?b?[0]==true?F<int,int>():$\"{F($\"{F(c?[1]:[2])}\")}\":null;"
                        "x=a?b?[0]==true?F<int,int>():$\"{F(c?[1]:[2])}\"+d?[0].F<int,int>():null;"
                    ] do
                    checkNullable source
            }
            test "nullable designations accept contextual pattern followers" {
                for source in
                    [
                        "x=o switch { T? v when flag => 1, _ => 0 };"
                        "x=o switch { T? v and {} when flag => 1, _ => 0 };"
                        "x=o switch { T? v or null when flag => 1, _ => 0 };"
                        "x=o is T? v and {};"
                        "x=o is T? v or null;"
                        "x=o is T? v and {} ? a : b;"
                        "x=o is T? v or null ? a : b;"
                        "x=o switch { G<G<int>>? v when flag => 1, _ => 0 };"
                        "x=o switch { T?[] v when flag => 1, _ => 0 };"
                        "x=o switch { T?[,] v when flag => 1, _ => 0 };"
                    ] do
                    checkNullable source
            }
            test "deep nesting conforms on a sufficient stack" {
                let mutable failure = None

                let worker =
                    System.Threading.Thread(
                        System.Threading.ThreadStart(fun () ->
                            try
                                for leaf, arm in [ "[0]", ":[]"; "b", ":c" ] do
                                    checkNullable (
                                        "x="
                                        + String.replicate 1024 "a?"
                                        + leaf
                                        + String.replicate 1024 arm
                                        + ";"
                                    )
                            with error ->
                                failure <-
                                    Some(
                                        System.Runtime.ExceptionServices
                                            .ExceptionDispatchInfo.Capture
                                            error
                                    )),
                        16 * 1024 * 1024
                    )

                worker.Start()
                worker.Join()

                match failure with
                | Some error -> error.Throw()
                | None -> ()
            }
            test "1024 chained accesses preserve tokens and are idempotent" {
                let source = "x=a" + String.replicate 1024 "?[0]" + ";"

                for options in nullableConfigurations do
                    let formatted = GeneratedOutput.format options source

                    TokenPreservation
                        .Checker()
                        .CheckWith(options, [], "access-stress.cs", source, formatted)
                    |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options formatted)
                        formatted
                        "The full stress chain is idempotent."
            }
            test "nested lambdas and collection conditionals" {
                for source in
                    [
                        "x=flag ? items?[0] == true ? () => 1 : Make<int,int>() : null;"
                        "x=flag ? o is int ? [] : items?[0].Make<int,int>() : [];"
                        "x=flag ? [F((item,index) => $\"{index}\")] : [];"
                        "x=o is T ? [$\"{a}\", $@\"{b}\", $\"\"\"{c}\"\"\"] : [];"
                        "x=flag ? [$\"{(o is T ? items?[0] : 1)}\"] : [];"
                        "x=flag == true ? () => o is string?[] t ? F<int,int>() : 0 : null;"
                        "x=" + String.replicate 16 "a?" + "[0]" + String.replicate 16 ":[]" + ";"
                        "x=a" + String.replicate 8 "?[0]" + ";"
                        String.replicate 2048 "x=$\"{a}\";"
                        "x=" + String.replicate 16 "a?" + "b" + String.replicate 16 ":c" + ";"
                    ] do
                    checkNullable source
            }
            test "null-conditional elements and collection arms keep every token" {
                let sources =
                    [
                        "class C { int? M(object x, int[] values) => x is int ? values?[0] : 1; }"
                        "x=x is int?a?[0]?[1]:1;"
                        "x=x is int?a?[F(b?0:1)]:1;"
                        "x=x is int?a?[0].M():1;"
                        "x=x is int?a?[0].M<G<G<int>>>()?[1]:1;"
                        "x=x is int?a?[0]+b?[1]:1;"
                        "x=a?b?[0]:c?[1];"
                        "x=a?b?[0]?[1]:c?[2]?[3];"
                        "x=a?b?c?[0]:d?[1]:e?[2];"
                        "x=a?b?[0]:c?d?[1]:e?[2];"
                        "x=x is int?[1]:[2];"
                        "x=x is int?a?[1]:[2]:[3];"
                        "x=a?[1]:[2];"
                        "x=a?[]:[1];"
                        "x=a?b?[]:[1]:[2];"
                        "x=a?b?[1]:[2]:[3];"
                        "x=a?b?[0]?[1]:[2];"
                        "x=a?b?[1]:c?[2]:[3];"
                        "x=x is int? ?a:b;"
                        "x=x is int?[]?a?[0]:b?[1];"
                        "x=x is int?[,]?a?[0]:b?[1];"
                        "x=y is C?new object?[0]:y;"
                        "x=b?()=>F(a?[0]):()=>G(c?[1]);"
                    ]

                for source, options in List.allPairs sources nullableConfigurations do
                    GeneratedOutput.checkSyntax source |> expectOk
                    let formatted = GeneratedOutput.format options source
                    GeneratedOutput.checkSyntax formatted |> expectOk

                    TokenPreservation.Checker().Check(options, "regression.cs", source, formatted)
                    |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options formatted)
                        formatted
                        "Element access and collection arms remain idempotent."
            }
            for name, sources in
                [
                    "nullable as types keep the outer false arm",
                    [
                        "class C { int[] M(bool a, bool b, object c) => a ? b ? [1,2] : c as int?[] : []; }"
                        "x=a?b?[1,2]:c as int?[,]:[];"
                        "x=a?b?[1,2]:c as G<G<int>>?[]:[];"
                        "x=a?b?[1,2]:c as int?[]?[]:[];"
                    ]
                    "nullable lambda returns keep collection conditionals",
                    [
                        "var f = List<int>? () => flag ? [1,2] : [];"
                        "var f = T? () => flag ? [1,2] : [];"
                        "var f = G<G<int>>? () => flag ? [1,2] : [];"
                        "x=a?static List<int>? () => flag ? [1,2] : []:null;"
                        "x=a?() => b?[0]:() => c?[1];"
                    ]
                    "generic arguments do not end conditional arms",
                    [
                        "x=a?b?[1]:F<int,int>():[2];"
                        "x=a?b?[1]:F<G<int,int>,G<G<int>>>():[2];"
                        "x=a?b?[1]:F<int?,int[]>():[2];"
                    ]
                    "nullable array ranks do not nest conditionals",
                    [
                        "x=a?b?[]:new int[0]?[]:[];"
                        "x=a?b?[]:new int[0]?[,]:[];"
                        "x=a?b?[]:new int[0]?[]?[]:[];"
                    ]
                    "stackalloc nullable types keep the outer false arm",
                    [
                        "using System; class C { void M(bool a, bool b) { Span<int?> values = a ? b ? [1, 2] : stackalloc int?[0] : []; } }"
                        "x=a?b?[]:stackalloc int?[0]:[];"
                        "x=a?b?[]:stackalloc int?[1]{0}:[];"
                        "x=a?b?[]:stackalloc int[0]:[];"
                    ]
                    "false arm lambdas allow element access recovery",
                    [
                        "Func<int>? f = flag ? items?[0].Make<int,int>() : () => 1;"
                        "x=flag?items?[0].Make<G<int,int>,G<G<int>>>():()=>1;"
                        "x=flag?items?[0].Make<int,int>():static()=>1;"
                        "x=flag?items?[0].Make<int,int>():int?()=>1;"
                        "x=flag?items?[0]?[1]:()=>1;"
                    ]
                    "terminal nullable array types keep the outer false arm",
                    [
                        "class C { object M(bool a, bool b, object c) => a ? b ? [] : new int[]?(c) : null; }"
                        "x=a?b?[]:new int[,]?(c):null;"
                        "x=a?b?[]:new int[]?[]?(c):null;"
                        "x=a?b?[]:new int[]?{}:null;"
                    ]
                    "later collection conditionals keep their own colons",
                    [
                        "class C { int[] M(int[,] a) => a?[111111,222222] == 1 ? [1] : [2]; }"
                        "x=a?[111111,222222]==1?[1]:[2];"
                        "x=a?[0]?[1]==1?[1]:[2];"
                        "x=a?b?[0]:c?[1]:[2];"
                        "x=a" + String.replicate 8 "?[0]" + "==1?[1]:[2];"
                    ]
                    "nullable patterns stay inside the current true arm",
                    [
                        "x=p?o is int?[,] a?F<int,int>():q:r;"
                        "x=p?o is int?[] a?F<int,int>():q:r;"
                        "x=p?o is int?[,] a?F<int,int>()+b?[0]:q:r;"
                    ]
                    "function pointer arrays keep collection false arms",
                    [
                        "class C { object M(bool a, bool b) => a ? b ? [null] : new delegate*<int,void>[0] : []; }"
                        "x=a?b?[null]:new delegate* unmanaged[Cdecl]<int,void>[0]:[];"
                    ]
                    "nullable lambda heads keep the outer false arm",
                    [
                        "var f = a ? b ? [1] : static int? () => 1 : null;"
                        "x=a?b?[1]:static T?()=>1:null;"
                        "x=a?b?[1]:static G<G<int>>?()=>1:null;"
                    ]
                ] do
                test $"syntax regression: {name}" {
                    let options =
                        { PrinterOptions.Default with
                            Width = 20
                        }
                        :: Array.toList configurations

                    for source, options in List.allPairs sources options do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let formatted = GeneratedOutput.format options source
                        GeneratedOutput.checkSyntax formatted |> expectOk

                        TokenPreservation
                            .Checker()
                            .Check(options, "regression.cs", source, formatted)
                        |> expectOk

                        Expect.equal
                            (GeneratedOutput.format options formatted)
                            formatted
                            "Conditional boundaries remain idempotent."
                }
            test "a directly following #endif survives code after it" {
                let directives (text: string) =
                    text.Split('\n')
                    |> Array.map (fun line -> line.Trim())
                    |> Array.filter (fun line -> line.StartsWith("#", StringComparison.Ordinal))

                for source in
                    [
                        "class C{\n#if X\nvoid A(){}\n#if Y\nvoid B(){}\n#endif\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\n#if Y\n#if Z\nvoid B(){}\n#endif\n#endif\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\nvoid A(){}\n#else\n#if Y\nvoid B(){}\n#endif\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\nvoid A(){}\n#if Y\nvoid B(){}\n#endif\nvoid E(){}\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\n#if Y\nvoid B(){}\n#endif\n#endif\n}"
                        "class C{\n#if X\n#region R\nvoid A(){}\n#endregion\n#endif\nvoid D(){}\n}"
                    ] do
                    for options in configurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let formatted = GeneratedOutput.format options source

                        Expect.equal
                            (directives formatted)
                            (directives source)
                            "Every directive survives, in its original order."

                        Expect.equal
                            (GeneratedOutput.format options formatted)
                            formatted
                            "Directive nesting is idempotent."
            }
            test "a raw interpolated string lays out the same however its holes arrive" {
                let wide =
                    "{{string.Format(FeaturesResources.Load_from_0, "
                    + "\"Microsoft.VisualBasic (net461)\")}}"

                for name, source in
                    [
                        "switch arm, hole too wide to fit",
                        "public class T{public class V{public void M(bool b){var e=b switch{"
                        + "true=>$\"\"\"\nEnd Module\n\"\"\","
                        + "false=>$$\"\"\"\n"
                        + wide
                        + "\n\"\"\",};}}}"
                        "switch arm, hole fits",
                        "public class T{public class V{public void M(bool b){var e=b switch{"
                        + "false=>$$\"\"\"\n{{x}}\n\"\"\",_=>null,};}}}"
                        "argument, hole too wide to fit",
                        "public class T{public void M(){Call($$\"\"\"\n" + wide + "\n\"\"\");}}"
                        "argument, hole already spanning lines",
                        "public class T{public void M(){Call($$\"\"\"\n{{string.Format(\n"
                        + "a,\nb)}}\n\"\"\");}}"
                        "trailing lambda returning a raw string",
                        "class C{void M(){Call(1,()=>$$\"\"\"\n    prefix "
                        + "{{new[]{1,2,3}}} suffix\n    \"\"\");}}"
                        "no interpolation",
                        "public class T{public class V{public void M(bool b){var e=b switch{"
                        + "false=>\"\"\"\nEnd Module\n\"\"\",_=>null,};}}}"
                        "verbatim string arm",
                        "public class T{public class V{public void M(bool b){var e=b switch{"
                        + "false=>@\"a\nb\",_=>null,};}}}"
                    ] do
                    for label, options in labelledConfigurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let once = GeneratedOutput.format options source

                        TokenPreservation.Checker().Check(options, $"{name}.cs", source, once)
                        |> expectOk

                        let twice = GeneratedOutput.format options once
                        Expect.equal twice once $"Idempotent at {label}, {name}:\n{source}"

                        Expect.equal
                            (GeneratedOutput.format options twice)
                            once
                            $"Still idempotent at the third pass, {label}, {name}"
            }
            test "a comment in a hole keeps its line ending, whichever one it is" {
                for name, terminator in
                    [
                        "carriage return", "\r"
                        "next line", "\u0085"
                        "line separator", "\u2028"
                        "paragraph separator", "\u2029"
                    ] do
                    let source =
                        "class C{void M(){var s=$$\"\"\"\n{{1 // c" + terminator + "+2}}\n\"\"\";}}"

                    for label, options in labelledConfigurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let once = GeneratedOutput.format options source

                        TokenPreservation.Checker().Check(options, $"{name}.cs", source, once)
                        |> expectOk

                        let afterComment = once.Substring(once.IndexOf "// c" + 4)

                        Expect.isTrue
                            (afterComment.Length > 0
                             && (afterComment.[0] = '\r'
                                 || afterComment.[0] = '\n'
                                 || afterComment.[0] = '\u0085'
                                 || afterComment.[0] = '\u2028'
                                 || afterComment.[0] = '\u2029'))
                            $"The comment keeps its line ending at {label}, {name}:\n{once}"

                        Expect.equal
                            (GeneratedOutput.format options once)
                            once
                            $"Idempotent at {label}, {name}"
            }
            test "a blank line between two documentation comments survives" {
                let blocks (text: string) =
                    let mutable count = 0
                    let mutable inside = false

                    for line in text.Split('\n') do
                        if line.Trim().StartsWith("///", StringComparison.Ordinal) then
                            if not inside then
                                count <- count + 1

                            inside <- true
                        else
                            inside <- false

                    count

                for name, source, expected in
                    [
                        "two blocks, one blank line",
                        "class C{/// <summary>A.</summary>\n\n/// <summary>B.</summary>\nint x;}",
                        2
                        "two blocks, two blank lines",
                        "class C{/// <summary>A.</summary>\n\n\n/// <summary>B.</summary>\nint x;}",
                        2
                        "two blocks, no blank line",
                        "class C{/// <summary>A.</summary>\n/// <summary>B.</summary>\nint x;}",
                        1
                        "one block", "class C{/// <summary>A.</summary>\nint x;}", 1
                        "two blocks at file scope",
                        "/// <summary>A.</summary>\n\n/// <summary>B.</summary>\nclass C{}",
                        2
                        "multiline blocks",
                        "class C{/// <summary>\n/// A.\n/// </summary>\n\n"
                        + "/// <summary>\n/// B.\n/// </summary>\nint x;}",
                        2
                    ] do
                    for label, options in labelledConfigurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let once = GeneratedOutput.format options source

                        TokenPreservation.Checker().Check(options, $"{name}.cs", source, once)
                        |> expectOk

                        Expect.equal
                            (GeneratedOutput.format options once)
                            once
                            $"Idempotent at {label}, {name}"

                        Expect.equal
                            (blocks once)
                            expected
                            $"Documentation blocks at {label}, {name}:\n{once}"
            }
            test "a blank line before a directive does not stack on the printer's own" {
                let blankLines (text: string) =
                    text.TrimEnd('\n', '\r').Split('\n')
                    |> Array.filter (fun line -> line.Trim() = "")
                    |> Array.length

                for source, expected in
                    [
                        "namespace N;\n#if false\n#endif\n", 1
                        "namespace N;\n#if false\nclass C{}\n#endif\n", 1
                        "namespace N;\n#region R\n#endregion\n", 1
                        "namespace N;\n#pragma warning disable 1\n", 1
                        "namespace N;\nclass C{}\n#if false\n#endif\n", 1
                        "namespace N;\n\nclass C{}\n", 1
                        "class A{}\n\nclass B{}\n", 1
                        "class A{}\n\n\nclass B{}\n", 1
                    ] do
                    for label, options in labelledConfigurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let once = GeneratedOutput.format options source

                        TokenPreservation.Checker().Check(options, "regression.cs", source, once)
                        |> expectOk

                        Expect.equal
                            (GeneratedOutput.format options once)
                            once
                            $"Idempotent at {label}:\n{source}"

                        Expect.equal
                            (blankLines once)
                            expected
                            $"Blank lines at {label}:\n{source}\n->\n{once}"
            }
            for name, source, options in
                [
                    "empty input", "", PrinterOptions.Default
                    "accessor blank line",
                    "class C{int P{get{\n\nreturn 1;}}}",
                    PrinterOptions.Default
                    "nested directive separator",
                    "#if true\nclass A{}\n#if X\nclass B{}\n#endif\n#endif\n",
                    PrinterOptions.Default
                    "disabled text preserves line endings",
                    "#if false\nclass C{}\n#endif\n",
                    { PrinterOptions.Default with
                        EndOfLine = EndOfLine.CrLf
                    }
                    "first switch label blank line",
                    "class C{void M(int x){switch(x){\n\ncase 0:return;}}}",
                    PrinterOptions.Default
                    "nested foreach blank line",
                    "foreach(x x in x)\n\nforeach(x x in x){}",
                    PrinterOptions.Default
                    "with initializer trailing comment",
                    "x=x with{x=x/*p*/};",
                    PrinterOptions.Default
                ] do
                test ($"finding / {name}") {
                    GeneratedOutput.checkSyntax source |> expectOk
                    let once = GeneratedOutput.format options source

                    TokenPreservation.Checker().Check(options, $"{name}.cs", source, once)
                    |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options once)
                        once
                        "Regression is idempotent."
                }
            test "nested loops preserve blank lines across configurations" {
                for source in
                    [
                        "foreach(x x in x)\n\nforeach(x x in x){}"
                        "foreach(var x in xs)\n\nforeach(var (a,b) in pairs){}"
                        "foreach(var (a,b) in pairs)\n\nforeach(var x in xs){}"
                        "foreach(var x in xs)\n\nforeach(var y in ys)\n\nforeach(var z in zs){}"
                        "for(;;)\n\nfor(;;){}"
                        "while(x)\n\nwhile(x){}"
                        "using(x)\n\nusing(x){}"
                        "unsafe{fixed(int* x=p)\n\nfixed(int* y=p){}}"
                    ] do
                    for options in configurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let once = GeneratedOutput.format options source

                        TokenPreservation.Checker().Check(options, "nested-loops.cs", source, once)
                        |> expectOk

                        Expect.equal (GeneratedOutput.format options once) once "Idempotent loops."
            }
            test "conditional indentation preserves trailing comments in both layouts" {
                for source in
                    [
                        "x=x with{x=x/*p*/};"
                        "x=x with{x=veryLongIdentifierThatBreaksAfterTheAssignmentOperator/*p*/};"
                        "x=x with{x=x/*p*//*q*/};"
                        "x=x with{x=x//p\n};"
                        "x=x with{x=x with{y=y}/*p*/};"
                        "x=x with{x=x with{y=y/*q*/}};"
                        "x=x with{x=F()/*p*/};"
                        "x=x with{x=obj.Member.F()/*p*/};"
                        "x=x with{x=()=>x/*p*/};"
                        "x=x with{x=a=>x/*p*/};"
                        "x=x with{x=F(()=>x)/*p*/};"
                        "x=x with{x=F(()=>x with{y=y/*q*/})};"
                        "x=x with{x=a switch{_=>x}/*p*/};"
                        "x=x with{x=a switch{_=>veryLongIdentifierThatBreaksAfterTheArrow}/*p*/};"
                        "x=x with{x=a switch{_=>x with{y=y/*q*/}}};"
                    ] do
                    for options in configurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let once = GeneratedOutput.format options source

                        TokenPreservation
                            .Checker()
                            .Check(options, "conditional-indent.cs", source, once)
                        |> expectOk

                        Expect.equal
                            (GeneratedOutput.format options once)
                            once
                            "Idempotent conditional indentation."
            }
            for index, kind in List.indexed Perturbations.kinds do
                testPropertyWithConfig
                    (config 1000 (uint64 (840 + index)))
                    ($"perturbation campaign / {kind}")
                    (perturbProperty seedGenerator (Some kind) (fun checker case ->
                        checkPerturbed checker case
                        checkIdempotent checker case))
            testPropertyWithConfig
                (config 2000 832UL)
                "perturbed generated source parses like Roslyn"
                (perturbProperty seedGenerator None checkPerturbed)
            testPropertyWithConfig
                (config 2000 833UL)
                "perturbed generated source is idempotent"
                (perturbProperty seedGenerator None checkIdempotent)
            testPropertyWithConfig
                (config 400 20261033UL)
                "generated source round-trips through the lexer before and after formatting"
                roundTripProperty
            testPropertyWithConfig
                (config 400 20261034UL)
                "generated source tokenizes the way the Roslyn oracle tokenizes it"
                tokenOracleProperty
            testPropertyWithConfig
                (config 400 20261035UL)
                "every configuration preserves tokens and reaches a fixed point"
                everyConfigurationProperty
            testPropertyWithConfig
                (config 400 20261036UL)
                "output carries the configured line ending and nothing else"
                lineEndingProperty
            testPropertyWithConfig
                (config 2000 20261037UL)
                "trivia inside a construct survives every width"
                triviaSplitWidthProperty
            test "every trivia-split cell formats, keeps its tokens and holds still" {
                let checker = TokenPreservation.Checker()

                let failures =
                    [
                        for case in triviaSplitCells () do
                            match
                                triviaSplitVerdict
                                    checker
                                    PrinterOptions.Default
                                    (GrammarCases.render case)
                            with
                            | Some error -> yield case, error
                            | None -> ()
                    ]

                if not failures.IsEmpty then
                    let census =
                        failures
                        |> List.countBy (fun (case, _) ->
                            match case with
                            | TriviaSplit(site, _, _, _) -> string site
                            | _ -> "other")
                        |> List.map (fun (site, count) -> site + " x" + string count)
                        |> String.concat ", "

                    let case, error = List.head failures

                    failtest
                        $"{failures.Length} of the trivia-split cells fail at the default configuration ({census}).\nFirst cell: {case}\n{error}\nReproducer:\n{GrammarCases.render case}"
            }
            test "trivia inside a construct survives the widths around its layout break" {
                let checker = TokenPreservation.Checker()

                let failures =
                    [
                        for site in GrammarCases.triviaSites do
                            for frame in GrammarCases.triviaFrames do
                                if GrammarCases.admitsTrivia site frame then
                                    for payload in [ LiteralValue; MemberPath ] do
                                        let case = TriviaSplit(site, frame, payload, FlushLeft)
                                        let source = GrammarCases.render case

                                        for width in triviaSplitBand do
                                            let options =
                                                { PrinterOptions.Default with
                                                    Width = width
                                                }

                                            match triviaSplitVerdict checker options source with
                                            | Some error -> yield case, width, error
                                            | None -> ()
                    ]

                if not failures.IsEmpty then
                    let widths = failures |> List.map (fun (_, width, _) -> width)
                    let narrowest = List.min widths
                    let widest = List.max widths
                    let case, width, error = List.head failures

                    failtest
                        $"{failures.Length} trivia-split cells fail inside the width band, from width {narrowest} to {widest}.\nFirst cell: {case} at width {width}\n{error}\nReproducer:\n{GrammarCases.render case}"
            }
            test "ported: conditional arms and attributed lambdas keep every token" {
                let sources =
                    [
                        "x=b?()=>F():()=>G();"
                        "x=b?(y)=>F():(z)=>G();"
                        "x=b?()=>F():G();"
                        "x=b?()=>1:()=>2;"
                        "x=y is C?new object?[0]:y;"
                        "x=y is C?new object?[]{}:y;"
                        "x=y is C?new Pair<int,int>[0]:y;"
                        "x=y is C?new Pair<int,int>?[0]:y;"
                        "x=b?()=>new Pair<int,int>():()=>G();"
                        "x=b?()=>F<int,int>():()=>G();"
                        "x=y is C?new Pair<int,Foo<int?>>?[0]:y;"
                        "x=[A]static()=>0;"
                        "x=[A]async()=>0;"
                        "x=[A]static async()=>0;"
                    ]

                let neighbors =
                    [
                        "x=b?y=>F():z=>G();"
                        "x=b?(()=>F()):(()=>G());"
                        "x=y is C?new object[0]:y;"
                        "x=y is null?null:z;"
                        "x=y is C?a:b;"
                        "x=y is C c?a:b;"
                        "x=c?a:b;"
                        "x=a?b?c:d:e;"
                        "x=a?b:c?d:e;"
                        "x=a?[1]:[2];"
                        "x=a?.B;"
                        "x=y is C?z<a:b;"
                        "x=b?()=>F<(int,int),int>():()=>G();"
                        "x=[A]()=>0;"
                        "x=static()=>0;"
                        "x=[A][B]static()=>0;"
                        "x=[A]static int()=>0;"
                    ]

                for source, options in
                    List.allPairs (sources @ neighbors) (Array.toList configurations) do
                    GeneratedOutput.checkSyntax source |> expectOk
                    let formatted = GeneratedOutput.format options source

                    TokenPreservation.Checker().Check(options, "lambdas.cs", source, formatted)
                    |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options formatted)
                        formatted
                        "The repaired shapes are idempotent."

                for options in configurations do
                    Expect.isError
                        (TokenPreservation
                            .Checker()
                            .Check(
                                options,
                                "lambda-arms.cs",
                                "x=b?()=>F():()=>G();",
                                "x = b? () => F();\n"
                            ))
                        "Discarding the false arm must fail."
            }
            test "ported: a directly following #endif survives code after it" {
                let directives (text: string) =
                    text.Split('\n')
                    |> Array.map (fun line -> line.Trim())
                    |> Array.filter (fun line -> line.StartsWith("#", StringComparison.Ordinal))

                for source in
                    [
                        "class C{\n#if X\nvoid A(){}\n#if Y\nvoid B(){}\n#endif\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\n#if Y\n#if Z\nvoid B(){}\n#endif\n#endif\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\nvoid A(){}\n#else\n#if Y\nvoid B(){}\n#endif\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\nvoid A(){}\n#if Y\nvoid B(){}\n#endif\nvoid E(){}\n#endif\nvoid D(){}\n}"
                        "class C{\n#if X\n#if Y\nvoid B(){}\n#endif\n#endif\n}"
                        "class C{\n#if X\n#region R\nvoid A(){}\n#endregion\n#endif\nvoid D(){}\n}"
                    ] do
                    for options in configurations do
                        GeneratedOutput.checkSyntax source |> expectOk
                        let formatted = GeneratedOutput.format options source

                        Expect.equal
                            (directives formatted)
                            (directives source)
                            "Every directive survives, in its original order."

                        Expect.equal
                            (GeneratedOutput.format options formatted)
                            formatted
                            "Directive nesting is idempotent."
            }
            test "ported: allows ref struct keeps its token separators" {
                let sources =
                    [
                        "class C<T> where T:allows ref struct{}"
                        "class C{void M<T>()where T:allows ref struct{}}"
                        "class C<T> where T:struct,allows ref struct{}"
                        "class C<T> where T:I,allows ref struct{}"
                        "class C<T> where T:new(),allows ref struct{}"
                        "class C<T,U> where T:allows ref struct where U:allows ref struct{}"
                        "struct S<T> where T:allows ref struct{}"
                        "interface I<T> where T:allows ref struct{}"
                        "delegate void D<T>()where T:allows ref struct;"
                    ]

                let neighbors =
                    [
                        "class C<T> where T:new(){}"
                        "class C<T> where T:class?{}"
                        "class C<T> where T:class{}"
                        "class C<T> where T:struct{}"
                        "class C<T> where T:notnull{}"
                        "class C{void M<T>()where T:default{}}"
                        "class C<T> where T:I{}"
                        "class C:B,I{}"
                    ]

                for source, options in
                    List.allPairs (sources @ neighbors) (Array.toList configurations) do
                    GeneratedOutput.checkSyntax source |> expectOk
                    let formatted = GeneratedOutput.format options source

                    TokenPreservation.Checker().Check(options, "allows-ref.cs", source, formatted)
                    |> expectOk

                    Expect.equal
                        (GeneratedOutput.format options formatted)
                        formatted
                        "Constraint printing is idempotent."

                for source, options in List.allPairs sources (Array.toList configurations) do
                    Expect.stringContains
                        (GeneratedOutput.format options source)
                        "allows ref struct"
                        "The anti-constraint keeps single spaces between its keywords."

                for source, options in List.allPairs neighbors (Array.toList configurations) do
                    let formatted = GeneratedOutput.format options source

                    Expect.isFalse
                        (formatted.Contains "new ( )" || formatted.Contains "class ?")
                        "Neighbouring constraints gain no separator."
            }
        ]

let tests = TestList([ generated ], Normal) |> testSequenced
