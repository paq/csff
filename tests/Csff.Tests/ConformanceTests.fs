module Csff.Tests.ConformanceTests

open System
open System.Collections.Generic
open System.IO
open Csff.Conformance
open Csff.Lexer
open Csff.Parser
open Csff.Printer
open Expecto
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

let private expectConforms result =
    match result with
    | Ok() -> ()
    | Error message -> failtest message

let private expectFailure fragments result =
    let message = Expect.wantError result "The corrupted buffer must fail."

    for fragment in fragments do
        Expect.stringContains message fragment "The report must locate and explain the failure."

let private verdict (verification: SyntaxPreservation.Verification) =
    match verification with
    | SyntaxPreservation.Verification.Proven -> "proven"
    | SyntaxPreservation.Verification.Violation _ -> "violation"
    | SyntaxPreservation.Verification.Unprovable _ -> "unprovable"

let private report (verification: SyntaxPreservation.Verification) =
    match verification with
    | SyntaxPreservation.Verification.Proven -> ""
    | SyntaxPreservation.Verification.Violation message -> message
    | SyntaxPreservation.Verification.Unprovable reason -> reason

let private unprovableSources = [ "AsmOffsets.cs", "# \nclass C { }\n" ]

let private withRepository action =
    let directory =
        Path.Combine(Path.GetTempPath(), "csff-checkout-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory directory |> ignore

    try
        action directory
    finally
        Directory.Delete(directory, true)

let private roundTripBuffer () =
    let buffer = TokenBuffer()
    buffer.AddTrivia(TriviaKind.WhitespaceTrivia, 0, 1)
    buffer.AddTrivia(TriviaKind.SingleLineCommentTrivia, 1, 5)
    buffer.AddTrivia(TriviaKind.EndOfLineTrivia, 6, 2)
    buffer.AddTrivia(TriviaKind.WhitespaceTrivia, 9, 1)
    buffer.AddTrivia(TriviaKind.EndOfLineTrivia, 10, 1)

    buffer.AddToken
        {
            Kind = TokenKind.IdentifierToken
            Start = 8
            Length = 1
            TriviaStart = 0
            LeadingCount = 3
            TrailingCount = 2
        }

    buffer.AddToken
        {
            Kind = TokenKind.EndOfFileToken
            Start = 11
            Length = 0
            TriviaStart = 5
            LeadingCount = 0
            TrailingCount = 0
        }

    buffer

let private copyBuffer changeToken changeTrivia (buffer: TokenBuffer) =
    let copy = TokenBuffer()

    for index in 0 .. buffer.TriviaCount - 1 do
        let trivia: Trivia = changeTrivia index (buffer.Trivia index)
        copy.AddTrivia(trivia.Kind, trivia.Start, trivia.Length)

    for index in 0 .. buffer.TokenCount - 1 do
        copy.AddToken(changeToken index (buffer.Token index))

    copy

let private unchanged _ value = value

let private oracleBuffer (source: string) =
    let options =
        let parseOptions =
            CSharpParseOptions(LanguageVersion.Preview, DocumentationMode.Diagnose)

        parseOptions.WithFeatures([ KeyValuePair("FileBasedProgram", "true") ])

    let root = CSharpSyntaxTree.ParseText(source, options).GetRoot()
    let buffer = TokenBuffer()

    for token in root.DescendantTokens() do
        let start = buffer.NextTriviaIndex

        for trivia in token.LeadingTrivia do
            buffer.AddTrivia(
                enum<TriviaKind> trivia.RawKind,
                trivia.FullSpan.Start,
                trivia.FullSpan.Length
            )

        for trivia in token.TrailingTrivia do
            buffer.AddTrivia(
                enum<TriviaKind> trivia.RawKind,
                trivia.FullSpan.Start,
                trivia.FullSpan.Length
            )

        buffer.AddToken
            {
                Kind = enum<TokenKind> token.RawKind
                Start = token.SpanStart
                Length = token.Span.Length
                TriviaStart = start
                LeadingCount = token.LeadingTrivia.Count
                TrailingCount = token.TrailingTrivia.Count
            }

    buffer

let private conformance =
    testList
        "conformance"
        [
            test "syntax preservation checks every conditional branch before writing" {
                let checker = SyntaxPreservation.Checker()
                let options = Csff.Printer.PrinterOptions.Default
                let source = "#if X\nclass B {}\n#else\nclass C {}\n#endif\n"
                let valid = "#if X\nclass B { }\n#else\nclass C { }\n#endif\n"

                checker.Check(options, "conditional.cs", source, valid) |> expectConforms

                let corrupted = "#if X\nclass C { }\n#else\nclass C { }\n#endif\n"

                checker.Check(options, "conditional.cs", source, corrupted)
                |> expectFailure [ "conditional.cs"; "could not be proven to preserve the C# syntax" ]

                Expect.equal
                    (verdict (checker.Decide(options, "conditional.cs", source, corrupted)))
                    "unprovable"
                    "A branch rewrite nothing names is refused as unproven, not written."
            }
            test "syntax preservation rejects a shebang moved off the first line" {
                let checker = SyntaxPreservation.Checker()
                let source = "#!/usr/bin/env dotnet\nclass C {}\n"
                let moved = "\n" + source

                checker.Check(Csff.Printer.PrinterOptions.Default, "script.cs", source, source)
                |> expectConforms

                checker.Check(Csff.Printer.PrinterOptions.Default, "script.cs", source, moved)
                |> expectFailure [ "script.cs"; "preprocessor directive line" ]
            }
            test "syntax preservation rejects syntax errors introduced in trivia" {
                let checker = SyntaxPreservation.Checker()
                let source = "class C {} /* comment */\n"

                let unclosed = "class C { } /* comment * /\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "comment.cs", source, unclosed)
                |> expectFailure [ "comment.cs"; "changed a comment" ]

                let directive = "class C { } #foo\n"

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "directive.cs",
                    "class C {}\n",
                    directive
                )
                |> expectFailure [ "directive.cs"; "preprocessor directive line" ]

                let existingError = "#error Fail\n" + source
                let additionalError = "#error Fail\n" + unclosed

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "existing-error.cs",
                    existingError,
                    additionalError
                )
                |> expectFailure [ "existing-error.cs"; "changed a comment" ]

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "short-comment.cs",
                    source,
                    "class C { } /*/\n"
                )
                |> expectFailure [ "short-comment.cs"; "changed a comment" ]

                let validDirective = "#pragma warning disable CS0168\nclass C {}\n"
                let malformedDirective = "#pragma warning invalid\nclass C { }\n"

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "pragma-directive.cs",
                    validDirective,
                    malformedDirective
                )
                |> expectFailure
                    [
                        "pragma-directive.cs"
                        "preprocessor directive line"
                        "\"#pragma warning disable CS0168\" became \"#pragma warning invalid\""
                    ]

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "line-directive.cs",
                    "#line 1 \"a \nclass C{}\n",
                    "#line 1 \"a\nclass C{ }\n"
                )
                |> expectFailure
                    [ "line-directive.cs"; "could not be proven to preserve the C# syntax" ]
            }
            test
                "syntax preservation proves #line spans, quoted #line and #pragma checksum" {
                let options = Csff.Printer.PrinterOptions.Default

                let source =
                    "#pragma checksum \"Views/a.cshtml\" \"{8829d00f-11b8-4213-878b-770e8597ac16}\" \"3b73\"\n"
                    + "namespace N\n{\n    using global::System.Threading.Tasks;\n"
                    + "    using global::Microsoft.AspNetCore.Components;\n"
                    + "    #line hidden\n    public class V\n    {\n"
                    + "#line (1,14)-(1,29) \"Views/a.cshtml\"\nobject   M() =>   new   object();\n\n"
                    + "#line default\n#line hidden\n#line 7 \"https://x/y.cshtml\" // a quoted // stays\n"
                    + "  void   F(){}\n#line default\n    }\n}\n"

                let tree = Csff.Parser.SyntaxTree()
                use builder = new SyntaxDocumentBuilder()
                use document = new DocumentBuffer()
                use printer = new Printer()
                Parser.parse source tree
                builder.Build(source, tree, document, options)
                printer.Print(source, document, options)
                let formatted = printer.OutputText

                Expect.isTrue
                    builder.Transformations.SortedUsings
                    "The fixture must sort its usings, or the comparison under test never runs."

                let checker = SyntaxPreservation.Checker()

                Expect.equal
                    (verdict (
                        checker.Decide(
                            options,
                            "razor.cs",
                            source,
                            formatted,
                            witness = builder.Transformations
                        )
                    ))
                    "proven"
                    $"Both forms are compared as text, so a reformatted file around them is proven: {formatted}"

                for before, after in
                    [
                        "#line (1,14)-(1,29) \"Views/a.cshtml\"",
                        "#line (1,14)-(1,29) \"Views/b.cshtml\""
                        "#line (1,14)-(1,29) \"Views/a.cshtml\"",
                        "#line (1,14)-(1,30) \"Views/a.cshtml\""
                        "\"3b73\"", "\"3b74\""
                    ] do
                    let changed = formatted.Replace(before, after)
                    Expect.notEqual changed formatted $"The fixture must hold {before}."

                    Expect.notEqual
                        (verdict (checker.Decide(options, "razor.cs", source, changed)))
                        "proven"
                        $"{before} became {after}, which nothing may prove."

                let unterminated = "#if false\n#line hidden\");   \n#endif\nclass C{}\n"
                let kept = "#if false\n#line hidden\");   \n#endif\nclass C { }\n"
                let trimmed = "#if false\n#line hidden\");\n#endif\nclass C { }\n"

                Expect.equal
                    (verdict (checker.Decide(options, "open.cs", unterminated, kept)))
                    "proven"
                    "An unterminated directive string kept exactly is the same directive."

                Expect.notEqual
                    (verdict (checker.Decide(options, "open.cs", unterminated, trimmed)))
                    "proven"
                    "Trimming an unterminated directive string changes the string."
            }
            test
                "syntax preservation proves using sorts whose alias names an array or predefined type" {
                let options = Csff.Printer.PrinterOptions.Default
                let checker = SyntaxPreservation.Checker()

                let print (source: string) =
                    let tree = Csff.Parser.SyntaxTree()
                    use builder = new SyntaxDocumentBuilder()
                    use document = new DocumentBuffer()
                    use printer = new Printer()
                    Parser.parse source tree
                    builder.Build(source, tree, document, options)
                    printer.Print(source, document, options)
                    struct (printer.OutputText, builder.Transformations)

                for source in
                    [
                        "using Z;\nusing B;\nusing R = int[]?;\nclass C{}\n"
                        "using A;\n#if P\nusing R;\n#endif\nusing B;\nusing M = X<int[]>;\nclass C {}\n"
                        "using A;\n#if P\nusing R;\n#else\nusing S;\n#endif\nusing B;\n#if Q\nusing M = X<string, string>;\n#else\nusing M = Y<string, string>;\n#endif\nclass C {}\n"
                    ] do
                    let struct (formatted, witness) = print source

                    Expect.isTrue
                        witness.SortedUsings
                        $"The fixture must sort its usings, or the rule under test never runs: {source}"

                    Expect.equal
                        (verdict (
                            checker.Decide(
                                options,
                                "alias.cs",
                                source,
                                formatted,
                                witness = witness
                            )
                        ))
                        "proven"
                        $"An alias to an array or predefined type moves like any other: {formatted}"

                    let changed =
                        formatted
                            .Replace("int[]", "int[,]")
                            .Replace("X<string, string>", "X<string, object>")

                    Expect.notEqual
                        changed
                        formatted
                        $"The fixture must hold an alias to change: {formatted}"

                    Expect.notEqual
                        (verdict (checker.Decide(options, "alias.cs", source, changed)))
                        "proven"
                        $"A changed alias target must not be proven: {changed}"
            }
            test "syntax preservation proves modifier sorts whose run holds a plain comment" {
                let options = Csff.Printer.PrinterOptions.Default
                let checker = SyntaxPreservation.Checker()

                let print (source: string) =
                    let tree = Csff.Parser.SyntaxTree()
                    use builder = new SyntaxDocumentBuilder()
                    use document = new DocumentBuffer()
                    use printer = new Printer()
                    Parser.parse source tree
                    builder.Build(source, tree, document, options)
                    printer.Print(source, document, options)
                    struct (printer.OutputText, builder.Transformations)

                for source in
                    [
                        "class C { extern static /* Boolean */ bool F(); }\n"
                        "class C { internal /*public*/ extern static int G(); }\n"
                        "unsafe // c\npublic class C {}\n"
                        "class C { static /* x */ public int H; }\n"
                    ] do
                    let struct (formatted, witness) = print source

                    Expect.isTrue
                        witness.SortedModifiers
                        $"The fixture must sort its modifiers, or the rule under test never runs: {source}"

                    Expect.equal
                        (verdict (
                            checker.Decide(
                                options,
                                "modifiers.cs",
                                source,
                                formatted,
                                witness = witness
                            )
                        ))
                        "proven"
                        $"A plain comment that stays with its word does not stop the sort: {formatted}"

                for source, moved in
                    [
                        "class C { extern static /* x */ bool M(); }\n",
                        "class C\n{\n    static extern /* x */\n    bool M();\n}\n"
                        "class C { static /* x */ public int M; }\n",
                        "class C\n{\n    public /* x */ static\n    int M;\n}\n"
                    ] do
                    Expect.equal
                        (verdict (checker.Decide(options, "moved.cs", source, moved)))
                        "violation"
                        $"A comment moved to another modifier is refused: {moved}"

                let documented = "class C\n{\n    static\n    /// d\n    public int F;\n}\n"
                let lifted = "class C\n{\n    /// d\n    public static int F;\n}\n"

                Expect.notEqual
                    (verdict (checker.Decide(options, "documented.cs", documented, lifted)))
                    "proven"
                    "An interior documentation comment brought to the front is not proven."
            }
            test "syntax preservation retains directive position within a using alias" {
                let checker = SyntaxPreservation.Checker()

                let source =
                    "using Alias =\n#pragma warning disable CS8632\nSystem.Collections.Generic.List<string?>;\nclass C {}\n"

                let moved =
                    "using Alias = System.Collections.Generic.List<string?>\n#pragma warning disable CS8632\n;\nclass C { }\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "alias.cs", source, moved)
                |> expectFailure [ "alias.cs"; "could not be proven to preserve the C# syntax" ]
            }
            test "syntax preservation accepts declared using permutations" {
                let checker = SyntaxPreservation.Checker()
                let source = "using Z;\nusing A;\nclass C {}\n"
                let formatted = "using A;\nusing Z;\nclass C { }\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "usings.cs", source, formatted)
                |> expectConforms
            }
            test "syntax preservation composes using sorting with a trailing comma" {
                let checker = SyntaxPreservation.Checker()
                let source = "using Z.Long;\nusing A;\nclass C { int[] M() => new[] { 1, 2 }; }\n"

                let formatted =
                    "using A;\nusing Z.Long;\nclass C { int[] M() => new[] {\n    1,\n    2,\n}; }\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "combined.cs", source, formatted)
                |> expectConforms
            }
            test "syntax preservation normalizes declared changes in inactive branches" {
                let checker = SyntaxPreservation.Checker()

                let source =
                    "#if X\nusing Z.Long;\nusing A;\nclass C { readonly static int[] Values = new[] { 1, 2 }; }\n#else\nclass C {}\n#endif\n"

                let formatted =
                    "#if X\nusing A;\nusing Z.Long;\nclass C { static readonly int[] Values = new[] {\n    1,\n    2,\n}; }\n#else\nclass C { }\n#endif\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "inactive.cs", source, formatted)
                |> expectConforms
            }
            test "syntax preservation accepts local-function and accessor modifier sorting" {
                let checker = SyntaxPreservation.Checker()

                let source =
                    "class C { async static System.Threading.Tasks.Task F() => null; public int P { get; internal protected set; } }"

                let formatted =
                    "class C { static async System.Threading.Tasks.Task F() => null; public int P { get; protected internal set; } }"

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "modifiers.cs",
                    source,
                    formatted
                )
                |> expectConforms
            }
            test "syntax preservation composes modifier sorting, trailing comma, and literal EOL" {
                let checker = SyntaxPreservation.Checker()

                let source =
                    "class C\n{\n    readonly static string[] Values = new[] { \"\"\"\r\n        one\r\n        two\r\n        \"\"\", \"three\" };\n}\n"

                let formatted =
                    "class C\n{\n    static readonly string[] Values = new[]\n    {\n        \"\"\"\n        one\n        two\n        \"\"\",\n        \"three\",\n    };\n}\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "combined.cs", source, formatted)
                |> expectConforms
            }
            test "syntax preservation rejects a moved definition directive" {
                let checker = SyntaxPreservation.Checker()
                let source = "#define X\nclass C {}\n"
                let formatted = "class C {}\n#define X\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "define.cs", source, formatted)
                |> expectFailure
                    [
                        "define.cs"
                        "preprocessor directive line"
                        "directive 0 (\"#define X\") followed 0 tokens and now follows 4"
                    ]
            }
            test "syntax preservation accepts using movement across a closed conditional" {
                let checker = SyntaxPreservation.Checker()

                let source =
                    "using System.IO;\n#if NET\nusing System.Text;\n#endif\nusing System.Linq;\nclass C {}\n"

                let formatted =
                    "using System.IO;\nusing System.Linq;\n#if NET\nusing System.Text;\n#endif\nclass C { }\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "usings.cs", source, formatted)
                |> expectConforms
            }
            test "syntax preservation rejects changed directive context for a using" {
                let checker = SyntaxPreservation.Checker()
                let source = "#nullable disable\nusing A = string?;\nclass C {}\n"
                let formatted = "using A = string?;\n#nullable disable\nclass C {}\n"

                checker.Check(Csff.Printer.PrinterOptions.Default, "nullable.cs", source, formatted)
                |> expectFailure
                    [ "nullable.cs"; "could not be proven to preserve the C# syntax" ]
            }
            test "syntax preservation checks every independent positive branch" {
                let checker = SyntaxPreservation.Checker()

                let source =
                    [| for index in 0..63 -> $"#if S{index}\nclass C{index}{{}}\n#endif\n" |]
                    |> String.concat ""

                let formatted = source.Replace("{}", "{ }")
                let corrupted = formatted.Replace("class C63", "class Other")

                checker.Check(Csff.Printer.PrinterOptions.Default, "branches.cs", source, formatted)
                |> expectConforms

                checker.Check(Csff.Printer.PrinterOptions.Default, "branches.cs", source, corrupted)
                |> expectFailure
                    [ "branches.cs"; "could not be proven to preserve the C# syntax" ]
            }
            test "syntax preservation combines independent closed-string branches" {
                let checker = SyntaxPreservation.Checker()
                let tokens = TokenPreservation.Checker()

                let source =
                    [|
                        for index in 0..63 ->
                            $"#if S{index}\nclass C{index} {{ string Value = \"hello\"; }}\n#endif\n"
                    |]
                    |> String.concat ""

                let normalized =
                    tokens.Normalize(Csff.Printer.PrinterOptions.Default, source, source)

                Expect.isSome
                    (tokens.CombinedIndependentSymbols(normalized, source))
                    "Closed string literals must permit a combined witness."

                let corrupted =
                    source.Replace(
                        "C63 { string Value = \"hello\"",
                        "C63 { string Value = \"changed\""
                    )

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "string-branches.cs",
                    source,
                    corrupted
                )
                |> expectFailure
                    [ "string-branches.cs"; "could not be proven to preserve the C# syntax" ]
            }
            test "syntax preservation keeps witnesses for a literal spanning branches" {
                let tokens = TokenPreservation.Checker()

                let source =
                    "#if A\nclass C { string Value = \"\"\"\n#endif\n#if B\nclass B {}\n#endif\n#if A\n\"\"\"; }\n#endif\n"

                let normalized =
                    tokens.Normalize(Csff.Printer.PrinterOptions.Default, source, source)

                Expect.isNone
                    (tokens.CombinedIndependentSymbols(normalized, source))
                    "A literal spanning conditional regions needs separate witnesses."
            }
            test "syntax preservation keeps witnesses for a verbatim literal spanning branches" {
                let tokens = TokenPreservation.Checker()

                let source =
                    "#if A\nclass C { string Value = @\"\n#endif\n#if B\nclass B {}\n#endif\n#if A\n\"; }\n#endif\n"

                let normalized =
                    tokens.Normalize(Csff.Printer.PrinterOptions.Default, source, source)

                Expect.isNone
                    (tokens.CombinedIndependentSymbols(normalized, source))
                    "A verbatim literal spanning conditional regions needs separate witnesses."

                let closed =
                    [|
                        for index in 0..32 ->
                            $"#if S{index}\nclass C{index} {{ string Value = @\"a\nb\"; }}\n#endif\n"
                    |]
                    |> String.concat ""

                let closedNormalized =
                    tokens.Normalize(Csff.Printer.PrinterOptions.Default, closed, closed)

                Expect.equal
                    (tokens.CombinedIndependentSymbols(closedNormalized, closed)
                     |> Option.map Array.length)
                    (Some 33)
                    "A closed verbatim literal must permit a combined witness."
            }
            test "syntax preservation retains separate witnesses when branches affect lexing" {
                let checker = SyntaxPreservation.Checker()

                let core =
                    "#if A\n/*\n#endif\n#if B\nclass B { int a, b; int M() => a + + + b; }\n#endif\n#if A\n*/\n#endif\n"

                let extra =
                    [| for index in 0..30 -> $"#if S{index}\nclass C{index} {{ }}\n#endif\n" |]
                    |> String.concat ""

                let source = core + extra
                let corrupted = source.Replace("a + + + b", "a++ + b")

                checker.Check(Csff.Printer.PrinterOptions.Default, "masked.cs", source, corrupted)
                |> expectFailure
                    [
                        "masked.cs"
                        "could not be proven to preserve the C# syntax"
                        "symbols: B"
                    ]
            }
            test "syntax preservation retries the configurations a combined witness cannot prove" {
                let checker = SyntaxPreservation.Checker()
                let tokens = TokenPreservation.Checker()

                let classes =
                    [| for index in 0..32 -> $"#if S{index}\nclass C{index} {{ }}\n#endif\n" |]
                    |> String.concat ""

                let source = classes + "#if U\nusing Z;\nusing A;\n#endif\n"
                let formatted = classes + "#if U\nusing A;\nusing Z;\n#endif\n"

                let normalized =
                    tokens.Normalize(Csff.Printer.PrinterOptions.Default, source, formatted)

                Expect.equal
                    (tokens.CombinedIndependentSymbols(normalized, formatted)
                     |> Option.map Array.length)
                    (Some 34)
                    "The shape must take a combined witness for the retry to be the thing tested."

                checker.Check(Csff.Printer.PrinterOptions.Default, "late-usings.cs", source, formatted)
                |> expectConforms
            }
            test "syntax preservation refuses a corruption inside the combined witness" {
                let checker = SyntaxPreservation.Checker()
                let tokens = TokenPreservation.Checker()

                let classes =
                    [| for index in 0..32 -> $"#if S{index}\nclass C{index} {{ }}\n#endif\n" |]
                    |> String.concat ""

                let source = classes + "#if U\nusing Original;\n#endif\n"
                let corrupted = source.Replace("using Original", "using Corrupted")

                let normalized =
                    tokens.Normalize(Csff.Printer.PrinterOptions.Default, source, source)

                Expect.equal
                    (tokens.CombinedIndependentSymbols(normalized, source)
                     |> Option.map Array.length)
                    (Some 34)
                    "Every region must be active in the combined witness."

                checker.Check(
                    Csff.Printer.PrinterOptions.Default,
                    "invalid-union.cs",
                    source,
                    corrupted
                )
                |> expectFailure
                    [ "invalid-union.cs"; "could not be proven to preserve the C# syntax" ]
            }
            test "checkout root accepts a worktree .git file" {
                withRepository (fun repository ->
                    File.WriteAllText(Path.Combine(repository, ".git"), "gitdir: /elsewhere")
                    let nested = Path.Combine(repository, "src", "nested")
                    Directory.CreateDirectory nested |> ignore

                    Expect.equal (Checkout.findRoot nested) repository "Use the nearest worktree.")
            }
            test "round-trip retains leading and trailing trivia, CRLF, and EOF" {
                RoundTrip.checkBuffer "fixture.cs" " // hi\r\nx \n" (roundTripBuffer ())
                |> expectConforms

                RoundTrip.check "empty.cs" "" (TokenBuffer()) |> expectConforms
            }
            test "round-trip reports the first differing offset and both contexts" {
                let corrupted =
                    roundTripBuffer ()
                    |> copyBuffer
                        (fun index token -> if index = 0 then { token with Start = 1 } else token)
                        unchanged

                RoundTrip.checkBuffer "fixture.cs" " // hi\r\nx \n" corrupted
                |> expectFailure [ "fixture.cs: offset 8"; "source:"; "reconstructed:"; "\\r\\n" ]
            }
            test "round-trip detects missing suffixes and duplicated text" {
                let source = " // hi\r\nx \n"
                let buffer = roundTripBuffer ()

                let missing =
                    copyBuffer
                        (fun index token ->
                            if index = 0 then
                                { token with TrailingCount = 0 }
                            else
                                token)
                        unchanged
                        buffer

                let duplicate =
                    copyBuffer
                        (fun index token ->
                            if index = 1 then
                                { token with Start = 8; Length = 1 }
                            else
                                token)
                        unchanged
                        buffer

                RoundTrip.checkBuffer "missing.cs" source missing
                |> expectFailure [ "missing.cs: offset 9" ]

                RoundTrip.checkBuffer "duplicate.cs" source duplicate
                |> expectFailure [ "duplicate.cs: offset 11" ]
            }
            test "round-trip reports invalid spans and trivia references" {
                let buffer = roundTripBuffer ()

                let span =
                    copyBuffer
                        (fun index token ->
                            if index = 0 then { token with Length = 100 } else token)
                        unchanged
                        buffer

                let trivia =
                    copyBuffer
                        (fun index token ->
                            if index = 0 then
                                { token with TriviaStart = 100 }
                            else
                                token)
                        unchanged
                        buffer

                RoundTrip.checkBuffer "span.cs" " // hi\r\nx \n" span
                |> expectFailure [ "span.cs: offset 8"; "invalid token span" ]

                RoundTrip.checkBuffer "trivia.cs" " // hi\r\nx \n" trivia
                |> expectFailure [ "trivia.cs: offset 0"; "invalid trivia range" ]
            }
            test
                "Roslyn oracle accepts directives, documentation, disabled text, and file-based programs" {
                let source =
                    "#!/usr/bin/env dotnet\n#if false\nunparsed text\n#else\n/// <summary>Doc</summary>\nclass C { string s = \"日本語😀\"; }\n#endif\n"

                let buffer = oracleBuffer source
                RoslynOracle.checkBuffer "fixture.cs" source buffer |> expectConforms
                RoundTrip.checkBuffer "fixture.cs" source buffer |> expectConforms
                RoslynOracle.check "empty.cs" "" (TokenBuffer()) |> expectConforms
            }
            test "Roslyn oracle detects token kind, start, and length changes" {
                let source = "class C {}"
                let buffer = oracleBuffer source

                let changes: (Token -> Token) list =
                    [
                        (fun token ->
                            { token with
                                Kind = TokenKind.IdentifierToken
                            })
                        (fun token -> { token with Start = 1 })
                        (fun token -> { token with Length = 4 })
                    ]

                for change in changes do
                    let corrupted =
                        copyBuffer
                            (fun index token -> if index = 0 then change token else token)
                            unchanged
                            buffer

                    RoslynOracle.checkBuffer "token.cs" source corrupted
                    |> expectFailure
                        [ "token.cs: offset 0"; "Roslyn: ClassKeyword"; "csff:"; "text=" ]
            }
            test "Roslyn oracle detects missing and extra tokens" {
                let source = "class C {}"
                let complete = oracleBuffer source
                let missing = TokenBuffer()

                for index in 0 .. complete.TriviaCount - 1 do
                    let trivia = complete.Trivia index
                    missing.AddTrivia(trivia.Kind, trivia.Start, trivia.Length)

                missing.AddToken(complete.Token 0)

                RoslynOracle.checkBuffer "missing.cs" source missing
                |> expectFailure
                    [
                        "missing.cs: offset 6"
                        "token count Roslyn=5, csff=1"
                        "csff: <missing token>"
                    ]

                complete.AddToken(complete.Token 4)

                RoslynOracle.checkBuffer "extra.cs" source complete
                |> expectFailure
                    [
                        "extra.cs: offset 10"
                        "token count Roslyn=5, csff=6"
                        "Roslyn: <missing token>"
                        "csff: EndOfFileToken"
                    ]
            }
            test
                "Roslyn oracle detects leading and trailing trivia kind, start, length, and count changes" {
                let source = " /* lead */ class C {} // tail\r\n"
                let buffer = oracleBuffer source
                let token = buffer.Token 0
                let triviaIndices = [ token.TriviaStart; token.TriviaStart + token.LeadingCount ]

                let changes: (Trivia -> Trivia) list =
                    [
                        (fun trivia ->
                            { trivia with
                                Kind = TriviaKind.EndOfLineTrivia
                            })
                        (fun trivia -> { trivia with Start = trivia.Start + 1 })
                        (fun trivia ->
                            { trivia with
                                Length = trivia.Length + 1
                            })
                    ]

                for triviaIndex in triviaIndices do
                    for change in changes do
                        let corrupted =
                            copyBuffer
                                unchanged
                                (fun index trivia ->
                                    if index = triviaIndex then change trivia else trivia)
                                buffer

                        RoslynOracle.checkBuffer "trivia.cs" source corrupted
                        |> expectFailure
                            [
                                "trivia.cs: offset"
                                "trivia 0 mismatch"
                                "Roslyn: WhitespaceTrivia"
                                "csff:"
                                "text="
                            ]

                let countChanges =
                    [
                        (fun token ->
                            { token with
                                LeadingCount = token.LeadingCount - 1
                            })
                        (fun token -> { token with TrailingCount = 0 })
                    ]

                for change in countChanges do
                    let corrupted =
                        copyBuffer
                            (fun index token -> if index = 0 then change token else token)
                            unchanged
                            buffer

                    RoslynOracle.checkBuffer "count.cs" source corrupted
                    |> expectFailure [ "count.cs: offset"; "trivia"; "<missing trivia>" ]
            }
            test "a formatting no layer can prove is unprovable, not a violation" {
                let checker = SyntaxPreservation.Checker()
                let options = Csff.Printer.PrinterOptions.Default

                for name, source in unprovableSources do
                    let formatted = GeneratedOutput.format options source

                    Expect.notEqual
                        formatted
                        source
                        (name + ": the fixture must be a file the formatter changes.")

                    Expect.equal
                        (verdict (checker.AdjudicateDecision(options, name, source, formatted)))
                        "proven"
                        (name + ": the independent comparison confirms the output.")

                    let decided = checker.Decide(options, name, source, formatted)

                    Expect.equal
                        (verdict decided)
                        "unprovable"
                        (name + ": what only the comparison confirms is unproven.")

                    Expect.stringContains
                        (report decided)
                        name
                        (name + ": the reason names the file.")

                    Expect.stringContains
                        (report decided)
                        "the file is unchanged"
                        (name + ": the reason says the file was left alone.")

                    Expect.stringStarts
                        (Expect.wantError
                            (checker.Check(options, name, source, formatted))
                            (name + ": an unproven output is refused."))
                        "unprovable:"
                        (name + ": the refusal says which of the two it is.")
            }
            test "a detected violation stays a violation" {
                let checker = SyntaxPreservation.Checker()
                let options = Csff.Printer.PrinterOptions.Default

                let source = "#pragma warning disable CS0168\nclass C {}\n"
                let corrupted = "#pragma warning invalid\nclass C { }\n"

                let decided = checker.Decide(options, "pragma.cs", source, corrupted)

                Expect.equal
                    (verdict decided)
                    "violation"
                    "An output a rule refuses is a violation, not an unproven file."

                Expect.stringContains
                    (report decided)
                    "formatting changed a preprocessor directive line"
                    "The violation names the rule that found it."

                let unnamed = "#if X\nclass B {}\n#else\nclass C {}\n#endif\n"
                let unnamedCorrupted = "#if X\nclass C { }\n#else\nclass C { }\n#endif\n"

                Expect.equal
                    (verdict (checker.Decide(options, "conditional.cs", unnamed, unnamedCorrupted)))
                    "unprovable"
                    "A pair no rule names stays the weaker of the two refusals."
            }
            test "a formatting the proofs settle is proven" {
                let checker = SyntaxPreservation.Checker()
                let options = Csff.Printer.PrinterOptions.Default

                for name, source in
                    [
                        "layout.cs", "class C{int x  =  1;}\n"
                        "declared.cs", "class C{static public int X=1;}\n"
                        "CircleInConvex.cs",
                        "class C\n{\n    void M() { }\n\n    // note \n    static public int P { get; }\n}\n"
                    ] do
                    let formatted = GeneratedOutput.format options source

                    Expect.notEqual
                        formatted
                        source
                        (name + ": the fixture must be a file the formatter changes.")

                    Expect.equal
                        (verdict (checker.Decide(options, name, source, formatted)))
                        "proven"
                        (name + ": a proven formatting is written.")
            }
        ]

let private separatorProofRefusals =
    [
        test "the separator proof refuses an added comma it cannot account for" {
            let refused source formatted =
                let verdict =
                    SyntaxPreservation.Checker().Check(PrinterOptions.Default, "sep.cs", source, formatted)

                Expect.notEqual verdict (Ok()) $"Must not be proven: {source} -> {formatted}"

            refused "class C{void M(){F(\n1\n);}}" "class C{void M(){F(\n1,\n);}}"
            refused "class C{void M(\nint a\n){}}" "class C{void M(\nint a,\n){}}"
            refused "class C{void M(){\nint a = 1;\n}}" "class C{void M(){\nint a = 1;\n,}}"
            refused "class C{void M(){A<\nint\n> x;}}" "class C{void M(){A<\nint\n,> x;}}"
            refused
                "class C{void M(){var v = new X{\nA = 1\n};}}"
                "class C{void M(){var v = new Y{\nA = 1,\n};}}"
            refused
                "class C{void M(){var v = new X{\n/*keep*/ A = 1\n};}}"
                "class C{void M(){var v = new X{\nA = 1,\n};}}"
            refused "class C{int[] a={\n1\n};}" "class C{int[] a={\n1\n#error injected\n,\n};}"
            refused "class C{int[] a={\n1\n};}" "class C{int[] a={\n1\n/*gained*/,\n};}"
            refused "class C{int[] a={\n1\n};}" "class C{int[] a={\n1\n,/*gained*/\n};}"
            refused
                "class C{void M(){var v = new X{\nA = 1\n};}}"
                "class C{void M(){var v = new X{\nA = 1,,\n};}}"
        }
        test "the separator proof accepts the printer's own trailing comma" {
            let print (source: string) =
                let tree = Csff.Parser.SyntaxTree()
                Parser.parse source tree
                use builder = new SyntaxDocumentBuilder()
                use d = new DocumentBuffer()
                use printer = new Printer()
                builder.Build(source, tree, d, PrinterOptions.Default)
                printer.Print(source, d, PrinterOptions.Default)
                printer.OutputText

            for source in
                [
                    "class C{void M(){var v = new X{Aaaaaaaaaaaaaaaaaaaaaaaaaaa=1,Bbbbbbbbbbbbbbbbbbbbbbbbbbbb=2,Ccccccccccccccccccccccccc=3};}}"
                    "class C{int[] M()=>new int[]{11111111,22222222,33333333,44444444,55555555,66666666,77777777,88888888};}"
                    "enum E{Aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,Bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,Cccccccccccccccccccccccccccccc}"
                ] do
                let formatted = print source

                Expect.equal
                    (SyntaxPreservation.Checker().Check(PrinterOptions.Default, "sep.cs", source, formatted))
                    (Ok())
                    source
        }
    ]

let private controlStackGrowth =
    [
        test "deeply nested documents format identically past the stacks' initial size" {
            let render (source: string) =
                let tree = Csff.Parser.SyntaxTree()
                Parser.parse source tree
                use builder = new SyntaxDocumentBuilder()
                use d = new DocumentBuffer()
                use printer = new Printer()
                builder.Build(source, tree, d, PrinterOptions.Default)
                printer.Print(source, d, PrinterOptions.Default)
                printer.OutputText

            let nested = String.replicate 400 "(" + "1" + String.replicate 400 ")"

            let regions =
                String.Join("", Seq.init 300 (fun i -> "#region R" + string i + "\n"))
                + "class C{}\n"
                + String.Join("", Seq.init 300 (fun _ -> "#endregion\n"))

            let onWorkerStack (work: unit -> unit) =
                let mutable error: exn = null

                let thread =
                    Threading.Thread(
                        Threading.ThreadStart(fun () ->
                            try
                                work ()
                            with e ->
                                error <- e),
                        Csff.Cli.Worker.StackSize
                    )

                thread.Start()
                thread.Join()

                if not (isNull error) then
                    raise error

            onWorkerStack (fun () ->
                for source in [ "class C{int M()=>" + nested + ";}"; regions ] do
                    let formatted = render source

                    Expect.equal
                        (SyntaxPreservation.Checker().Check(PrinterOptions.Default, "deep.cs", source, formatted))
                        (Ok())
                        "A deeply nested document must still be proven."

                    Expect.equal (render formatted) formatted "The second pass must change nothing.")
        }
    ]

let tests =
    TestList(
        [ conformance
          testList "conformance" separatorProofRefusals
          testList "conformance" controlStackGrowth ],
        Normal
    )
