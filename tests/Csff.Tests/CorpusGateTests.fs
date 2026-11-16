module Csff.Tests.CorpusGateTests

open System
open System.IO
open Expecto
open Csff.Gate

module private Fixtures =
    let accepted =
        [
            "using directives sorted",
            "using B;\nusing A;\nclass C { }\n",
            "using A;\nusing B;\nclass C { }\n"
            "declaration modifiers sorted",
            "class C { static public void M() { } }\n",
            "class C { public static void M() { } }\n"
            "accessor modifiers sorted",
            "class C { int P { private protected set { } } }\n",
            "class C { int P { protected private set { } } }\n"
            "trailing separator added to a list",
            "class C { int[] x = new[] { 1, 2 }; }\n",
            "class C { int[] x = new[] { 1, 2, }; }\n"
            "trailing separator added to an enum closed with a semicolon",
            "enum E { A, B };\n",
            "enum E { A, B, };\n"
            "trailing separator removed from a collection expression",
            "class C { int[] x = [1, 2,]; }\n",
            "class C { int[] x = [1, 2]; }\n"
            "trailing separator removed from an attribute list",
            "[A, B,]\nclass C { }\n",
            "[A, B]\nclass C { }\n"
            "trailing separator removed from an attribute list with a target",
            "[assembly: A,]\n",
            "[assembly: A]\n"
            "trailing separator removed from an attribute list on a parameter",
            "class C { void M([In, Out,] int x) { } }\n",
            "class C { void M([In, Out] int x) { } }\n"
            "trailing separator removed from a property pattern",
            "class C { bool M(object o) => o is { P: 1, }; }\n",
            "class C { bool M(object o) => o is { P: 1 }; }\n"
            "multiline raw string reindented",
            "class C { string s = \"\"\"\n        hi\n          deep\n        \"\"\"; }\n",
            "class C { string s = \"\"\"\n    hi\n      deep\n    \"\"\"; }\n"
            "interpolated multiline raw string reindented",
            "class C { string s = $\"\"\"\n        a{1}b\n          deep\n        \"\"\"; }\n",
            "class C { string s = $\"\"\"\n    a{1}b\n      deep\n    \"\"\"; }\n"
            "multiline literal newline bytes rewritten",
            "class C { string s = @\"a\nb\"; }\n",
            "class C { string s = @\"a\r\nb\"; }\n"
            "a whole conditional frame moved through the import list",
            "using A;\nusing D;\n#if X\nusing C;\n#endif\nusing B;\nclass C2 { }\n",
            "using A;\nusing B;\nusing D;\n#if X\nusing C;\n#endif\nclass C2 { }\n"
            "usings sorted inside a conditional frame",
            "#if DEBUG\nusing B;\nusing A;\n#endif\nclass C { }\n",
            "#if DEBUG\nusing A;\nusing B;\n#endif\nclass C { }\n"
            "trailing separator removed from a list pattern with a designation",
            "class C { bool M(int[] a) => a is [1, 2,] rest; }\n",
            "class C { bool M(int[] a) => a is [1, 2] rest; }\n"
            "trailing separator added to a list pattern with a discard designation",
            "class C { bool M(int[] a) => a is [1, 2] _; }\n",
            "class C { bool M(int[] a) => a is [1, 2,] _; }\n"
            "usings sorted together after a #nullable directive",
            "#nullable enable\nusing B;\nusing A;\nclass C { }\n",
            "#nullable enable\nusing A;\nusing B;\nclass C { }\n"
            "usings sorted inside a compound conditional branch",
            "#if A && B\nusing B;\nusing A;\n#endif\nclass C { }\n",
            "#if A && B\nusing A;\nusing B;\n#endif\nclass C { }\n"
        ]

    let refused =
        [
            "a using directive dropped",
            "using A;\nusing B;\nclass C { }\n",
            "using A;\nclass C { }\n"
            "a using directive duplicated",
            "using A;\nusing B;\nclass C { }\n",
            "using A;\nusing A;\nclass C { }\n"
            "a modifier dropped",
            "class C { public static void M() { } }\n",
            "class C { public void M() { } }\n"
            "a modifier replaced",
            "class C { public void M() { } }\n",
            "class C { private void M() { } }\n"
            "list elements reordered",
            "class C { int[] x = new[] { 1, 2 }; }\n",
            "class C { int[] x = new[] { 2, 1 }; }\n"
            "an attribute dropped with the separator before it",
            "[A, B,]\nclass C { }\n",
            "[A,]\nclass C { }\n"
            "an attribute list's interior separator dropped",
            "[A, B,]\nclass C { }\n",
            "[A B,]\nclass C { }\n"
            "an attribute moved out of its list with the separator",
            "[A, B,]\nclass C { }\n",
            "[A]\n[B]\nclass C { }\n"
            "a property subpattern dropped with the separator before it",
            "class C { bool M(object o) => o is { P: 1, Q: 2, }; }\n",
            "class C { bool M(object o) => o is { P: 1, }; }\n"
            "a separator added where the grammar forbids one",
            "using System.Collections.Generic;\nclass C { Dictionary<int, int> d = new() { { 1, 2 } }; }\n",
            "using System.Collections.Generic;\nclass C { Dictionary<int, int> d = new() { { 1, 2, } }; }\n"
            "raw string content changed",
            "class C { string s = \"\"\"\n    hi\n    \"\"\"; }\n",
            "class C { string s = \"\"\"\n    ho\n    \"\"\"; }\n"
            "verbatim string interior indentation changed",
            "class C { string s = @\"a\n   b\"; }\n",
            "class C { string s = @\"a\nb\"; }\n"
            "a semicolon dropped", "class C { int x = 1; }\n", "class C { int x = 1 }\n"
            "a statement moved into a conditional frame",
            "class C { void M() { int a = 1;\n#if X\n int b = 2;\n#endif\n } }\n",
            "class C { void M() {\n#if X\n int a = 1; int b = 2;\n#endif\n } }\n"
            "a directive condition changed",
            "class C { void M() {\n#if X\n int a = 1;\n#endif\n } }\n",
            "class C { void M() {\n#if Y\n int a = 1;\n#endif\n } }\n"
            "a pragma re-anchored across code",
            "class C { int a = 1;\n#pragma warning disable 1\n int b = 2; }\n",
            "class C { int a = 1; int b = 2;\n#pragma warning disable 1\n }\n"
            "a using directive left an active conditional frame",
            "#if !DEBUG\nusing U;\n#endif\nclass C { }\n",
            "using U;\n#if !DEBUG\n#endif\nclass C { }\n"
            "an unselected branch rewritten",
            "class C { void M() {\n#if X\n int a = 1;\n#else\n int a = 2;\n#endif\n } }\n",
            "class C { void M() {\n#if X\n int a = 9;\n#else\n int a = 2;\n#endif\n } }\n"
            "a using directive sorted across #nullable",
            "using B;\n#nullable disable\nusing A;\nclass C { }\n",
            "using A;\n#nullable disable\nusing B;\nclass C { }\n"
            "a using directive sorted across #pragma warning",
            "using B;\n#pragma warning disable CS0105\nusing A;\nclass C { }\n",
            "using A;\n#pragma warning disable CS0105\nusing B;\nclass C { }\n"
            "an identical using directive moved across #nullable",
            "using A;\n#nullable disable\nusing A;\nclass C { }\n",
            "using A;\nusing A;\n#nullable disable\nclass C { }\n"
            "a conjunctive #if branch rewritten",
            "class C { void M() {\n#if A && B\n int a = 1;\n#endif\n } }\n",
            "class C { void M() {\n#if A && B\n int a = 9;\n#endif\n } }\n"
            "a nested #if branch rewritten",
            "class C { void M() {\n#if A\n#if B\n int a = 1;\n#endif\n#endif\n } }\n",
            "class C { void M() {\n#if A\n#if B\n int a = 9;\n#endif\n#endif\n } }\n"
            "a conjunctive #elif branch rewritten",
            "class C { void M() {\n#if A\n int a = 1;\n#elif B && C\n int a = 2;\n#endif\n } }\n",
            "class C { void M() {\n#if A\n int a = 1;\n#elif B && C\n int a = 9;\n#endif\n } }\n"
            "a #warning message rewritten",
            "class C { void M() {\n#warning keep this\n } }\n",
            "class C { void M() {\n#warning changed\n } }\n"
            "a #region label rewritten",
            "class C {\n#region Original\n int x = 1;\n#endregion Original\n}\n",
            "class C {\n#region Renamed\n int x = 1;\n#endregion Original\n}\n"
            "an #endregion label rewritten",
            "class C {\n#region Section\n int x = 1;\n#endregion Original\n}\n",
            "class C {\n#region Section\n int x = 1;\n#endregion Renamed\n}\n"
            "an #error message rewritten",
            "class C {\n#error original reason\n}\n",
            "class C {\n#error different reason\n}\n"
        ]

let private budget = 8

let private refusedFiles () =
    let corpus = Environment.GetEnvironmentVariable "CSFF_GATE_CORPUS"
    let listed = Environment.GetEnvironmentVariable "CSFF_GATE_REFUSED"

    if
        String.IsNullOrEmpty corpus
        || String.IsNullOrEmpty listed
        || not (File.Exists listed)
    then
        None
    else
        let config =
            match Environment.GetEnvironmentVariable "CSFF_GATE_CONFIG" with
            | null -> None
            | "" -> None
            | path -> Some path

        Some(
            corpus,
            config,
            File.ReadAllLines listed
            |> Array.map (fun line ->
                let parts = line.Split ':'
                parts[0].Trim())
            |> Array.filter (fun line -> line <> "")
            |> Array.distinct
            |> Array.sort
        )

[<Tests>]
let tests =
    testList
        "corpus-gate"
        [
            testList
                "accepts"
                [
                    for name, before, after in Fixtures.accepted ->
                        testCase name
                        <| fun () ->
                            let outcome = Adjudicator.adjudicate before after budget

                            let detail =
                                outcome.Findings
                                |> List.map (fun finding ->
                                    finding.Category.Name + ": " + finding.Detail)
                                |> String.concat "; "

                            Expect.isEmpty outcome.Findings ("expected equivalent: " + detail)
                ]
            testList
                "refuses"
                [
                    for name, before, after in Fixtures.refused ->
                        testCase name
                        <| fun () ->
                            let outcome = Adjudicator.adjudicate before after budget

                            Expect.isNonEmpty
                                outcome.Findings
                                "expected a disagreement, which means a tolerance is too broad"
                ]
            testList
                "csff refuses them too"
                [
                    for name, before, after in Fixtures.refused ->
                        testCase name
                        <| fun () ->
                            let verdict =
                                Csff.Conformance.SyntaxPreservation
                                    .Checker()
                                    .Check(
                                        Csff.Printer.PrinterOptions.Default,
                                        "fixture.cs",
                                        before,
                                        after
                                    )

                            match verdict with
                            | Error _ -> ()
                            | Ok() ->
                                failtestf
                                    "csff's own verification accepts a pair the gate refuses: %s"
                                    name
                ]
            testCase "the refused corpus files are adjudicated"
            <| fun () ->
                match refusedFiles () with
                | None -> skiptest "CSFF_GATE_CORPUS and CSFF_GATE_REFUSED are unset"
                | Some(corpus, config, relatives) ->
                    let verdicts = ResizeArray<string>()

                    for relative in relatives do
                        let path = Path.Combine(corpus, relative)

                        let verdict =
                            if not (File.Exists path) then
                                "absent"
                            else
                                try
                                    let source = Csff.Cli.SourceEncoding.read path

                                    match Csff.Cli.Discovery.settingsForFile path config with
                                    | None -> "excluded by configuration"
                                    | Some settings ->
                                        use worker = new Csff.Cli.Worker()

                                        let printed =
                                            Csff.Cli.Worker.Run(fun () ->
                                                worker.Print(source, settings)
                                                worker.OutputText)

                                        let outcome = Adjudicator.adjudicate source printed budget

                                        let sizes =
                                            String.Format(
                                                " [source={0} printed={1}]",
                                                source.Length,
                                                printed.Length
                                            )

                                        match outcome.Findings with
                                        | [] ->
                                            "ROSLYN ACCEPTS the refused output (csff refused it)"
                                            + sizes
                                        | findings ->
                                            (findings
                                             |> List.map (fun finding ->
                                                 finding.Category.Name
                                                 + " ("
                                                 + finding.Configuration
                                                 + "): "
                                                 + finding.Detail)
                                             |> String.concat "; ")
                                            + sizes
                                with error ->
                                    let frame =
                                        match error.StackTrace with
                                        | null -> ""
                                        | trace ->
                                            let lines = trace.Split '\n'

                                            if lines.Length > 0 then
                                                " at" + lines[0].Trim().Substring(2)
                                            else
                                                ""

                                    "unprintable: "
                                    + error.GetType().Name
                                    + ": "
                                    + error.Message
                                    + frame

                        verdicts.Add(relative + "\n    " + verdict)

                    printfn "refused files adjudicated (%d):" verdicts.Count

                    for verdict in verdicts do
                        printfn "  %s" verdict
            testCase "decode distinguishes UTF-32 BOMs and uses Windows-1252 fallback"
            <| fun () ->
                let sample = "class C { }"
                let utf32Le = System.Text.UTF32Encoding(false, true, true)
                let utf32Be = System.Text.UTF32Encoding(true, true, true)
                let utf16Le = System.Text.UnicodeEncoding(false, true, true)
                let utf16Be = System.Text.UnicodeEncoding(true, true, true)

                let withPreamble (encoding: System.Text.Encoding) =
                    Array.append (encoding.GetPreamble()) (encoding.GetBytes sample)

                let struct (m32Le, t32Le) = Program.decode (withPreamble utf32Le)
                Expect.equal m32Le Decoding.Utf32Le "UTF-32LE BOM must not be misread as UTF-16LE."
                Expect.equal t32Le sample "UTF-32LE payload decodes cleanly."

                let struct (m32Be, t32Be) = Program.decode (withPreamble utf32Be)
                Expect.equal m32Be Decoding.Utf32Be "UTF-32BE BOM detected."
                Expect.equal t32Be sample "UTF-32BE payload decodes cleanly."

                let struct (m16Le, t16Le) = Program.decode (withPreamble utf16Le)
                Expect.equal m16Le Decoding.Utf16Le "UTF-16LE BOM detected."
                Expect.equal t16Le sample "UTF-16LE payload decodes cleanly."

                let struct (m16Be, t16Be) = Program.decode (withPreamble utf16Be)
                Expect.equal m16Be Decoding.Utf16Be "UTF-16BE BOM detected."
                Expect.equal t16Be sample "UTF-16BE payload decodes cleanly."

                let commentThenCode =
                    [|
                        byte '/'
                        byte '/'
                        byte ' '
                        0x85uy
                        byte ' '
                        byte 'c'
                        byte 'l'
                        byte 'a'
                        byte 's'
                        byte 's'
                        byte ' '
                        byte 'C'
                        byte ' '
                        byte '{'
                        byte '}'
                    |]

                let struct (mWin, tWin) = Program.decode commentThenCode
                Expect.equal mWin Decoding.Bytewise "Non-UTF-8 without BOM decodes bytewise."

                Expect.stringContains
                    tWin
                    "\u2026"
                    "Windows-1252 maps 0x85 to horizontal ellipsis, not NEL."

                Expect.isFalse (tWin.Contains('\u0085')) "0x85 must not decode to U+0085 NEL."
                let root = Adjudicator.parse tWin Adjudicator.parseOptions

                Expect.equal
                    (root.DescendantTokens()
                     |> Seq.filter (fun t ->
                         not (
                             t.RawKind =
                                 int Microsoft.CodeAnalysis.CSharp.SyntaxKind.EndOfFileToken
                         ))
                     |> Seq.length)
                    0
                    "0x85 keeps trailing code inside the // comment."
            testCase "pair mode rejects encoding changes and compares multi-symbol conditions"
            <| fun () ->
                let utf8Bytes = System.Text.Encoding.UTF8.GetBytes "class C { }\n"

                let utf8BomBytes =
                    Array.append (System.Text.UTF8Encoding(true).GetPreamble()) utf8Bytes

                let utf32Le = System.Text.UTF32Encoding(false, true, true)

                let utf32LeBytes =
                    Array.append (utf32Le.GetPreamble()) (utf32Le.GetBytes "class C { }\n")

                let exitBom, linesBom = Program.comparePair utf8BomBytes utf8Bytes 8
                Expect.equal exitBom 1 "--pair must fail when UTF-8 BOM is dropped."

                Expect.isFalse
                    (linesBom |> List.exists (fun line -> line = "equivalent"))
                    "--pair must not print equivalent when encoding changed."

                let exitUtf32, _ = Program.comparePair utf32LeBytes utf8Bytes 8
                Expect.equal exitUtf32 1 "--pair must fail when UTF-32LE changes to UTF-8."

                let tempDir =
                    Path.Combine(
                        Path.GetTempPath(),
                        "csff-gate-pair-" + Guid.NewGuid().ToString("N")
                    )

                Directory.CreateDirectory tempDir |> ignore

                try
                    let beforeFile = Path.Combine(tempDir, "before.cs")
                    let afterFile = Path.Combine(tempDir, "after.cs")
                    File.WriteAllBytes(beforeFile, utf8BomBytes)
                    File.WriteAllBytes(afterFile, utf8Bytes)

                    Expect.equal
                        (Program.main [| "--pair"; beforeFile; afterFile |])
                        1
                        "CLI --pair entry point exits 1 on encoding change."

                    File.WriteAllText(
                        beforeFile,
                        "class C { bool M(int[] a) => a is [1, 2,] rest; }\n"
                    )

                    File.WriteAllText(
                        afterFile,
                        "class C { bool M(int[] a) => a is [1, 2] rest; }\n"
                    )

                    Expect.equal
                        (Program.main [| "--pair"; beforeFile; afterFile |])
                        0
                        "CLI --pair exits 0 on valid list-pattern designation formatting."
                finally
                    if Directory.Exists tempDir then
                        Directory.Delete(tempDir, true)

                let conjOutcome =
                    Adjudicator.adjudicate
                        "class C { void M() {\n#if A && B\n int a = 1;\n#endif\n } }\n"
                        "class C { void M() {\n#if A && B\n int a = 9;\n#endif\n } }\n"
                        1

                Expect.isNonEmpty
                    conjOutcome.Findings
                    "budget=1 still detects corruption inside #if A && B via conjunctive config."

                Expect.isFalse
                    conjOutcome.SymbolsCapped
                    "finding a mismatch on budget=1 must not mark SymbolsCapped."

                let conjLargeBudget =
                    Adjudicator.adjudicate
                        "class C { void M() {\n#if A && B\n int a = 1;\n#endif\n } }\n"
                        "class C { void M() {\n#if A && B\n int a = 9;\n#endif\n } }\n"
                        64

                Expect.isNonEmpty
                    conjLargeBudget.Findings
                    "budget=64 detects corruption inside #if A && B."

                Expect.isFalse
                    conjLargeBudget.SymbolsCapped
                    "early mismatch on #if A && B before budget exhaustion must not set SymbolsCapped."

                let chainedEquality =
                    "#if " + String.Join(" == ", Array.create 40 "A") + "\nclass C { }\n#endif\n"

                let sw = System.Diagnostics.Stopwatch.StartNew()
                let chainedZero = Adjudicator.adjudicate chainedEquality (chainedEquality + "\n") 0

                let chainedBudget =
                    Adjudicator.adjudicate chainedEquality (chainedEquality + "\n") 8

                sw.Stop()

                Expect.isEmpty
                    chainedZero.Findings
                    "40-operand chained == agrees with whitespace change."

                Expect.isTrue
                    chainedZero.SymbolsCapped
                    "budget=0 marks 40-operand == condition as capped."

                Expect.isEmpty
                    chainedBudget.Findings
                    "40-operand chained == remains clean with budget=8."

                Expect.isLessThan
                    sw.Elapsed.TotalSeconds
                    2.0
                    "Memoized witness solver scales linearly on chained ==."

                let branchPriorityBefore =
                    String.concat
                        "\n"
                        [
                            "#if (A || B || C) && (D || E || F)"
                            "class Branch1 { int x = 1; }"
                            "#endif"
                            "#if G"
                            "class Branch2 { int y = 1; }"
                            "#endif"
                        ]

                let branchPriorityAfter = branchPriorityBefore.Replace("int y = 1;", "int y = 9;")

                let priorityOutcome =
                    Adjudicator.adjudicate branchPriorityBefore branchPriorityAfter 8

                Expect.isNonEmpty
                    priorityOutcome.Findings
                    "budget=8 covers one primary witness per branch before trying alternate combinations."

                let localDefineSource =
                    "#define Z\n"
                    + String.concat "" [ for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" ]
                    + "#if A\nclass C { int x = 1; }\n#endif\n"

                let localDefineOutcome =
                    Adjudicator.adjudicate
                        localDefineSource
                        (localDefineSource.Replace("int x = 1;", "int x = 9;"))
                        8

                Expect.isNonEmpty
                    localDefineOutcome.Findings
                    "Local #define Z rules out unreachable !Z && Bi combinations so #if A is tested at budget=8."

                let truncationSource =
                    "#if (B || C || D || E || F) && (B || C || D || E || F) || A\n#if !B && !C && !D && !E && !F\nclass C { int x = 1; }\n#endif\n#endif\n"

                let truncationOutcome =
                    Adjudicator.adjudicate
                        truncationSource
                        (truncationSource.Replace("int x = 1;", "int x = 9;"))
                        8

                Expect.isNonEmpty
                    truncationOutcome.Findings
                    "Constrained unit fallback recovers {A} across capped outer OR/AND combinations at budget=8."

                let alt16Source =
                    "#if ("
                    + String.Join(" || ", [| for i in 0..15 -> $"S{i}" |])
                    + ") && "
                    + String.Join(" && ", [| for i in 0..14 -> $"!S{i}" |])
                    + " && Z\nclass C { int x = 1; }\n#endif\n"

                let alt16Outcome =
                    Adjudicator.adjudicate
                        alt16Source
                        (alt16Source.Replace("int x = 1;", "int x = 9;"))
                        8

                Expect.isNonEmpty
                    alt16Outcome.Findings
                    "Constrained unit fallback satisfies 16-alternative disjunction under negated prefix literals."

                let headerGuardSource =
                    "#if !G\n#define G\n#if !G && B0\nclass Bad { }\n#endif\n#if X\nclass Good { int x = 1; }\n#endif\n#endif\n"

                let headerGuardOutcome =
                    Adjudicator.adjudicate
                        headerGuardSource
                        (headerGuardSource.Replace("int x = 1;", "int x = 9;"))
                        8

                Expect.isNonEmpty
                    headerGuardOutcome.Findings
                    "Conditional #define G inside #if !G respects entry vs body positions so #if X is tested."

                for header in
                    [
                        "#if true\n#define Z\n#endif\n"
                        "#if true\n#define Z\n#else\n#endif\n"
                        "#if false\n#else\n#define Z\n#endif\n"
                    ] do
                    let afterIfDefineSource =
                        header
                        + String.concat "" [ for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" ]
                        + "#if A\nclass C { int x = 1; }\n#endif\n"

                    let afterIfDefineOutcome =
                        Adjudicator.adjudicate
                            afterIfDefineSource
                            (afterIfDefineSource.Replace("int x = 1;", "int x = 9;"))
                            8

                    Expect.isNonEmpty
                        afterIfDefineOutcome.Findings
                        $"Unconditional {header.Trim()} persists past #endif so #if A is tested at budget=8."

                let gatedUndefSource =
                    "#if !B\n#define Z\n#endif\n#if B && !Z && C0\nclass Gated { int x = 1; }\n#endif\n"

                let gatedUndefOutcome =
                    Adjudicator.adjudicate
                        gatedUndefSource
                        (gatedUndefSource.Replace("int x = 1;", "int x = 9;"))
                        8

                Expect.isNonEmpty
                    gatedUndefOutcome.Findings
                    "Symbol-gated #define Z under #if !B is rolled back at #endif so #if B && !Z && C0 is discovered."

                let warningUsingBefore =
                    String.concat
                        "\n"
                        [
                            "#if X"
                            "#warning Hello"
                            "using C;"
                            "#endif"
                            "using B;"
                            "using A;"
                            "class C { }"
                            ""
                        ]

                let warningUsingAfter =
                    String.concat
                        "\n"
                        [
                            "using A;"
                            "using B;"
                            "#if X"
                            "#warning Hello"
                            "using C;"
                            "#endif"
                            "class C { }"
                            ""
                        ]

                let warningOutcome = Adjudicator.adjudicate warningUsingBefore warningUsingAfter 8

                Expect.isEmpty
                    warningOutcome.Findings
                    "Conditional block with #warning moved past sorted imports does not violate UsingScope."

                let inactiveNullableBefore =
                    String.concat
                        "\n"
                        [
                            "using B;"
                            "#if false"
                            "#nullable enable"
                            "#endif"
                            "using A;"
                            "class C { }"
                            ""
                        ]

                let inactiveNullableAfter =
                    String.concat
                        "\n"
                        [
                            "using A;"
                            "using B;"
                            "#if false"
                            "#nullable enable"
                            "#endif"
                            "class C { }"
                            ""
                        ]

                let inactiveNullableOutcome =
                    Adjudicator.adjudicate inactiveNullableBefore inactiveNullableAfter 8

                Expect.isEmpty
                    inactiveNullableOutcome.Findings
                    "Inactive #nullable directive under #if false does not split using context segments."
            testSequenced (
                testCase
                    "deep and combinator-rich witness discovery stays bounded on dedicated stack"
                <| fun () ->
                    let runMeasured (action: unit -> 'T) =
                        let mutable result = Unchecked.defaultof<'T>
                        let mutable allocated = 0L
                        let mutable failure: exn = null

                        let thread =
                            System.Threading.Thread(
                                System.Threading.ThreadStart(fun () ->
                                    try
                                        let before = GC.GetAllocatedBytesForCurrentThread()
                                        result <- action ()

                                        allocated <-
                                            GC.GetAllocatedBytesForCurrentThread() - before
                                    with ex ->
                                        failure <- ex),
                                16 * 1024 * 1024
                            )

                        thread.Start()
                        thread.Join()

                        if not (isNull failure) then
                            System.Runtime.ExceptionServices.ExceptionDispatchInfo
                                .Capture(failure)
                                .Throw()

                        struct (result, allocated)

                    ignore (
                        runMeasured (fun () ->
                            Adjudicator.adjudicate
                                "#if K0\nclass Warm { }\n#endif\n"
                                "#if K0\nclass Warm { }\n#endif\n\n"
                                8)
                    )

                    let deepAndCondition =
                        "#if "
                        + String.Join(" && ", [| for i in 0..3999 -> $"X{i}" |])
                        + "\nclass Deep { }\n#endif\n"

                    let struct ((deepZero, deepBudget), _) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate deepAndCondition (deepAndCondition + "\n") 0,
                            Adjudicator.adjudicate deepAndCondition (deepAndCondition + "\n") 8)

                    Expect.isEmpty
                        deepZero.Findings
                        "4000-operand && succeeds cleanly with budget=0."

                    Expect.isTrue deepZero.SymbolsCapped "budget=0 marks 4000-operand && as capped."

                    Expect.isEmpty
                        deepBudget.Findings
                        "4000-operand && succeeds cleanly with budget=8."

                    let hugeConj =
                        "#if "
                        + String.Join(" && ", [| for i in 0..7999 -> $"K{i}" |])
                        + "\nclass Huge { }\n#endif\n"

                    let struct (hugeZero, zeroAlloc) =
                        runMeasured (fun () -> Adjudicator.adjudicate hugeConj (hugeConj + "\n") 0)

                    Expect.isEmpty hugeZero.Findings "8000-operand && budget=0 stays clean."

                    Expect.isLessThan
                        zeroAlloc
                        120_000_000L
                        "8000-operand && discovery (budget=0) stays sublinearly bounded vs quadratic baseline."

                    let struct (hugeOutcome, allocDelta) =
                        runMeasured (fun () -> Adjudicator.adjudicate hugeConj (hugeConj + "\n") 8)

                    Expect.isEmpty
                        hugeOutcome.Findings
                        "8000-operand && whitespace change stays clean."

                    Expect.isLessThan
                        allocDelta
                        600_000_000L
                        "8000-operand && witness construction stays linear in allocation."

                    let orChain800 =
                        "#if "
                        + String.Join(" && ", [| for i in 0..799 -> $"(A{i} || B{i})" |])
                        + "\nclass OrChain { }\n#endif\n"

                    let struct (orChainZero, orChainZeroAlloc) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate orChain800 (orChain800 + "\n") 0)

                    Expect.isEmpty orChainZero.Findings "800-pair (A||B) && budget=0 stays clean."

                    Expect.isTrue
                        orChainZero.SymbolsCapped
                        "800-pair (A||B) && budget=0 marks capped."

                    Expect.isLessThan
                        orChainZeroAlloc
                        60_000_000L
                        "800-pair (A||B) && discovery (budget=0) avoids quadratic Set.GetHashCode allocation."

                    let struct (orChainBudget, orChainBudgetAlloc) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate orChain800 (orChain800 + "\n") 8)

                    Expect.isEmpty orChainBudget.Findings "800-pair (A||B) && budget=8 stays clean."

                    Expect.isLessThan
                        orChainBudgetAlloc
                        150_000_000L
                        "800-pair (A||B) && witness evaluation (budget=8) stays bounded in allocation."

                    let promotedAltSource =
                        "#if A || B\n#if B\n#if A\nclass Nested { }\n#endif\n#endif\n#endif\n"

                    let promotedAltOutcome =
                        Adjudicator.adjudicate promotedAltSource (promotedAltSource + "\n") 2

                    Expect.isEmpty
                        promotedAltOutcome.Findings
                        "Promoted alternate symbol source stays clean at budget=2."

                    Expect.isTrue
                        promotedAltOutcome.SymbolsCapped
                        "Stale promoted alternate queue entry does not stop discovery before nested #if A is seen."

                    let nested2000Builder = System.Text.StringBuilder()

                    for _ = 1 to 2000 do
                        nested2000Builder.Append("#if A\n") |> ignore

                    nested2000Builder.Append("class DeepIf { }\n") |> ignore

                    for _ = 1 to 2000 do
                        nested2000Builder.Append("#endif\n") |> ignore

                    let nested2000 = nested2000Builder.ToString()

                    let struct (nested2000Outcome, nested2000Alloc) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate nested2000 (nested2000 + "\n") 8)

                    Expect.isEmpty
                        nested2000Outcome.Findings
                        "2000 nested #if A blocks stay clean at budget=8."

                    Expect.isLessThan
                        nested2000Alloc
                        150_000_000L
                        "2000 nested #if A blocks keep discovery allocation linear."

                    let nestedElse8000Builder = System.Text.StringBuilder()

                    for _ = 1 to 8000 do
                        nestedElse8000Builder.Append("#if A\n") |> ignore

                    nestedElse8000Builder.Append("class DeepElse { }\n") |> ignore

                    for _ = 1 to 8000 do
                        nestedElse8000Builder.Append("#else\n#endif\n") |> ignore

                    let nestedElse8000 = nestedElse8000Builder.ToString()

                    let struct ((nestedElse8000Outcome, nestedElseElapsed), _) =
                        runMeasured (fun () ->
                            let timer = System.Diagnostics.Stopwatch.StartNew()

                            let outcome =
                                Adjudicator.adjudicate nestedElse8000 (nestedElse8000 + "\n") 1

                            timer.Stop()
                            outcome, timer.Elapsed.TotalSeconds)

                    Expect.isEmpty
                        nestedElse8000Outcome.Findings
                        "8000 nested #if A / #else blocks stay clean at budget=1."

                    Expect.isFalse
                        nestedElse8000Outcome.SymbolsCapped
                        "8000 nested #if A / #else blocks exhaust budget=1 without false cap."

                    Expect.isLessThan
                        nestedElseElapsed
                        5.0
                        "8000 nested #if A / #else discovery completes linearly when outer candidates are reused."

                    let elifSame2000 =
                        "#if A\n" + String.replicate 2000 "#elif A\n" + "#endif\nclass C { }\n"

                    let struct (elifSameOutcome, elifSameAlloc) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate elifSame2000 (elifSame2000 + "\n") 8)

                    Expect.isEmpty
                        elifSameOutcome.Findings
                        "2000 repeated #elif A arms stay clean at budget=8."

                    Expect.equal
                        elifSameOutcome.Configurations
                        2
                        "2000 repeated #elif A arms only test base and A configurations."

                    Expect.isLessThan
                        elifSameAlloc
                        80_000_000L
                        "2000 repeated #elif A arms short-circuit contradictory priors linearly in allocation."

                    let elifDiff2000 =
                        "#if B0\n"
                        + String.Join("", [| for i in 1..2000 -> $"#elif B{i}\n" |])
                        + "#else\n#endif\nclass D { }\n"

                    let struct (elifDiffOutcome, elifDiffAlloc) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate elifDiff2000 (elifDiff2000 + "\n") 8)

                    Expect.isEmpty
                        elifDiffOutcome.Findings
                        "2000 distinct #elif Bi arms stay clean at budget=8."

                    Expect.isLessThan
                        elifDiffAlloc
                        120_000_000L
                        "2000 distinct #elif Bi arms maintain incremental negated priors linearly in allocation."

                    let nestedDefinesBuilder = System.Text.StringBuilder()

                    for i = 0 to 1599 do
                        nestedDefinesBuilder.Append($"#define D{i}\n") |> ignore

                    for i = 0 to 1599 do
                        nestedDefinesBuilder.Append($"#if D{i}\n") |> ignore

                    nestedDefinesBuilder.Append("class Inner { }\n#else\nclass Alt { }\n#endif\n")
                    |> ignore

                    for _ = 1 to 1599 do
                        nestedDefinesBuilder.Append("#endif\n") |> ignore

                    let nestedDefines1600 = nestedDefinesBuilder.ToString()

                    let struct (nestedDefinesOutcome, nestedDefinesAlloc) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate nestedDefines1600 (nestedDefines1600 + "\n") 8)

                    Expect.isEmpty
                        nestedDefinesOutcome.Findings
                        "1600 defined symbols with nested #if/#else stay clean at budget=8."

                    Expect.isLessThan
                        nestedDefinesAlloc
                        250_000_000L
                        "1600 defined symbols with nested #if/#else use cached witness hashes instead of quadratic Set comparisons."

                    let impossibleNestedCases =
                        [
                            "const-false",
                            "#if false\n"
                            + String.Concat([| for i in 0..7 -> $"#if B{i}\n#endif\n" |])
                            + "#endif\n#if A\nclass C { int x = 1; }\n#endif\n"
                            "contradictory-if",
                            "#if Z\n"
                            + String.Concat([| for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" |])
                            + "#endif\n#if A\nclass C { int x = 1; }\n#endif\n"
                            "contradictory-elif",
                            "#if Y\n#elif W\n"
                            + String.Concat([| for i in 0..7 -> $"#if Y && B{i}\n#endif\n" |])
                            + "#endif\n#if A\nclass C { int x = 1; }\n#endif\n"
                            "contradictory-else",
                            "#if !Z\n#else\n"
                            + String.Concat([| for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" |])
                            + "#endif\n#if A\nclass C { int x = 1; }\n#endif\n"
                            "after-const-true",
                            "#if true\n#elif P\n"
                            + String.Concat([| for i in 0..7 -> $"#if B{i}\n#endif\n" |])
                            + "#else\n"
                            + String.Concat([| for i in 0..7 -> $"#if C{i}\n#endif\n" |])
                            + "#endif\n#if A\nclass C { int x = 1; }\n#endif\n"
                            "undef-in-const-true-if",
                            "#define Z\n#if Z\n#undef Z\n#if A\nclass C { int x = 1; }\n#endif\n#endif\n"
                            "define-in-conditional-if",
                            "#if !Z\n#define Z\n#if A\nclass C { int x = 1; }\n#endif\n#endif\n"
                            "nested-two-symbols",
                            "#if Z\n#if Y\nclass C { int x = 1; }\n#endif\n#endif\n"
                        ]

                    for label, src in impossibleNestedCases do
                        let outcome = Adjudicator.adjudicate src (src.Replace("x = 1", "x = 9")) 8

                        Expect.isNonEmpty
                            outcome.Findings
                            $"Unreachable nested branches ({label}) must not starve later reachable configuration #if A at budget=8."

                    let nestedFalse8000 =
                        "#if false\n"
                        + String.replicate 8000 "#if B\n"
                        + String.replicate 8000 "#endif\n"
                        + "#endif\n#if A\nclass C { int x = 1; }\n#endif\n"

                    let struct (nestedFalseOutcome, _) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate
                                nestedFalse8000
                                (nestedFalse8000.Replace("x = 1", "x = 9"))
                                8)

                    Expect.isNonEmpty
                        nestedFalseOutcome.Findings
                        "8000 nested #if B directives inside #if false are skipped without exhausting budget for later #if A."

                    Expect.equal
                        nestedFalseOutcome.Configurations
                        2
                        "8000 nested #if B directives inside #if false only test base and A."

                    let guardedDefineCases =
                        [
                            "if-guarded-define",
                            "#if !A\n#define Z\n#endif\n"
                            + String.Concat([| for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" |])
                            + "#if !Z\nclass C { int x = 1; }\n#endif\n"
                            "else-guarded-define",
                            "#if A\n#else\n#define Z\n#endif\n"
                            + String.Concat([| for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" |])
                            + "#if !Z\nclass C { int x = 1; }\n#endif\n"
                            "before-elif-guarded-define",
                            "#if !A\n#define Z\n#elif C\n#else\n#endif\n"
                            + String.Concat([| for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" |])
                            + "#if !Z\nclass C { int x = 1; }\n#endif\n"
                            "guarded-define-then-undef",
                            "#if !A\n#define Z\n#endif\n#if !B\n#undef Z\n#endif\n#if Z\nclass C { int x = 1; }\n#endif\n"
                            "nested-guarded-define",
                            "#if !A\n#if !B\n#define Z\n#endif\n#endif\n"
                            + String.Concat([| for i in 0..7 -> $"#if !Z && C{i}\n#endif\n" |])
                            + "#if !Z\nclass C { int x = 1; }\n#endif\n"
                        ]

                    for label, src in guardedDefineCases do
                        let badOutcome =
                            Adjudicator.adjudicate src (src.Replace("x = 1", "x = 9")) 8

                        Expect.isNonEmpty
                            badOutcome.Findings
                            $"Guarded preprocessor override ({label}) must preserve dependencies past #endif at budget=8."

                        let cleanOutcome = Adjudicator.adjudicate src (src + "\n") 8

                        Expect.isEmpty
                            cleanOutcome.Findings
                            $"Guarded preprocessor override ({label}) stays clean under whitespace-only change."

                    let nestedDisj4000 =
                        String.Concat([| for i in 0..3999 -> $"#if A || X{i}\n" |])
                        + "class C {}\n"
                        + String.replicate 4000 "#endif\n"

                    let struct ((nestedDisjOutcome, nestedDisjElapsed), nestedDisjAlloc) =
                        runMeasured (fun () ->
                            let timer = System.Diagnostics.Stopwatch.StartNew()

                            let outcome =
                                Adjudicator.adjudicate nestedDisj4000 (nestedDisj4000 + "\n") 8

                            timer.Stop()
                            outcome, timer.Elapsed.TotalSeconds)

                    Expect.isEmpty
                        nestedDisjOutcome.Findings
                        "4000 nested #if A || Xi directives stay clean."

                    Expect.isLessThan
                        nestedDisjElapsed
                        5.0
                        "4000 nested #if A || Xi directives reuse inherited constraint proofs linearly."

                    Expect.isLessThan
                        nestedDisjAlloc
                        500_000_000L
                        "4000 nested #if A || Xi directives avoid quadratic alternate allocations."

                    let inactiveGuardedSrc =
                        "#if Y\n#define Z\n#endif\n"
                        + String.Concat(
                            [|
                                for i in 0..7 -> $"#if Y && !Z && B{i}\nclass K{i} {{ }}\n#endif\n"
                            |]
                        )
                        + "#if A\nclass M { int x = 1; }\n#endif\n"

                    let inactiveGuardedMutated =
                        Adjudicator.adjudicate
                            inactiveGuardedSrc
                            (inactiveGuardedSrc.Replace("x = 1", "x = 9"))
                            8

                    Expect.isNonEmpty
                        inactiveGuardedMutated.Findings
                        "Inactive guarded #define Z under #if Y blocks impossible Y && !Z branches from exhausting budget 8."

                    let elifOverrideOrderSrc =
                        "#if X\n#define Z\n#elif Y\n#undef Z\n#endif\n#if X && Z\nclass C { int x = 1; }\n#endif\n#if !X && Y && Z\nclass D { int y = 1; }\n#endif\n"

                    Expect.isNonEmpty
                        (Adjudicator.adjudicate
                            elifOverrideOrderSrc
                            (elifOverrideOrderSrc.Replace("x = 1", "x = 9"))
                            8)
                            .Findings
                        "#elif arm preserves #define Z under #if X while keeping arm order intact."

                    Expect.isEmpty
                        (Adjudicator.adjudicate
                            elifOverrideOrderSrc
                            (elifOverrideOrderSrc.Replace("y = 1", "y = 9"))
                            8)
                            .Findings
                        "#elif #undef Z under !X && Y prevents false witness for impossible !X && Y && Z."

                    let chain6000Src =
                        "#if !A\n#define D0\n#endif\n"
                        + String.Concat(
                            [| for i in 1..5999 -> $"#if D{i - 1}\n#define D{i}\n#endif\n" |]
                        )
                        + "#if D5999\nclass C { int x = 1; }\n#endif\n"

                    Expect.isEmpty
                        (Adjudicator.adjudicate chain6000Src (chain6000Src + "\n") 0).Findings
                        "6000-link guarded define chain evaluates iteratively without stack overflow at budget=0."

                    Expect.isNonEmpty
                        (Adjudicator.adjudicate
                            chain6000Src
                            (chain6000Src.Replace("x = 1", "x = 9"))
                            8)
                            .Findings
                        "6000-link guarded define chain retains finding detection at budget=8."

                    let nestedDefines400 =
                        String.Concat([| for i in 0..399 -> $"#if !A\n#define D{i}\n" |])
                        + "class C {}\n"
                        + String.replicate 400 "#endif\n"

                    let struct (nestedDefinesOutcome, nestedDefinesAlloc) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate nestedDefines400 (nestedDefines400 + "\n") 0)

                    Expect.isEmpty
                        nestedDefinesOutcome.Findings
                        "400 nested #if !A blocks with local #define stay clean."

                    Expect.isLessThan
                        nestedDefinesAlloc
                        40_000_000L
                        "Sharing guard nodes across nested conditionals avoids cubic array-copy allocations."

                    let diamondNeg n =
                        "#if !A\n#define D0\n#endif\n"
                        + String.Concat(
                            [|
                                for i in 1..n -> $"#if D{i - 1} && D{i - 1}\n#define D{i}\n#endif\n"
                            |]
                        )
                        + $"#if D{n}\nclass C {{ int x = 1; }}\n#endif\n"

                    let d25 = diamondNeg 25

                    let struct (d25Outcome, d25Alloc) =
                        runMeasured (fun () -> Adjudicator.adjudicate d25 (d25 + "\n") 0)

                    Expect.isEmpty
                        d25Outcome.Findings
                        "25-link diamond guarded define chain evaluates linearly with symbolBudget=0."

                    Expect.isLessThan
                        d25Alloc
                        25_000_000L
                        "25-link diamond guarded define chain avoids exponential guard expansion."

                    let d100 = diamondNeg 100

                    let struct (d100Outcome, _) =
                        runMeasured (fun () ->
                            Adjudicator.adjudicate d100 (d100.Replace("x = 1", "x = 9")) 8)

                    Expect.isNonEmpty
                        d100Outcome.Findings
                        "100-link diamond guarded define chain detects active-branch mutation."

                    let diamondPos25 =
                        "#if A\n#define D0\n#endif\n"
                        + String.Concat(
                            [|
                                for i in 1..25 ->
                                    $"#if D{i - 1} && D{i - 1}\n#define D{i}\n#endif\n"
                            |]
                        )
                        + "#if D25\nclass C { int x = 1; }\n#endif\n"

                    let diamondPosMutated =
                        Adjudicator.adjudicate
                            diamondPos25
                            (diamondPos25.Replace("x = 1", "x = 9"))
                            8

                    Expect.isNonEmpty
                        diamondPosMutated.Findings
                        "Positive 25-link diamond guarded define chain solves #define A without exponential evalCondition blowup."

                    let dupOrCond = String.concat " || " (List.replicate 13 "A")

                    let dupElifSrc n =
                        $"#if {dupOrCond}\n"
                        + String.replicate n $"#elif {dupOrCond}\n"
                        + "#endif\nclass C {}\n"

                    let s1000 = dupElifSrc 1000
                    let s4000 = dupElifSrc 4000

                    let struct (_, dupElif1000Alloc) =
                        runMeasured (fun () -> Adjudicator.adjudicate s1000 (s1000 + "\n") 8)

                    let struct (dupElifOutcome, dupElifAlloc) =
                        runMeasured (fun () -> Adjudicator.adjudicate s4000 (s4000 + "\n") 8)

                    Expect.isEmpty
                        dupElifOutcome.Findings
                        "4000 unreachable #elif arms with duplicate-witness || conditions stay clean."

                    Expect.isLessThan
                        dupElifAlloc
                        (dupElif1000Alloc * 5L)
                        "Duplicate witnesses do not set rootCapped or trigger quadratic solveConstrainedCandidates."
            )

            testCase
                "Inequality comparison against true tracks false-branch dependencies for overridden symbols"
            <| fun () ->
                let source =
                    String.concat
                        "\n"
                        [
                            "#if A"
                            "#define X"
                            "#else"
                            "#undef X"
                            "#endif"
                            "#if X != true && C"
                            "class K { int a = [1]; }"
                            "#endif"
                            "class D { int b = [1,]; }"
                            ""
                        ]

                let clean =
                    String.concat
                        "\n"
                        [
                            "#if A"
                            "#define X"
                            "#else"
                            "#undef X"
                            "#endif"
                            "#if X != true && C"
                            "class K { int a = [1]; }"
                            "#endif"
                            "class D { int b = [1]; }"
                            ""
                        ]

                let tampered =
                    String.concat
                        "\n"
                        [
                            "#if A"
                            "#define X"
                            "#else"
                            "#undef X"
                            "#endif"
                            "#if X != true && C"
                            "class K { int a = [2]; }"
                            "#endif"
                            "class D { int b = [1]; }"
                            ""
                        ]

                let cleanOutcome = Adjudicator.adjudicate source clean 32
                Expect.isEmpty cleanOutcome.Findings "Clean X != true && C branch stays proven."

                let tamperedOutcome = Adjudicator.adjudicate source tampered 32

                Expect.isNonEmpty
                    tamperedOutcome.Findings
                    "Watcher index retains dependency on false-evaluated X inside X != true && C."

            testCase "Fallback constraint solver rechecks outer watchers and target expressions"
            <| fun () ->
                let source =
                    String.concat
                        "\n"
                        [
                            "#if A0"
                            "class K0 { }"
                            "#endif"
                            "#if A1"
                            "class K1 { }"
                            "#endif"
                            "#if (A0 || A1) && B"
                            "#if !(A0) && !(A1)"
                            "#else"
                            "#if X0 || X1 || X2 || X3 || X4"
                            "#if Y0 || Y1 || Y2 || Y3 || Y4"
                            "#if F"
                            "class G { int a = [1]; }"
                            "#endif"
                            "#endif"
                            "#endif"
                            "#endif"
                            "#endif"
                            "class R { int b = [1,]; }"
                            ""
                        ]

                let tampered =
                    String.concat
                        "\n"
                        [
                            "#if A0"
                            "class K0 { }"
                            "#endif"
                            "#if A1"
                            "class K1 { }"
                            "#endif"
                            "#if (A0 || A1) && B"
                            "#if !(A0) && !(A1)"
                            "#else"
                            "#if X0 || X1 || X2 || X3 || X4"
                            "#if Y0 || Y1 || Y2 || Y3 || Y4"
                            "#if F"
                            "class G { int a = [2]; }"
                            "#endif"
                            "#endif"
                            "#endif"
                            "#endif"
                            "#endif"
                            "class R { int b = [1]; }"
                            ""
                        ]

                let cleanOutcome = Adjudicator.adjudicate source source 32

                Expect.isEmpty
                    cleanOutcome.Findings
                    "Untampered constrained fallback file stays proven."

                let tamperedOutcome = Adjudicator.adjudicate source tampered 32

                Expect.isNonEmpty
                    tamperedOutcome.Findings
                    "Fallback solver preserves satisfiable A0/B/F branch without violating outer !(A0) && !(A1) prior."

            testSequenced (
                testCase
                    "Chained conditional overrides, nested diamonds, and deep external guards scale linearly with directive count"
                <| fun () ->
                    let buildChain withUndef count =
                        let sb = System.Text.StringBuilder()

                        if withUndef then
                            for i = 0 to count do
                                sb.Append("#undef D").Append(i).Append('\n') |> ignore

                        sb.Append("#if R0\n#define D0\n#endif\n") |> ignore

                        for i = 1 to count do
                            sb.Append("#if D").Append(i - 1).Append('\n') |> ignore
                            sb.Append("#define D").Append(i).Append('\n') |> ignore
                            sb.Append("#endif\n") |> ignore

                        sb.Append("class C { }\n") |> ignore
                        sb.ToString()

                    let measureChain withUndef count =
                        let src = buildChain withUndef count
                        let before = GC.GetAllocatedBytesForCurrentThread()
                        let outcome = Adjudicator.adjudicate src src 32
                        let after = GC.GetAllocatedBytesForCurrentThread()
                        outcome, after - before

                    measureChain true 32
                    |> fst
                    |> fun o -> Expect.isEmpty o.Findings "Warmup undef chain stays clean."

                    measureChain false 32
                    |> fst
                    |> fun o -> Expect.isEmpty o.Findings "Warmup no-undef chain stays clean."

                    let undefSmall, undefSmallAlloc = measureChain true 300
                    let undefLarge, undefLargeAlloc = measureChain true 1200
                    Expect.isEmpty undefSmall.Findings "300-link undef chain stays clean."
                    Expect.isEmpty undefLarge.Findings "1200-link undef chain stays clean."

                    Expect.isLessThan
                        undefLargeAlloc
                        (undefSmallAlloc * 6L)
                        "Overridden deep guard chain scales linearly without quadratic guard re-evaluation."

                    let extSmall, extSmallAlloc = measureChain false 300
                    let extLarge, extLargeAlloc = measureChain false 1200
                    Expect.isEmpty extSmall.Findings "300-link external guard chain stays clean."
                    Expect.isEmpty extLarge.Findings "1200-link external guard chain stays clean."

                    Expect.isLessThan
                        extLargeAlloc
                        (extSmallAlloc * 6L)
                        "Deep external guard chain reuses dependency-profile cache linearly."

                    let buildNestedDiamond (useElif: bool) count =
                        let sb = System.Text.StringBuilder()

                        for i = 0 to count do
                            sb.Append("#undef D").Append(i).Append('\n') |> ignore

                        sb.Append("#if WRAP\n") |> ignore

                        if useElif then
                            sb.Append("#if false\n#elif A\n#define D0\n#endif\n") |> ignore

                            for i = 1 to count do
                                sb
                                    .Append("#if false\n#elif D")
                                    .Append(i - 1)
                                    .Append(" && D")
                                    .Append(i - 1)
                                    .Append("\n#define D")
                                    .Append(i)
                                    .Append("\n#endif\n")
                                |> ignore
                        else
                            sb.Append("#if A\n#define D0\n#endif\n") |> ignore

                            for i = 1 to count do
                                sb
                                    .Append("#if D")
                                    .Append(i - 1)
                                    .Append(" && D")
                                    .Append(i - 1)
                                    .Append("\n#define D")
                                    .Append(i)
                                    .Append("\n#endif\n")
                                |> ignore

                        sb
                            .Append("#if D")
                            .Append(count)
                            .Append(
                                "\nclass Inner { int x = 1; }\n#endif\n#endif\nclass Outer { }\n"
                            )
                        |> ignore

                        sb.ToString()

                    for useElif in [ false; true ] do
                        let nested20 = buildNestedDiamond useElif 20
                        let b0 = GC.GetAllocatedBytesForCurrentThread()
                        let cleanOutcome = Adjudicator.adjudicate nested20 (nested20 + " ") 8
                        let b1 = GC.GetAllocatedBytesForCurrentThread()

                        Expect.isEmpty
                            cleanOutcome.Findings
                            $"Nested diamond chain (useElif=%b{useElif}) stays clean."

                        Expect.isLessThan
                            (b1 - b0)
                            40_000_000L
                            $"Nested diamond chain (useElif=%b{useElif}) caches const guard checks in scope."

                    let buildCappedElifChain (distinctArms: bool) count =
                        let sb = System.Text.StringBuilder()

                        let wideOr =
                            "A0 || A1 || A2 || A3 || A4 || A5 || A6 || A7 || A8 || A9 || A10 || A11 || A12"

                        sb.Append("#if ").Append(wideOr).Append("\nclass C0 { int x = 1; }\n")
                        |> ignore

                        for i = 1 to count do
                            if distinctArms then
                                sb
                                    .Append("#elif (")
                                    .Append(wideOr)
                                    .Append(") && B")
                                    .Append(i)
                                    .Append('\n')
                                    .Append("class C")
                                    .Append(i)
                                    .Append(" { }\n")
                                |> ignore
                            else
                                sb
                                    .Append("#elif ")
                                    .Append(wideOr)
                                    .Append('\n')
                                    .Append("class C")
                                    .Append(i)
                                    .Append(" { }\n")
                                |> ignore

                        sb.Append("#else\nclass CE { }\n#endif\n") |> ignore
                        sb.ToString()

                    let measureElif distinctArms count =
                        let src = buildCappedElifChain distinctArms count
                        let a0 = GC.GetAllocatedBytesForCurrentThread()
                        let outcome = Adjudicator.adjudicate src (src + " ") 8
                        let a1 = GC.GetAllocatedBytesForCurrentThread()
                        outcome, a1 - a0

                    for distinctArms in [ false; true ] do
                        let smallOut, smallAlloc = measureElif distinctArms 400
                        let largeOut, largeAlloc = measureElif distinctArms 1600

                        Expect.isEmpty
                            smallOut.Findings
                            $"400-arm capped #elif chain (distinct={distinctArms}) stays clean."

                        Expect.isEmpty
                            largeOut.Findings
                            $"1600-arm capped #elif chain (distinct={distinctArms}) stays clean."

                        Expect.isLessThan
                            largeAlloc
                            (smallAlloc * 6L)
                            $"1600-arm capped #elif chain (distinct={distinctArms}) scales linearly."

                    let unsatRescuedSrc =
                        "#if !(X0 || X1 || X2 || X3 || X4 || X5 || X6 || X7 || X8 || X9)\nint a = 1;\n#elif X0 && !X0\nint dead = 1;\n#elif Z\nint b = 1;\n#endif\n"

                    let unsatRescuedFmt =
                        "#if !(X0 || X1 || X2 || X3 || X4 || X5 || X6 || X7 || X8 || X9)\nint a = 1;\n#elif X0 && !X0\nint dead = 1;\n#elif Z\nint b = 2;\n#endif\n"

                    let unsatRescuedOut = Adjudicator.adjudicate unsatRescuedSrc unsatRescuedFmt 8

                    Expect.isNonEmpty
                        unsatRescuedOut.Findings
                        "Reachable #elif Z after capped UnsatOnEmpty prior catches semantic tamper."

                    let deepShort =
                        "#if false && ("
                        + String.concat " && " [ for i in 0..49999 -> $"X{i}" ]
                        + ")\nclass C {}\n#endif\n"

                    let deepOutcome = Adjudicator.adjudicate deepShort (deepShort + " ") 0

                    Expect.isEmpty
                        deepOutcome.Findings
                        "Deep short-circuited conjunction does not stack overflow."

                    let buildWatchedConjunction count =
                        let rec conj lo hi =
                            if lo = hi then
                                $"X{lo}"
                            else
                                let mid = (lo + hi) / 2
                                $"({conj lo mid} && {conj (mid + 1) hi})"

                        let c = conj 0 (count - 1)
                        $"#if !({c} && Z)\n#if {c}\nclass C {{ }}\n#endif\n#endif\n"

                    let watch2k = buildWatchedConjunction 2048
                    let watch8k = buildWatchedConjunction 8192
                    let w0 = GC.GetAllocatedBytesForCurrentThread()
                    let out2k = Adjudicator.adjudicate watch2k (watch2k + " ") 0
                    let w1 = GC.GetAllocatedBytesForCurrentThread()
                    let out8k = Adjudicator.adjudicate watch8k (watch8k + " ") 0
                    let w2 = GC.GetAllocatedBytesForCurrentThread()
                    Expect.isEmpty out2k.Findings "2k-symbol watched conjunction stays clean."
                    Expect.isEmpty out8k.Findings "8k-symbol watched conjunction stays clean."

                    Expect.isLessThan
                        (w2 - w1)
                        ((w1 - w0) * 6L)
                        "8k-symbol watched conjunction scales linearly via WatcherIndex deduplication."

                    let buildDeepNestedGuardedDefs count =
                        let sb = System.Text.StringBuilder()

                        for _ = 1 to count do
                            sb.Append("#if !A\n") |> ignore

                        sb.Append("#define S\n") |> ignore

                        for _ = 1 to count do
                            sb.Append("#endif\n") |> ignore

                        for _ = 1 to count do
                            sb.Append("#if S && B\n#endif\n") |> ignore

                        sb.Append("class C { }\n") |> ignore
                        sb.ToString()

                    let nested200 = buildDeepNestedGuardedDefs 200
                    let nested800 = buildDeepNestedGuardedDefs 800
                    let g0 = GC.GetAllocatedBytesForCurrentThread()
                    let gOut200 = Adjudicator.adjudicate nested200 (nested200 + " ") 8
                    let g1 = GC.GetAllocatedBytesForCurrentThread()
                    let gOut800 = Adjudicator.adjudicate nested800 (nested800 + " ") 8
                    let g2 = GC.GetAllocatedBytesForCurrentThread()
                    Expect.isEmpty gOut200.Findings "200 nested guarded uses stay clean."
                    Expect.isEmpty gOut800.Findings "800 nested guarded uses stay clean."

                    Expect.isLessThan
                        (g2 - g1)
                        ((g1 - g0) * 6L)
                        "800 nested sealed guard chain uses reuse witness expansion linearly."

                    let buildRepeatedSkippedHistory (interleaved: bool) count =
                        let sb = System.Text.StringBuilder()

                        if interleaved then
                            for _ = 1 to count do
                                sb.Append("#if A\n#define S\n#endif\n#if S\n#endif\n") |> ignore
                        else
                            for _ = 1 to count do
                                sb.Append("#if A\n#define S\n#endif\n") |> ignore

                            for _ = 1 to count do
                                sb.Append("#if S\n#endif\n") |> ignore

                        sb.Append("class C { }\n") |> ignore
                        sb.ToString()

                    for interleaved in [ false; true ] do
                        let repSmall = buildRepeatedSkippedHistory interleaved 1600
                        let repLarge = buildRepeatedSkippedHistory interleaved 6400
                        let r0 = GC.GetAllocatedBytesForCurrentThread()
                        let rOutSmall = Adjudicator.adjudicate repSmall (repSmall + " ") 8
                        let r1 = GC.GetAllocatedBytesForCurrentThread()
                        let rOutLarge = Adjudicator.adjudicate repLarge (repLarge + " ") 8
                        let r2 = GC.GetAllocatedBytesForCurrentThread()

                        Expect.isEmpty
                            rOutSmall.Findings
                            $"1600 skipped override histories (interleaved={interleaved}) stay clean."

                        Expect.isEmpty
                            rOutLarge.Findings
                            $"6400 skipped override histories (interleaved={interleaved}) stay clean."

                        Expect.isLessThan
                            (r2 - r1)
                            ((r1 - r0) * 6L)
                            $"6400 skipped override histories (interleaved={interleaved}) scale linearly."

                    let dupTrueSrc =
                        "#if true\n#define Z\n#elif true\n#endif\n"
                        + String.concat "" [ for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" ]
                        + "#if A\nclass Target {}\n#endif\n"

                    let dupTrueOut =
                        Adjudicator.adjudicate dupTrueSrc (dupTrueSrc.Replace("Target", "Tamper")) 8

                    Expect.isNonEmpty
                        dupTrueOut.Findings
                        "Duplicate #elif true preserves unconditional #define Z from #if true."

                    let ghostSrc =
                        String.concat
                            ""
                            [
                                for i in 0..7 ->
                                    $"#if false\n#undef Z\n#elif Z && B{i}\nclass Dead{i} {{}}\n#endif\n"
                            ]
                        + "#if A\nclass Target {}\n#endif\n"

                    let ghostOut =
                        Adjudicator.adjudicate ghostSrc (ghostSrc.Replace("Target", "Tamper")) 8

                    Expect.isNonEmpty
                        ghostOut.Findings
                        "Skipped #undef before #elif does not spend budget on unreachable #elif Z && B."

                    let siblingUndefNotZSrc =
                        "#if false\n#undef Z\n#elif !Z && B\nclass Reached {}\n#endif\n"

                    let siblingUndefNotZOut =
                        Adjudicator.adjudicate
                            siblingUndefNotZSrc
                            (siblingUndefNotZSrc.Replace("Reached", "Tamper"))
                            8

                    Expect.isNonEmpty
                        siblingUndefNotZOut.Findings
                        "Skipped #undef before #elif !Z && B still discovers reachable {B} branch."

                    let siblingDefElifZSrc =
                        "#if false\n#define Z\n#elif Z && B\nclass Dead { }\n#endif\n#if Z\nclass AfterZ { }\n#endif\n"

                    let siblingDefElifZOut =
                        Adjudicator.adjudicate
                            siblingDefElifZSrc
                            (siblingDefElifZSrc.Replace("AfterZ", "Tamper"))
                            8

                    Expect.isNonEmpty
                        siblingDefElifZOut.Findings
                        "Sibling #define before #elif does not leak past #endif and reaches #if Z."

                    let siblingPosPreservedSrc =
                        "// Copyright\n#define Y\n"
                        + String.concat
                            ""
                            [
                                for i in 0..7 ->
                                    $"#if false\n#undef Z\n#elif !Z && !Y && B{i}\n#endif\n"
                            ]
                        + "#if A\nclass Target {}\n#endif\n"

                    let siblingPosPreservedOut =
                        Adjudicator.adjudicate
                            siblingPosPreservedSrc
                            (siblingPosPreservedSrc.Replace("Target", "Tamper"))
                            8

                    Expect.isNonEmpty
                        siblingPosPreservedOut.Findings
                        "Sibling override preserves remaining identifier SpanStart for earlier #define Y lookup."

                    let buildAliasChainWithDistractors aliasCount distractorCount =
                        let sb = System.Text.StringBuilder()

                        for i = 0 to aliasCount do
                            sb.Append("#undef D").Append(i).Append('\n') |> ignore

                        sb.Append("#if !A\n#define D0\n#endif\n") |> ignore

                        for i = 1 to aliasCount do
                            sb
                                .Append("#if D")
                                .Append(i - 1)
                                .Append("\n#define D")
                                .Append(i)
                                .Append("\n#endif\n")
                            |> ignore

                        sb
                            .Append("#if !D")
                            .Append(aliasCount)
                            .Append("\nclass Target { }\n#endif\n")
                        |> ignore

                        for i = 0 to distractorCount - 1 do
                            sb.Append("#if Z").Append(i).Append("\n#endif\n") |> ignore

                        sb.ToString()

                    let alias9Src = buildAliasChainWithDistractors 8 8
                    let alias9Clean = Adjudicator.adjudicate alias9Src (alias9Src + " ") 8

                    let alias9Tamper =
                        Adjudicator.adjudicate alias9Src (alias9Src.Replace("Target", "Tamper")) 8

                    Expect.isEmpty
                        alias9Clean.Findings
                        "9-link guarded alias chain with distractor blocks stays clean."

                    Expect.isNonEmpty
                        alias9Tamper.Findings
                        "9-link guarded alias chain preserves singleton witness beyond depth 8 under budget 8."

                    let deepAliasSrc = buildAliasChainWithDistractors 200 8
                    let deepAliasClean = Adjudicator.adjudicate deepAliasSrc (deepAliasSrc + " ") 8

                    let deepAliasTamper =
                        Adjudicator.adjudicate
                            deepAliasSrc
                            (deepAliasSrc.Replace("Target", "Tamper"))
                            8

                    Expect.isEmpty
                        deepAliasClean.Findings
                        "200-link guarded alias chain completes iteratively and stays clean."

                    Expect.isNonEmpty
                        deepAliasTamper.Findings
                        "200-link guarded alias chain finds witness without stack overflow or truncation."

                    for eqBudget in [ 8; 64 ] do
                        let eqNestedSrc =
                            "#if A == B\n#if A\nclass C { int x = 1; }\n#endif\n#endif\n"

                        let eqNestedOut =
                            Adjudicator.adjudicate
                                eqNestedSrc
                                (eqNestedSrc.Replace("1", "9"))
                                eqBudget

                        Expect.isNonEmpty
                            eqNestedOut.Findings
                            $"Nested #if A inside #if A == B recovers {{A,B}} at budget {eqBudget}."

                    let eqRepairSrc =
                        "#if A == B\n#if A || C\n#if !C\nclass Target { int x = 1; }\n#endif\n#endif\n#endif\n"

                    let eqRepairOut =
                        Adjudicator.adjudicate eqRepairSrc (eqRepairSrc.Replace("1", "9")) 8

                    Expect.isNonEmpty
                        eqRepairOut.Findings
                        "Constraint repair recovers invalidated outer A == B when inner guards force A and !C."

                    let eqZeroForcedSrc =
                        "#if A == B\n#if A != false\nclass Target { int x = 1; }\n#endif\n#endif\n"

                    let eqZeroForcedOut =
                        Adjudicator.adjudicate eqZeroForcedSrc (eqZeroForcedSrc.Replace("1", "9")) 8

                    Expect.isNonEmpty
                        eqZeroForcedOut.Findings
                        "Constraint solver repairs outer A == B even when inner guard leaves forced map empty."

                    let eqElseSrc =
                        "#if A == B\n#if !A\n#else\nclass Target { int x = 1; }\n#endif\n#endif\n"

                    let eqElseOut = Adjudicator.adjudicate eqElseSrc (eqElseSrc.Replace("1", "9")) 8

                    Expect.isNonEmpty
                        eqElseOut.Findings
                        "Constraint solver recovers outer A == B for negated inner #else arm."

                    let escapedSymSrc =
                        "#define \\u005A\n"
                        + String.concat "" [ for i in 0..7 -> $"#if !Z && B{i}\n#endif\n" ]
                        + "#if A\nclass Target { int x = 1; }\n#endif\n"

                    let escapedSymClean =
                        Adjudicator.adjudicate escapedSymSrc (escapedSymSrc + " ") 8

                    let escapedSymTamper =
                        Adjudicator.adjudicate escapedSymSrc (escapedSymSrc.Replace("1", "9")) 8

                    Expect.isEmpty
                        escapedSymClean.Findings
                        "Unicode-escaped #define \\u005A canonicalized as Z keeps clean file green."

                    Expect.isNonEmpty
                        escapedSymTamper.Findings
                        "Unicode-escaped #define \\u005A suppresses impossible !Z && Bi blocks so #if A is tested at budget 8."

                    for eqChainCount in [ 6; 12 ] do
                        let sbEq = System.Text.StringBuilder()

                        for i = eqChainCount - 1 downto 0 do
                            sbEq.Append($"#if S{i} == S{i + 1}\n") |> ignore

                        sbEq.Append("#if S0 && Z\nclass C { int x = 1; }\n#endif\n") |> ignore

                        for _ = 0 to eqChainCount - 1 do
                            sbEq.Append("#endif\n") |> ignore

                        let eqChainSrc = sbEq.ToString()

                        let eqChainOut =
                            Adjudicator.adjudicate
                                eqChainSrc
                                (eqChainSrc.Replace("x = 1", "x = 9"))
                                8

                        Expect.isTrue
                            (eqChainOut.Findings
                             |> List.exists (fun f ->
                                 f.Category = Category.Structural && f.Configuration <> "default"))
                            $"{eqChainCount}-equality chain S{eqChainCount - 1}==S{eqChainCount}..S0==S1 repairs to fixed point under budget 8."
            )
            testCase
                "enclosing constraints guide deep parity witnesses, propagate branch truncation, and repair linear equality chains"
                (fun () ->
                    let guidedParity =
                        "#if !F == (B || F)\n#if F != A != F != B != C == D\nclass C { int x = 1; }\n#endif\n#endif\n"

                    for budget in [ 8; 64 ] do
                        let cleanOut = Adjudicator.adjudicate guidedParity guidedParity budget

                        Expect.isEmpty
                            cleanOut.Findings
                            $"Clean guided parity file at budget {budget}."

                        let tamperOut =
                            Adjudicator.adjudicate
                                guidedParity
                                (guidedParity.Replace("x = 1", "x = 9"))
                                budget

                        Expect.isTrue
                            (tamperOut.Findings
                             |> List.exists (fun f ->
                                 f.Category = Category.Structural && f.Configuration <> "default"))
                            $"Constrained witness solver must not drop enclosing !F == (B || F) witness at budget {budget}."

                    for outerExpr in [ "F == B"; "F != B" ] do
                        let splitParity =
                            $"#if {outerExpr}\n#if F != A != F != B != C == D\nclass C {{ int x = 1; }}\n#endif\n#endif\n"

                        let splitOut =
                            Adjudicator.adjudicate
                                splitParity
                                (splitParity.Replace("x = 1", "x = 9"))
                                64

                        Expect.isTrue
                            (splitOut.Findings
                             |> List.exists (fun f ->
                                 f.Category = Category.Structural
                                 && (outerExpr = "F == B" || f.Configuration <> "default")))
                            $"Split recovery finds valid witness under enclosing '{outerExpr}'."

                    let cappedBranchSrc =
                        "#if X0 != X1 != X2 != X3 != X4 != X5 != X6 != X7 != X8 != X9\n"
                        + "#if !(X0 != X1 != X2 != X3 != X4 != X5 != X6 != X7 != X8 != X9)\n"
                        + "class C { int x = 1; }\n#endif\n#endif\n"

                    let cappedOut = Adjudicator.adjudicate cappedBranchSrc cappedBranchSrc 64

                    Expect.isEmpty
                        cappedOut.Findings
                        "Unmodified high-arity truncated branch has no findings."

                    Expect.isLessThan
                        cappedOut.Configurations
                        65
                        "Truncated branch check does not require exhausting all 64 budget configs."

                    Expect.isTrue
                        cappedOut.SymbolsCapped
                        "Branch truncation must propagate into Outcome.SymbolsCapped = true."

                    let buildEq n =
                        let sb = System.Text.StringBuilder()

                        for i = n - 1 downto 0 do
                            sb.Append($"#if S{i} == S{i + 1}\n") |> ignore

                        sb.Append("#if S0 && Z\nclass C { int x = 1; }\n#endif\n") |> ignore

                        for _ = 0 to n - 1 do
                            sb.Append("#endif\n") |> ignore

                        sb.ToString()

                    let buildHard n =
                        let sb = System.Text.StringBuilder()

                        for i = n - 1 downto 0 do
                            sb.Append(
                                $"#if (S{i} == S{i + 1}) || (A{i} && B{i} && C{i} && D{i})\n"
                            )
                            |> ignore

                        sb.Append("#if S0 && Z\nclass C { int x = 1; }\n#endif\n") |> ignore

                        for _ = 0 to n - 1 do
                            sb.Append("#endif\n") |> ignore

                        sb.ToString()

                    let measureChain (builder: int -> string) (n: int) =
                        let src = builder n
                        let a0 = System.GC.GetAllocatedBytesForCurrentThread()
                        let cleanOut = Adjudicator.adjudicate src src 8
                        let alloc = System.GC.GetAllocatedBytesForCurrentThread() - a0
                        Expect.isEmpty cleanOut.Findings $"Clean chain n={n}."
                        alloc

                    ignore (measureChain buildEq 64)
                    ignore (measureChain buildHard 64)

                    let eq512 = measureChain buildEq 512
                    let eq2048 = measureChain buildEq 2048

                    Expect.isLessThan
                        eq2048
                        (max 100_000_000L (eq512 * 8L))
                        "2048-link equality chain scales linearly."

                    Expect.isLessThan
                        eq2048
                        900_000_000L
                        "2048-link equality chain avoids quadratic allocation."

                    let eq2048Src = buildEq 2048

                    let eq2048Tamper =
                        Adjudicator.adjudicate eq2048Src (eq2048Src.Replace("x = 1", "x = 9")) 8

                    Expect.isTrue
                        (eq2048Tamper.Findings
                         |> List.exists (fun f ->
                             f.Category = Category.Structural && f.Configuration <> "default"))
                        "2048-link equality chain catches inner tamper in non-default config."

                    let hard512 = measureChain buildHard 512
                    let hard2048 = measureChain buildHard 2048

                    Expect.isLessThan
                        hard2048
                        (max 100_000_000L (hard512 * 8L))
                        "2048-link 5-var repair chain scales linearly."

                    Expect.isLessThan
                        hard2048
                        900_000_000L
                        "2048-link 5-var repair chain avoids quadratic allocation."

                    let hard2048Src = buildHard 2048

                    let hard2048Tamper =
                        Adjudicator.adjudicate
                            hard2048Src
                            (hard2048Src.Replace("x = 1", "x = 9"))
                            8

                    Expect.isTrue
                        (hard2048Tamper.Findings
                         |> List.exists (fun f ->
                             f.Category = Category.Structural && f.Configuration <> "default"))
                        "2048-link 5-var repair chain catches inner tamper in non-default config.")
            testCase
                "shared elif prior-guard chains scale linearly and preserve nested and negated arm semantics"
                (fun () ->
                    let nestedElifSrc =
                        "#if X0\n#define Z\n#elif X1\n#define A\n#if Y1\n#define W\n#endif\n#elif X2\n#define Z\n#endif\n#if W\nclass CW { int x = 1; }\n#endif\n#if !X0 && !X1 && X2 && Z\nclass CZ { int y = 1; }\n#endif\n"

                    Expect.isEmpty
                        (Adjudicator.adjudicate nestedElifSrc nestedElifSrc 16).Findings
                        "Clean nested elif guard chain."

                    Expect.isNonEmpty
                        (Adjudicator.adjudicate
                            nestedElifSrc
                            (nestedElifSrc.Replace("x = 1", "x = 2"))
                            16)
                            .Findings
                        "Shared PriorNegNode preserves nested #elif + inner #if guard for W."

                    Expect.isNonEmpty
                        (Adjudicator.adjudicate
                            nestedElifSrc
                            (nestedElifSrc.Replace("y = 1", "y = 2"))
                            16)
                            .Findings
                        "Shared PriorNegNode preserves !X0 && !X1 && X2 && Z guard for CZ."

                    let buildUnreach n =
                        let sb = System.Text.StringBuilder()
                        sb.Append("#if A\nint a = 1;\n") |> ignore

                        for i = 0 to n - 1 do
                            sb.Append($"#elif A && X{i} && !X{i}\n#define Z\nint b{i} = 1;\n")
                            |> ignore

                        sb.Append("#endif\n") |> ignore
                        sb.ToString()

                    let buildReach n =
                        let sb = System.Text.StringBuilder()
                        sb.Append("#if X0\n#define Z\nint a = 1;\n") |> ignore

                        for i = 1 to n - 1 do
                            sb.Append($"#elif X{i}\n#define Z\nint b{i} = 1;\n") |> ignore

                        sb.Append("#endif\n#if Z\nclass C { int x = 1; }\n#endif\n") |> ignore
                        sb.ToString()

                    let measure (builder: int -> string) (n: int) =
                        let src = builder n
                        let a0 = System.GC.GetAllocatedBytesForCurrentThread()
                        let out = Adjudicator.adjudicate src src 8
                        let alloc = System.GC.GetAllocatedBytesForCurrentThread() - a0
                        Expect.isEmpty out.Findings $"Clean elif chain n={n}."
                        alloc

                    ignore (measure buildUnreach 64)
                    ignore (measure buildReach 64)

                    let u500 = measure buildUnreach 500
                    let u2000 = measure buildUnreach 2000

                    Expect.isLessThan
                        u2000
                        (max 80_000_000L (u500 * 6L))
                        "Unreachable elif override chain scales linearly."

                    Expect.isLessThan
                        u2000
                        350_000_000L
                        "Unreachable elif chain avoids quadratic allocation."

                    let r500 = measure buildReach 500
                    let r2000 = measure buildReach 2000

                    Expect.isLessThan
                        r2000
                        (max 80_000_000L (r500 * 6L))
                        "Reachable elif override chain scales linearly."

                    Expect.isLessThan
                        r2000
                        200_000_000L
                        "Reachable elif chain avoids quadratic allocation.")
            testCase
                "repeated self-negating override histories reuse fallback memos in linear allocation"
                (fun () ->
                    let buildSelfNeg sameSym n =
                        let sb = System.Text.StringBuilder()
                        sb.Append("#define Z\n") |> ignore

                        for i = 0 to n - 1 do
                            let sym = if sameSym then "A" else $"A{i}"

                            sb.Append($"#if {sym} && Z\n#undef Z\nint x{i} = 1;\n#endif\n")
                            |> ignore

                        sb.ToString()

                    let measureSelfNeg sameSym n =
                        let src = buildSelfNeg sameSym n
                        let a0 = System.GC.GetAllocatedBytesForCurrentThread()
                        let out = Adjudicator.adjudicate src (src + " ") 8
                        let alloc = System.GC.GetAllocatedBytesForCurrentThread() - a0

                        Expect.isEmpty
                            out.Findings
                            $"Self-negating override chain clean for n={n}, sameSym={sameSym}."

                        alloc

                    ignore (measureSelfNeg true 32)
                    ignore (measureSelfNeg false 32)

                    let same256 = measureSelfNeg true 256
                    let same1024 = measureSelfNeg true 1024

                    Expect.isLessThan
                        same1024
                        (max 60_000_000L (same256 * 7L))
                        "Same-symbol self-negating chain scales linearly."

                    Expect.isLessThan
                        same1024
                        300_000_000L
                        "Same-symbol self-negating chain avoids quadratic fallback allocation."

                    let dist256 = measureSelfNeg false 256
                    let dist1024 = measureSelfNeg false 1024

                    Expect.isLessThan
                        dist1024
                        (max 80_000_000L (dist256 * 7L))
                        "Distinct-symbol self-negating chain scales linearly."

                    Expect.isLessThan
                        dist1024
                        450_000_000L
                        "Distinct-symbol self-negating chain avoids quadratic fallback allocation.")
        ]
