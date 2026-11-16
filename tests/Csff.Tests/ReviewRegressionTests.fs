module Csff.Tests.ReviewRegressionTests

open System
open System.Buffers
open System.Collections.Generic
open System.Diagnostics
open System.IO
open System.Text
open System.Threading
open Csff.Cli
open Csff.Conformance
open Csff.Parser
open Csff.Printer
open Expecto
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

let private withDirectory action =
    let directory =
        Path.Combine(Path.GetTempPath(), "csff-review-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory directory |> ignore
    File.WriteAllText(Path.Combine(directory, ".editorconfig"), "root = true\n")

    try
        action directory
    finally
        Directory.Delete(directory, true)

let private print source settings =
    use worker = new Worker()

    match worker.PrintChecked("test.cs", source, settings) with
    | null -> ()
    | unverified -> failtest unverified

    let output = worker.OutputText
    output.ToString()

let private stable source settings =
    let output = print source settings
    Expect.equal (print output settings) output "Formatting is idempotent."
    output

let private stableUnprovable source settings =
    use worker = new Worker()

    Expect.isNotNull
        (worker.PrintChecked("test.cs", source, settings, secondPrint = false))
        "This pair is recorded as one no layer can prove; it is provable now."

    let output = worker.OutputText.ToString()
    Expect.equal (print output settings) output "Formatting is idempotent."
    output

let private lines (items: string list) = String.concat "\n" items + "\n"

let private incompleteConditionalMember body =
    "class C\n{\n    int P\n#if S\n        => 1;\n#endif\n"
    + "    void M()\n    {\n#if S\n        return;\n#else\n"
    + body
    + "#endif\n    }\n}\n"

let private deadLiteral literal =
    "class C\n{\n    void M()\n    {\n#if false\n        var s = "
    + literal
    + ";\n#endif\n    }\n}\n"

let private invoke args =
    let originalOut, originalError = Console.Out, Console.Error
    use output = new StringWriter()
    use errors = new StringWriter()

    try
        Console.SetOut output
        Console.SetError errors
        let code = Program.run args
        code, output.ToString(), errors.ToString()
    finally
        Console.SetOut originalOut
        Console.SetError originalError

let private compilationErrors (source: string) =
    let references =
        (AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") :?> string).Split(Path.PathSeparator)
        |> Array.map (fun path -> MetadataReference.CreateFromFile(path) :> MetadataReference)

    CSharpCompilation
        .Create(
            "regression",
            [
                CSharpSyntaxTree.ParseText(source, CSharpParseOptions(LanguageVersion.Preview))
            ],
            references,
            CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)
        )
        .GetDiagnostics()
    |> Seq.filter (fun diagnostic -> diagnostic.Severity = DiagnosticSeverity.Error)
    |> Seq.map (fun diagnostic -> diagnostic.Id)
    |> Seq.toArray

let private endOfLineCommentCells =
    [
        "an own-line // comment below a trailing // comment",
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "    ["
                "        1, 1, 0, // first"
                "        // second"
                "        0, 0, 1,"
                "    ];"
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ],
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "        ["
                "            1,"
                "            1,"
                "            0, // first"
                "            // second"
                "            0,"
                "            0,"
                "            1,"
                "        ];"
                ""
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ]
        "an own-line /* */ comment below a trailing // comment",
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "    ["
                "        1, 1, 0, // first"
                "        /* second */"
                "        0, 0, 1,"
                "    ];"
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ],
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "        ["
                "            1,"
                "            1,"
                "            0, // first"
                "            /* second */"
                "            0,"
                "            0,"
                "            1,"
                "        ];"
                ""
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ]
        "an own-line // comment below a trailing /* */ comment",
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "    ["
                "        1, 1, 0, /* first */"
                "        // second"
                "        0, 0, 1,"
                "    ];"
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ],
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "        ["
                "            1,"
                "            1,"
                "            0, /* first */"
                "            // second"
                "            0,"
                "            0,"
                "            1,"
                "        ];"
                ""
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ]
        "an own-line /* */ comment below a trailing /* */ comment",
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "    ["
                "        1, 1, 0, /* first */"
                "        /* second */"
                "        0, 0, 1,"
                "    ];"
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ],
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "        ["
                "            1,"
                "            1,"
                "            0, /* first */"
                "            /* second */"
                "            0,"
                "            0,"
                "            1,"
                "        ];"
                ""
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ]
        "an inline comment that is not at the start of its source line",
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "    ["
                "        1, /* inline */ 1, 0, // tail"
                "        0, 0, 1,"
                "    ];"
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ],
        lines
            [
                "class C"
                "{"
                "    static byte[] A =>"
                "        ["
                "            1, /* inline */"
                "            1,"
                "            0, // tail"
                "            0,"
                "            0,"
                "            1,"
                "        ];"
                ""
                "#if COND"
                "    void M() { }"
                "#endif"
                "}"
            ]
    ]

let tests =
    testSequenced
    <| testList
        "review regressions"
        [
            test "disabled branch line tails normalize despite an unrelated incomplete member" {
                for eol in [ EndOfLine.Lf; EndOfLine.CrLf; EndOfLine.Cr ] do
                    let settings =
                        { Settings.Default with
                            AutoEndOfLine = false
                            Printer =
                                { PrinterOptions.Default with
                                    EndOfLine = eol
                                }
                        }

                    let clean = incompleteConditionalMember "        return;\n"
                    let dirty = incompleteConditionalMember "        return; \t\t\t\n"
                    let expected = stable clean settings
                    let actual = stable dirty settings

                    Expect.equal
                        actual
                        expected
                        "The valid else branch cannot retain trailing tabs."
            }
            test "disabled branch normalization preserves multiline literal bytes" {
                for literal in
                    [
                        "@\"first \t\nsecond \t\n\""
                        "$@\"first \t\n{1} second \t\n\""
                        "\"\"\"\n        first \t\n        second \t\n        \"\"\""
                    ] do
                    let source =
                        incompleteConditionalMember (
                            "        var value = " + literal + "; \t\n        return; \t\n"
                        )

                    let actual = stable source Settings.Default

                    Expect.stringContains
                        actual
                        literal
                        "Whitespace inside a literal remains its value."

                    Expect.isFalse
                        (actual.Contains("return; \t"))
                        "The following code line is normalized."

                    Expect.isFalse
                        (actual.Contains("; \t\n"))
                        "Whitespace after a literal is still layout."
            }
            test "disabled branches inside ignored source retain line tails" {
                let body = "// csff-ignore-start\n        return; \t\n// csff-ignore-end\n"
                let actual = stable (incompleteConditionalMember body) Settings.Default
                Expect.stringContains actual body "A disabled ignore region stays byte-identical."
            }
            test "disabled namespace templates and unmatched braces normalize line tails" {
                let cases =
                    [
                        "#if S\nnamespace N\n#else\nnamespace $rootnamespace$.Runtime{tail}\n#endif\n{\n    internal static class C { }\n}\n"
                        "#if S\n#else\nusing JClass = System.Type;{tail}\nusing Type = System.Type;{tail}\n#endif\nclass C\n#if S\n{\n#else\n}{tail}\n#endif\n}\n"
                        "#if S\n#else\n    }{tail}\n#endif\n"
                        "#if S\n#else\n    }{tail}\n"
                    ]

                for template in cases do
                    for eol in [ "\n"; "\r\n"; "\r" ] do
                        let source = template.Replace("\n", eol)
                        let clean = source.Replace("{tail}", "")
                        let dirty = source.Replace("{tail}", " \t \t")

                        Expect.equal
                            (stable dirty Settings.Default)
                            (stable clean Settings.Default)
                            "Unreadable siblings cannot preserve nonliteral line tails."

                    for eol in [ "\u0085"; "\u2028"; "\u2029" ] do
                        stable
                            (template.Replace("\n", eol).Replace("{tail}", " \t \t"))
                            Settings.Default
                        |> ignore
            }
            test "independent modifier branches do not waive invalid-template verification" {
                let template =
                    "#if S\nnamespace N\n#else\nnamespace $rootnamespace$.Runtime{tail}\n#endif\n{\n#if S\npublic\n#else\n    internal{tail}\n#endif\nstatic class C { }\n}\n"

                for tail in [ ""; " \t \t" ] do
                    use worker = new Worker()

                    Expect.isNotNull
                        (worker.PrintChecked(
                            "Template.cs",
                            template.Replace("{tail}", tail),
                            Settings.Default
                        ))
                        "Trimming disabled line tails does not authorize an unproven output."
            }
            test "dead and unterminated disabled strings keep their whitespace" {
                for literal in
                    [
                        "@\"first \t\nsecond \t\n\"; \t\n"
                        "@\"first \t\nsecond \t\n"
                        "\"\"\"\n    first \t\n    second \t\n"
                    ] do
                    let source = "#if false\nvar value = " + literal + "#endif\nclass C{}\n"
                    let actual = stable source Settings.Default

                    let content = literal.Replace("; \t\n", ";\n")
                    Expect.stringContains actual content "Disabled token contents remain exact."
            }
            test "dead literals split by directive-shaped lines keep their bytes" {
                for literal in
                    [
                        "\"\"\"\n            first\n            #pragma warning disable\n            second \t\n            \"\"\""
                        "@\"first\n    #pragma warning disable\nsecond \t\n\""
                        "$@\"first\n    #nullable disable\n{1} second \t\n\""
                        "$\"first {\n    #pragma warning disable\n    1 \t\n} second\""
                    ] do
                    for newline in [ "\n"; "\r\n" ] do
                        let source = (deadLiteral literal).Replace("\n", newline)

                        Expect.equal
                            (stable source Settings.Default)
                            source
                            "Whitespace inside a dead literal remains its value."

                let nested =
                    deadLiteral
                        "\"\"\"\n            #if X\n            second \t\n            #endif\n            \"\"\""

                Expect.stringContains
                    (stable nested Settings.Default)
                    "\n            second \t\n"
                    "Whitespace inside a dead literal remains its value."
            }
            test "disabled branch tails after closed literals and directives still normalize" {
                let body tail =
                    "        Write(\"a\");"
                    + tail
                    + "\n        #region r\n        return;"
                    + tail
                    + "\n        #endregion\n"

                let expected = stable (incompleteConditionalMember (body "")) Settings.Default
                let actual = stable (incompleteConditionalMember (body " \t")) Settings.Default
                Expect.equal actual expected "A closed literal does not reach the next item."
            }
            test "disabled line tails converge before every C# line terminator" {
                for newline, tail, directive in
                    [
                        "\r", "", "\r"
                        "\n", "", "\n"
                        "\r\n", "", "\r\n"
                        "\u0085", " \t", "\u0085\n"
                        " ", " \t", " \n"
                        " ", " \t", " \n"
                    ] do
                    let prefix = "class C\n{\n#if false\n    int x; \t" + newline
                    let kept = "class C\n{\n#if false\n    int x;" + tail

                    Expect.equal
                        (stable (prefix + "    int y; \t\n#endif\n}\n") Settings.Default)
                        (kept + newline + "    int y;\n#endif\n}\n")
                        "A later CR or LF line still drops its tail."

                    Expect.equal
                        (stable (prefix + "#endif\n}\n") Settings.Default)
                        (kept + directive + "#endif\n}\n")
                        "The first pass prints what the second keeps."
            }
            test "async partial void formats as CSharpier prints it" {
                Expect.equal
                    (stable
                        "partial class C { public partial void F(); public    async partial void F() { } }\n"
                        Settings.Default)
                    "partial class C\n{\n    public partial void F();\n\n    public async partial void F() { }\n}\n"
                    "maui AlertManager.Tizen.cs, minimised."
            }
            test "deep pointer argument decisions preserve every written expression" {
                let shapes =
                    [
                        "B*"
                        "B**"
                        "G<B>*"
                        "G<int>*"
                        "G<int>**"
                        "G<B*>"
                        "G<int*>"
                        "G<G<int>>*"
                        "G<G<B>>*"
                        "G<G<int>*>*"
                        "G<G<B>*>*"
                        "G<int>.H<B>*"
                        "G<int>.H<int>*"
                        "G<G<int>.H<B>>*"
                        "G<G<int>.H<B>,int>*"
                        "G<G<G<int>>>*"
                        "G<G<G<B>>>*"
                        "N.G<int>.H<B>*"
                        "(int,B)*"
                        "G<(int,B)>*"
                        "G<B[]>*"
                        "G<B?>*"
                    ]

                use worker = new Worker()
                let mutable checkedCount = 0
                let mutable written = 0

                for shape in shapes do
                    for closing in [ "> + b"; "> * b"; ">>=1"; ">>>=1" ] do
                        let expression = "A<" + shape + closing

                        for body in
                            [
                                expression + ";"
                                "var v = " + expression + ";"
                                "var v = new X { " + expression + " };"
                            ] do
                            let source = $"class C {{ unsafe void M(int b) {{ {body} }} }}"

                            let refusal =
                                try
                                    worker.PrintChecked("pointer.cs", source, Settings.Default)
                                with :? InvalidOperationException as error when
                                    error.Message.StartsWith(
                                        "Incomplete C# syntax",
                                        StringComparison.Ordinal
                                    ) ->
                                    error.Message

                            checkedCount <- checkedCount + 1

                            if isNull refusal then
                                written <- written + 1
                                let output = worker.OutputText.ToString()
                                let outcome = Csff.Gate.Adjudicator.adjudicate source output 8

                                Expect.isEmpty
                                    outcome.Findings
                                    $"Independent Roslyn proof: {source}"

                Expect.equal
                    checkedCount
                    264
                    "22 nested shapes, four closing runs, three expression hosts."

                Expect.equal
                    written
                    90
                    "The campaign retains all accepted outputs, including the ten deeper generic expressions."

                printfn
                    "deep pointer argument campaign: %d checked, %d accepted"
                    checkedCount
                    written
            }
            test "a query statement stays on one line where it fits, as CSharpier prints it" {
                Expect.equal
                    (stable
                        "class C { void M() {   from s in \"a\"   select s; } }\n"
                        Settings.Default)
                    "class C\n{\n    void M()\n    {\n        from s in \"a\" select s;\n    }\n}\n"
                    "mono cs0201-7.cs, minimised."

                Expect.equal
                    (stable
                        "class C { void M() { from int x in xs /* c */ select x; from int x in someVeryLongCollectionNameThatGoesOnAndOn where x > 1000000 select x * 2 + someOtherValue; } }\n"
                        Settings.Default)
                    "class C\n{\n    void M()\n    {\n        from int x in xs /* c */\n        select x;\n        from int x in someVeryLongCollectionNameThatGoesOnAndOn\n        where x > 1000000\n        select x * 2 + someOtherValue;\n    }\n}\n"
                    "Broken query statements align their clauses."
            }
            test "conditional blank lines do not depend on the output line ending" {
                for source in
                    [
                        "#if A\n\nclass C{}\n#else\n\nclass D{}\n#endif\n"
                        "#if A\nnamespace N{\n#if B\n\nclass C{}\n#else\n\nclass D{}\n#endif\n}\n#endif\n"
                        "#if A || B\nclass C { void M(){\n#if A\nF();\n#endif\n\nG();\n}}\n#endif\n"
                        "#if OUTER\n#if A\n\nclass C{int x=;}\n#else\n\nclass D{int y=;}\n#endif\n#endif\n"
                    ] do
                    let expected = stable source Settings.Default

                    for inputEnding in [ "\n"; "\r\n"; "\r" ] do
                        for outputEnding in [ EndOfLine.Lf; EndOfLine.CrLf; EndOfLine.Cr ] do
                            let settings =
                                {
                                    Printer =
                                        { PrinterOptions.Default with
                                            EndOfLine = outputEnding
                                        }
                                    AutoEndOfLine = false
                                }

                            let actual = stable (source.Replace("\n", inputEnding)) settings

                            Expect.equal
                                (actual.Replace("\r\n", "\n").Replace("\r", "\n"))
                                expected
                                "Conditional passes retain the same physical blank lines for every EOL pair."
            }
            test
                "a namespace's attribute lists print one to a line above it, as CSharpier prints them" {
                Expect.equal
                    (stable
                        "using System;\n\n[A(11)]   [B]\nnamespace   N\n{\nclass C { }\n}\n"
                        Settings.Default)
                    "using System;\n\n[A(11)]\n[B]\nnamespace N\n{\n    class C { }\n}\n"
                    "mono cs1671.cs, minimised."

                for source, expected in
                    [
                        "[A][B] namespace N { using Z; using System; class C { } }\n",
                        "[A]\n[B]\nnamespace N\n{\n    using System;\n    using Z;\n\n    class C { }\n}\n"
                        "[A][B] namespace N; using Z; using System; class C { }\n",
                        "[A]\n[B]\nnamespace N;\n\nusing System;\nusing Z;\n\nclass C { }\n"
                    ] do
                    Expect.equal
                        (stable source Settings.Default)
                        expected
                        "The sorted usings are proven."
            }
            test "documented modifier runs remain provable when comment layout changes" {
                for documentation in
                    [
                        "/// <summary>Loads an array.</summary> \n"
                        "/// <summary> \n  /// Loads an array.\n /// </summary>\n"
                        "/** <summary>\n  Loads an array. \n </summary> */\n"
                    ] do
                    for prefix, suffix in
                        [
                            "", ""
                            "#if HAVE_ASYNC\n", "#endif\n"
                            "#define HAVE_ASYNC\n#if HAVE_ASYNC\n", "#endif\n"
                        ] do
                        for eol in [ "\n"; "\r\n" ] do
                            let source =
                                (prefix
                                 + "class C\n{\nstatic public async Task WriteAsync() { }\n"
                                 + documentation
                                 + "public new static async Task<C> LoadAsync() { return null; }\n}\n"
                                 + suffix)
                                    .Replace("\n", eol)

                            let output = stable source Settings.Default

                            Expect.stringContains
                                output
                                "public static new async Task<C> LoadAsync()"
                                "Documented modifier runs are sorted and proven across conditional passes."

                            Expect.stringContains
                                output
                                "public static async Task WriteAsync()"
                                "Undocumented modifier runs are still sorted."

                            Expect.stringContains
                                output
                                "Loads an array."
                                "The documentation content survives."
            }
            test "an empty format specifier formats as CSharpier prints it" {
                Expect.equal
                    (stable
                        "class C { void M() { int v = 0; var s =   $\"{v:}\"; } }\n"
                        Settings.Default)
                    "class C\n{\n    void M()\n    {\n        int v = 0;\n        var s = $\"{v:}\";\n    }\n}\n"
                    "mono cs8089.cs, minimised."
            }
            test "modifier sorting preserves documentation with mixed line endings" {
                for commentEnding in [ "\n"; "\r\n"; "\r" ] do
                    for documentation in
                        [
                            [ "    /// </summary>" ]
                            [ "    /// <summary>"; "  /// text"; "    /// </summary>" ]
                        ] do
                        let source =
                            "class C : B\r\n{\r\n"
                            + String.concat commentEnding documentation
                            + commentEnding
                            + "  new public virtual int Options => 1;\r\n}\r\n"

                        let expected =
                            "class C : B\r\n{\r\n"
                            + (documentation
                               |> List.map (fun line -> "    " + line.TrimStart())
                               |> String.concat "\r\n")
                            + "\r\n    public new virtual int Options => 1;\r\n}\r\n"

                        Expect.equal
                            (stable source Settings.Default)
                            expected
                            "The comment keeps its content and declaration while its layout changes."
            }
            test "a field of type partial formats as CSharpier prints it" {
                Expect.equal
                    (stable "class C {   partial field; }\n" Settings.Default)
                    "class C\n{\n    partial field;\n}\n"
                    "mono test-partial-30.cs, minimised."
            }
            test "partial worker startup joins every successfully started thread" {
                for failAt in [ 1; 3 ] do
                    use release = new ManualResetEventSlim(false)
                    let mutable starts = 0
                    let mutable finished = 0
                    let failure = OutOfMemoryException "simulated thread startup failure"
                    let mutable caught: exn = null

                    let startThread (thread: Thread) =
                        starts <- starts + 1

                        if starts = failAt then
                            release.Set()
                            raise failure

                        thread.Start()

                    try
                        Worker.Parallel(
                            4,
                            CancellationToken.None,
                            (fun () ->
                                release.Wait()
                                Interlocked.Increment(&finished) |> ignore),
                            startThread = startThread
                        )
                    with error ->
                        caught <- error

                    Expect.isTrue
                        (obj.ReferenceEquals(caught, failure))
                        "The startup error survives."

                    Expect.equal
                        finished
                        (failAt - 1)
                        "All running workers finish before the error escapes."
            }
            test "a top-level tuple delegate formats as CSharpier prints it" {
                Expect.equal
                    (stable
                        "delegate (int     a,        int b) Del((int a, int b) d);\n"
                        Settings.Default)
                    "delegate (int a, int b) Del((int a, int b) d);\n"
                    "mono test-tuple-05.cs, minimised."
            }
            test
                "one configuration's lexical proof does not stand for a configuration that reads past a disabled run" {
                let verifier = SyntaxPreservation.Checker()
                let tokens = TokenPreservation.Checker()

                let refused label (source: string) (formatted: string) =
                    Expect.isFalse
                        (tokens.LexicallyPreserved(source, formatted))
                        $"{label}: the lexical proof declines."

                    match
                        verifier.Decide(PrinterOptions.Default, "Swallowed.cs", source, formatted)
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest $"{label} must not be proven."
                    | _ -> ()

                refused
                    "directive lines inside a raw string another configuration reads"
                    "#if DEBUG\nclass C\n{\n    void M()\n    {\n        var test = \"\"\"\n            #if X\n #else\n            #endif\n            \"\"\";\n        {\n        };\n    }\n}\n#endif\n"
                    "#if DEBUG\nclass C\n{\n    void M()\n    {\n        var test = \"\"\"\n#if X\n#else\n#endif\n            \"\"\";\n        {\n        };\n    }\n}\n#endif\n"

                refused
                    "code inside a verbatim string another configuration reads"
                    "#if DEBUG\nvar s = @\"\n#endif\nclass   D { }\n#if DEBUG\n\";\n#endif\n"
                    "#if DEBUG\nvar s = @\"\n#endif\nclass D { }\n#if DEBUG\n\";\n#endif\n"

                refused
                    "an opener after a string holding //"
                    "#if DEBUG\nvar u = \"http://x\"; var s = @\"\n#endif\nclass   D { }\n#if DEBUG\n\";\n#endif\n"
                    "#if DEBUG\nvar u = \"http://x\"; var s = @\"\n#endif\nclass D { }\n#if DEBUG\n\";\n#endif\n"

                refused
                    "code inside a block comment another configuration reads"
                    "#if DEBUG\n/*\n#endif\nclass   D { }\n#if DEBUG\n*/\n#endif\n"
                    "#if DEBUG\n/*\n#endif\nclass D { }\n#if DEBUG\n*/\n#endif\n"

                Expect.isTrue
                    (tokens.LexicallyPreserved(
                        "#if DEBUG\nclass C { string s = \"a // b @\"; char q = '\"'; char a = '\\''; } // it's \"quoted\"\n#endif\nclass   D { }\n",
                        "#if DEBUG\nclass C { string s = \"a // b @\"; char q = '\"'; char a = '\\''; } // it's \"quoted\"\n#endif\nclass D { }\n"
                    ))
                    "Plain disabled code is still settled by the lexical proof."

                Expect.equal
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "Plain.cs",
                        "#if DEBUG\nclass C { string s = \"a // b @\"; char q = '\"'; char a = '\\''; } // it's \"quoted\"\n#endif\nclass   D { }\n",
                        "#if DEBUG\nclass C { string s = \"a // b @\"; char q = '\"'; char a = '\\''; } // it's \"quoted\"\n#endif\nclass D { }\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "And proven."
            }
            test "a configuration that is not C# is proven only by its own tokens" {
                let verifier = SyntaxPreservation.Checker()

                let decide (source: string) (formatted: string) =
                    verifier.Decide(PrinterOptions.Default, "Recovered.cs", source, formatted)

                let refused label verdict =
                    match verdict with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest $"{label} must not be proven."
                    | _ -> ()

                let source =
                    "class C\n{\n    void M()\n    {\n#if MDA\n        catch\n#endif\n    }\n#if FEATURE\n    static extern void N();   \n#endif\n}\n"

                Expect.equal
                    (decide
                        source
                        "class C\n{\n    void M()\n    {\n#if MDA\n        catch\n#endif\n    }\n#if FEATURE\n    static extern void N();\n#endif\n}\n")
                    SyntaxPreservation.Verification.Proven
                    "Only whitespace moved: the same tokens, and the same recovery from them."

                refused
                    "A token changed where the parse recovered"
                    (decide
                        source
                        "class C\n{\n    void M()\n    {\n#if MDA\n        finally\n#endif\n    }\n#if FEATURE\n    static extern void N();\n#endif\n}\n")

                refused
                    "Modifiers sorted where the parse recovered"
                    (decide
                        "class C\n{\n    static internal void M()\n    {\n#if MDA\n        catch\n#endif\n    }\n#if FEATURE\n    static extern void N();   \n#endif\n}\n"
                        "class C\n{\n    internal static void M()\n    {\n#if MDA\n        catch\n#endif\n    }\n#if FEATURE\n    static extern void N();\n#endif\n}\n")

                refused
                    "Two touching closers split where the parse recovered"
                    (decide
                        "using System.Text;\nusing System;\n#if NEVER\nvoid M() {\n#endif\nclass C\n{\n    System.Collections.Generic.Dictionary<string, System.Collections.Generic.List<System.Collections.Generic.KeyValuePair<string, int>>> field;\n    int  y;\n}\n"
                        "using System.Text;\nusing System;\n#if NEVER\nvoid M() {\n#endif\nclass C\n{\n    System.Collections.Generic.Dictionary<\n        string,\n        System.Collections.Generic.List<System.Collections.Generic.KeyValuePair<string, int>>\n    > field;\n    int y;\n}\n")

                refused
                    "A bad token where the parse recovered"
                    (decide
                        "class C\n{\n    void M()\n    {\n#if MDA\n        `\n#endif\n    }\n#if FEATURE\n    static extern void N();   \n#endif\n}\n"
                        "class C\n{\n    void M()\n    {\n#if MDA\n        `\n#endif\n    }\n#if FEATURE\n    static extern void N();\n#endif\n}\n")
            }
            test "raw literal member access preserves newlines in force-flat layouts" {
                for prefix in [ ""; "$" ] do
                    for ending in [ ".Length"; ".Trim().Length" ] do
                        let content = if prefix = "" then "hello  " else "hello {1}  "

                        let literal =
                            prefix
                            + "\"\"\"\n              "
                            + content
                            + "\n\n              world\n            \"\"\""
                            + ending

                        for source in
                            [
                                "class C { void M() { var x = " + literal + "; } }"
                                "class C { int P { get; } = " + literal + "; }"
                            ] do
                            for eol in [ "\n"; "\r\n"; "\r" ] do
                                let source = source.Replace("\n", eol)
                                let output = stable source Settings.Default

                                Expect.isTrue
                                    (output.Contains(content + eol, StringComparison.Ordinal))
                                    "Literal newlines and trailing spaces survive assignment layouts."
            }
            test "directives outside the if family keep their csff-ignore layout" {
                let lines (items: string list) = String.concat "\n" items + "\n"

                let ranged =
                    [
                        "class C"
                        "{"
                        "    // csff-ignore-start"
                        "    /** <summary>kept</summary> */"
                        "    #region Inner"
                        "    void   M( )   {   }"
                        "    #endregion"
                        "    // csff-ignore-end"
                    ]

                Expect.equal
                    (stable (lines (ranged @ [ "    void   N( )   {   }"; "}" ])) Settings.Default)
                    (lines (ranged @ [ "    void N() { }"; "}" ]))
                    "An ignore range spanning a region keeps its own text."

                let singled =
                    [
                        "class C"
                        "{"
                        "    #region One"
                        "    // csff-ignore"
                        "    void   M( int a,int b )   {   }"
                    ]

                let closing =
                    [
                        "    #endregion"
                        "    #region Two"
                        "    void P(int a, int b) { }"
                        "    #endregion"
                        "}"
                    ]

                Expect.equal
                    (stable
                        (lines (
                            singled
                            @ [ "    void   N( int a,int b )   {   }" ]
                            @ [
                                "    #endregion"
                                "    #region Two"
                                "    void   P( int a,int b )   {   }"
                                "    #endregion"
                                "}"
                            ]
                        ))
                        Settings.Default)
                    (lines (singled @ [ ""; "    void N(int a, int b) { }" ] @ closing))
                    "A single ignore inside a region keeps its member and its separator."

                let conditional body =
                    lines (
                        [ "class C"; "{"; "    void A() { }" ]
                        @ [ "#if FOO" ]
                        @ body
                        @ [ "#endif"; "    void B() { }"; "}" ]
                    )

                Expect.equal
                    (stable (conditional []) Settings.Default)
                    (conditional [])
                    "An empty conditional prefix adds no blank line."

                Expect.equal
                    (stable (conditional [ "    void X() { }" ]) Settings.Default)
                    (lines
                        [
                            "class C"
                            "{"
                            "    void A() { }"
                            ""
                            "#if FOO"
                            "    void X() { }"
                            "#endif"
                            ""
                            "    void B() { }"
                            "}"
                        ])
                    "A conditional prefix holding a member separates both neighbours."
            }
            test "retiring large workers preserves queued commits and following small files" {
                let large = "class Large{\n" + String.replicate 100_000 "int a;\n" + "}\n"
                let expectedLarge = stable large Settings.Default
                let small = "class Small{string Text=>\"kept\";}\n"
                let expectedSmall = stable small Settings.Default

                for jobs in [ 1; 24 ] do
                    withDirectory (fun root ->
                        let files =
                            Array.init 40 (fun index ->
                                let path = Path.Combine(root, $"{index:D2}.cs")
                                File.WriteAllText(path, if index < 4 then large else small)

                                {
                                    Path = path
                                    Settings = Settings.Default
                                    Root = 0
                                })

                        let run check =
                            Formatter.run
                                [| root |]
                                files
                                check
                                true
                                false
                                jobs
                                None
                                CancellationToken.None

                        let checkedFiles = run true

                        for result in checkedFiles do
                            Expect.isNull result.Error "All inputs can be formatted."
                            Expect.isNull result.Unverified "All formatting is proven."
                            Expect.isTrue result.Changed "Check mode sees each required edit."

                        for index = 0 to files.Length - 1 do
                            Expect.equal
                                (File.ReadAllText files[index].Path)
                                (if index < 4 then large else small)
                                "Check mode writes nothing."

                        let written = run false

                        for index = 0 to files.Length - 1 do
                            Expect.isNull written[index].Error "Retirement does not break commits."

                            Expect.isNull
                                written[index].Unverified
                                "The committed result is proven."

                            Expect.equal
                                (File.ReadAllText files[index].Path)
                                (if index < 4 then expectedLarge else expectedSmall)
                                "Queued output owns its bytes after retirement."

                        for result in run true do
                            Expect.isNull result.Error "Replacement workers start clean."
                            Expect.isNull result.Unverified "The second pass is proven."
                            Expect.isFalse result.Changed "All files are at a fixed point.")
            }
            test "explicit worker retirement returns each owned buffer once" {
                let owned = HashSet<byte array>(HashIdentity.Reference)

                let pool =
                    { new ArrayPool<byte>() with
                        override _.Rent length =
                            let buffer = Array.zeroCreate<byte> length
                            owned.Add buffer |> ignore
                            buffer

                        override _.Return(buffer, _) =
                            Expect.isTrue
                                (owned.Remove buffer)
                                "A retired buffer is returned only once."
                    }

                let worker = new Worker(buffers = pool)
                Expect.equal owned.Count 3 "The worker owns its three I/O buffers."
                worker.ReleaseBuffers()
                Expect.equal owned.Count 0 "Retirement releases every owned buffer."
                worker.ReleaseBuffers()
                (worker :> IDisposable).Dispose()
                Expect.equal owned.Count 0 "Lifetime cleanup after retirement is harmless."
            }
            test "failed buffer growth retains ownership for reuse and disposal" {
                for failDuringInput in [ true; false ] do
                    withDirectory (fun root ->
                        let owned = HashSet<byte array>(HashIdentity.Reference)

                        let pool =
                            { new ArrayPool<byte>() with
                                override _.Rent length =
                                    if length > 64 * 1024 then
                                        raise (OutOfMemoryException "simulated rent failure")

                                    let buffer = Array.zeroCreate<byte> length
                                    owned.Add buffer |> ignore
                                    buffer

                                override _.Return(buffer, _) =
                                    Expect.isTrue
                                        (owned.Remove buffer)
                                        "Each returned buffer is still owned, and returned once."
                            }

                        let path = Path.Combine(root, "Input.cs")

                        let file =
                            {
                                Path = path
                                Settings = Settings.Default
                                Root = 0
                            }

                        do
                            use worker = new Worker(buffers = pool)

                            let source =
                                if failDuringInput then
                                    String(' ', 70_000) + "class C{}"
                                else
                                    "class C{" + String.replicate 6000 "int a;" + "}"

                            File.WriteAllText(path, source)
                            let failed = worker.Format(file, null, false, false)

                            Expect.stringContains
                                failed.Error
                                "simulated rent failure"
                                "Growth fails."

                            Expect.equal owned.Count 3 "Every original buffer remains owned."

                            Expect.equal
                                (File.ReadAllText path)
                                source
                                "Failed formatting writes nothing."

                            File.WriteAllText(path, "class C{int a;}")
                            let succeeded = worker.Format(file, null, false, false)

                            Expect.isNull
                                succeeded.Error
                                "The same worker can format another file."

                            Expect.isTrue succeeded.Changed "The succeeding file is formatted."

                        Expect.equal owned.Count 0 "Disposal returns all still-owned buffers.")
            }
            test
                "a prefetch ring never waits on a position nobody will take once the run is cancelled or abandoned" {
                use worker = new Worker()
                use cancellation = new CancellationTokenSource()
                let cancelled = PrefetchRing(2, ArrayPool<byte>.Shared)

                let take = Tasks.Task.Run(fun () -> cancelled.Take(2, worker, cancellation.Token))

                Expect.isFalse
                    (take.Wait(TimeSpan.FromMilliseconds 200.0))
                    "Take waits while the older position may still be taken."

                cancellation.Cancel()

                Expect.isTrue
                    (take.Wait(TimeSpan.FromSeconds 5.0))
                    "A cancelled run's Take stops waiting for the older position."

                let abandoned = PrefetchRing(2, ArrayPool<byte>.Shared)

                let abandonedTake =
                    Tasks.Task.Run(fun () -> abandoned.Take(2, worker, CancellationToken.None))

                let abandonedRead = Tasks.Task.Run(fun () -> abandoned.TryBeginRead 2)

                Expect.isFalse
                    (abandonedTake.Wait(TimeSpan.FromMilliseconds 200.0))
                    "Take waits while the ring is live."

                abandoned.Abandon()

                Expect.isTrue
                    (abandonedTake.Wait(TimeSpan.FromSeconds 5.0))
                    "An abandoned ring's Take stops waiting."

                Expect.isTrue
                    (abandonedRead.Wait(TimeSpan.FromSeconds 5.0))
                    "An abandoned ring's reader stops waiting."

                Expect.equal abandonedRead.Result -1 "An abandoned ring gives a reader no slot."
            }
            test "a prefetched read that outgrew its slot leaves the file to its worker" {
                let returned = ResizeArray<byte array>()

                let pool =
                    { new ArrayPool<byte>() with
                        override _.Rent length = Array.zeroCreate<byte> length

                        override _.Return(buffer, _) =
                            lock returned (fun () -> returned.Add buffer)
                    }

                let ring = PrefetchRing(2, pool)
                let slot = ring.TryBeginRead 0
                Expect.equal slot 0 "Position 0 is free for a reader."

                let outgrown = Array.zeroCreate<byte>(CommitSlot.MaxBytes * 2)
                ring.Buffers[slot] <- outgrown
                ring.PublishRead(slot, 0, outgrown.Length, false, null)

                Expect.equal ring.Buffers[slot].Length 0 "The slot keeps no outgrown buffer."

                Expect.isTrue
                    (lock returned (fun () ->
                        returned |> Seq.exists (fun b -> obj.ReferenceEquals(b, outgrown))))
                    "The outgrown buffer goes back to the pool."

                use worker = new Worker(buffers = pool)
                ring.Take(0, worker, CancellationToken.None)

                Expect.equal
                    ring.Buffers[slot].Length
                    0
                    "The worker adopts nothing for the file it reads itself, so no buffer is swapped in."
            }
            test "a cancelled direct run formats none of the large files it deferred" {
                withDirectory (fun root ->
                    use giantStarted = new ManualResetEventSlim(false)
                    use release = new ManualResetEventSlim(false)
                    use cancellation = new CancellationTokenSource()
                    use rents = new ThreadLocal<int>()
                    let blocked = ref 0

                    let pool =
                        { new ArrayPool<byte>() with
                            override _.Rent length =
                                if length = 64 * 1024 then
                                    let count = rents.Value + 1
                                    rents.Value <- count

                                    if
                                        count = 4 && Interlocked.Exchange(&blocked.contents, 1) = 0
                                    then
                                        giantStarted.Set()
                                        release.Wait(TimeSpan.FromSeconds 10.0) |> ignore

                                Array.zeroCreate<byte> length

                            override _.Return(_, _) = ()
                        }

                    let source = "class C{}" + String(' ', 600000) + "\n"
                    let lengths = Array.zeroCreate<int64> 31

                    let files =
                        Array.init 31 (fun i ->
                            let path = Path.Combine(root, $"Large{i:D2}.cs")
                            File.WriteAllText(path, source)
                            lengths[i] <- FileInfo(path).Length

                            {
                                Path = path
                                Settings = Settings.Default
                                Root = 0
                            })

                    let runTask =
                        Tasks.Task.Run(fun () ->
                            Formatter.runWithLengthsAndOptions
                                [| root |]
                                files
                                lengths
                                false
                                true
                                false
                                2
                                None
                                pool
                                (ValueSome 1)
                                cancellation.Token)

                    Expect.isTrue
                        (giantStarted.Wait(TimeSpan.FromSeconds 10.0))
                        "The first large file reaches its giant worker."

                    Thread.Sleep 300
                    cancellation.Cancel()
                    release.Set()

                    let finished =
                        try
                            runTask.Wait(TimeSpan.FromSeconds 20.0)
                        with :? AggregateException ->
                            true

                    Expect.isTrue finished "The cancelled run returns."

                    let written =
                        files |> Array.filter (fun file -> File.ReadAllText file.Path <> source)

                    Expect.isLessThanOrEqual
                        written.Length
                        1
                        "Only the large file already in its giant worker is formatted after the cancellation.")
            }
            test "giant worker allocation failure releases the large-file gate permit" {
                for check in [ true; false ] do
                    withDirectory (fun root ->
                        let ownedGate = obj ()
                        let owned = HashSet<byte array>(HashIdentity.Reference)
                        use thread64kRents = new ThreadLocal<int>()
                        use workersReady = new Barrier(2)

                        let pool =
                            { new ArrayPool<byte>() with
                                override _.Rent length =
                                    if length = 64 * 1024 then
                                        let count = thread64kRents.Value + 1
                                        thread64kRents.Value <- count

                                        if count = 3 then
                                            workersReady.SignalAndWait(TimeSpan.FromSeconds 5.0)
                                            |> ignore
                                        elif count = 5 then
                                            Thread.Sleep 25

                                            raise (
                                                OutOfMemoryException
                                                    "simulated giant worker rent failure"
                                            )

                                    let buffer = Array.zeroCreate<byte> length
                                    lock ownedGate (fun () -> owned.Add buffer |> ignore)
                                    buffer

                                override _.Return(buffer, _) =
                                    lock ownedGate (fun () ->
                                        Expect.isTrue
                                            (owned.Remove buffer)
                                            "Each rented buffer is still owned, and returned once.")
                            }

                        let fileCount = if check then 2 else 32
                        let giantCount = if check then 2 else 30
                        let lengths = Array.zeroCreate<int64> fileCount

                        let files =
                            Array.init fileCount (fun i ->
                                let path = Path.Combine(root, $"File{i:D2}.cs")

                                if i < giantCount then
                                    use stream = File.Create path
                                    stream.SetLength(512L * 1024L)
                                    lengths[i] <- 512L * 1024L
                                else
                                    let small = "class C{}"
                                    File.WriteAllText(path, small)
                                    lengths[i] <- int64 small.Length

                                {
                                    Path = path
                                    Settings = Settings.Default
                                    Root = 0
                                })

                        let runTask =
                            Tasks.Task.Run(fun () ->
                                Formatter.runWithLengthsAndOptions
                                    [| root |]
                                    files
                                    lengths
                                    check
                                    true
                                    false
                                    2
                                    None
                                    pool
                                    (ValueSome 1)
                                    CancellationToken.None)

                        let finished =
                            try
                                runTask.Wait(TimeSpan.FromSeconds 10.0)
                            with :? AggregateException ->
                                true

                        Expect.isTrue
                            finished
                            "Giant worker constructor failure releases the gate instead of hanging."

                        let raised =
                            try
                                runTask.GetAwaiter().GetResult() |> ignore
                                null
                            with :? OutOfMemoryException as error ->
                                error

                        Expect.isNotNull
                            raised
                            "The simulated OutOfMemoryException surfaces from the parallel run."

                        Expect.stringContains
                            raised.Message
                            "simulated giant worker rent failure"
                            "The giant worker rent failure is reported."

                        Expect.equal
                            (lock ownedGate (fun () -> owned.Count))
                            0
                            "Every worker, shard, and partial giant-worker buffer is returned.")
            }
            test "files beyond the array limit are rejected before renting" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "TooLarge.cs")

                    do
                        use stream = File.Create path
                        stream.SetLength(int64 Array.MaxLength + 1L)

                    let pool =
                        { new ArrayPool<byte>() with
                            override _.Rent length =
                                Expect.isLessThanOrEqual
                                    length
                                    (64 * 1024)
                                    "Only initial buffers are rented."

                                Array.zeroCreate<byte> length

                            override _.Return(_, _) = ()
                        }

                    use worker = new Worker(buffers = pool)

                    let result =
                        worker.Format(
                            {
                                Path = path
                                Settings = Settings.Default
                                Root = 0
                            },
                            null,
                            false,
                            false
                        )

                    Expect.stringContains
                        result.Error
                        "buffer limit"
                        "An oversized file has a bounded failure.")
            }
            test "ignored global usings keep compilable order" {
                for marker in [ "// csff-ignore"; "// csff-ignore-start" ] do
                    let ending =
                        if marker.EndsWith("start", StringComparison.Ordinal) then
                            "// csff-ignore-end\n"
                        else
                            ""

                    let source =
                        marker
                        + "\nglobal using System;\n"
                        + ending
                        + "using System.Collections;\nclass C{}"

                    Expect.isEmpty (compilationErrors source) "The regression input compiles."
                    let output = stable source Settings.Default

                    Expect.isEmpty
                        (compilationErrors output)
                        "Using ordering must preserve compilation."

                    Expect.isLessThan
                        (output.IndexOf("global using", StringComparison.Ordinal))
                        (output.IndexOf("using System.Collections", StringComparison.Ordinal))
                        "Global usings precede ordinary ones."

                    withDirectory (fun root ->
                        let path = Path.Combine(root, "Input.cs")
                        File.WriteAllText(path, source)
                        let code, _, errors = invoke [| "--no-cache"; path |]
                        Expect.equal code 0 errors

                        Expect.equal
                            (File.ReadAllText path)
                            output
                            "The write path publishes the safe output.")
            }
            test "malformed interpolation is rejected without overlapping tokens" {
                for literal in
                    [
                        "$$\"\"\"{{x}\"\"\""
                        "$$\"\"\"{{x:X}\"\"\""
                        "$$\"{1+2}\""
                        "$$@\"{1+2}\""
                        "@@$\"{1+2}\""
                    ] do
                    let source = "class C { string M() => " + literal + "; }"
                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse source tree

                    for index in 1 .. tree.TokenCount - 1 do
                        let previous = tree.Token(index - 1)

                        Expect.isLessThanOrEqual
                            previous.End
                            (tree.Token index).Start
                            "Parser tokens must not overlap, including malformed closers."

                    withDirectory (fun root ->
                        let path = Path.Combine(root, "Input.cs")
                        File.WriteAllText(path, source)
                        let code, output, _ = invoke [| "--write-stdout"; path |]
                        Expect.equal code 2 "Stdout rejects malformed interpolation."
                        Expect.equal output "" "Invalid text is never published."
                        let code, _, _ = invoke [| "--no-cache"; path |]
                        Expect.equal code 1 "Writing rejects malformed interpolation."
                        Expect.equal (File.ReadAllText path) source "The original text survives.")
            }
            test "force-flat line comments retain following syntax" {
                let sources =
                    [
                        "class C { void M() { var x = a. // c\nb; } }"
                        "class C { void M() { var x = a.\n// c\nb; } }"
                        "class C { int M() { return a = b = Foo( // c\n1); } }"
                        "class C { void M() { o.Foo< // c\nint>(); } }"
                        "class C { void M() { List< // c\nint> x = Foo(); } }"
                        "class C<[A] // c\nT> { }"
                        "class C { void M() { var x = stackalloc int[ // c\n2]; } }"
                        "class C { void M() { var x = new Foo( // c\n); } }"
                    ]

                for source in sources do
                    for width in [ 30; 100 ] do
                        let settings =
                            { Settings.Default with
                                Printer =
                                    { PrinterOptions.Default with
                                        Width = width
                                    }
                            }

                        let output = stable source settings

                        Expect.isEmpty
                            (CSharpSyntaxTree.ParseText(output).GetDiagnostics()
                             |> Seq.filter (fun d -> d.Severity = DiagnosticSeverity.Error)
                             |> Seq.toArray)
                            "Line comments must not swallow tokens."
            }
            test "conditional patterns and expression precedence conform to Roslyn" {
                for source in
                    [
                        "class C { void M(int x) { switch (x) { case true ? 1 : 2: break; } } }"
                        "class C { bool M(object x) => x is [true ? 1 : 2]; }"
                        "class C { bool M(object x) => x is { P: true ? 1 : 2 }; }"
                        "class C { int M(int x) => x switch { (true ? 1 : 2) => 3, _ => 0 }; }"
                        "class C { object M() => a..b switch { _ => 1 }; }"
                        "class C { object M() => a..b with { }; }"
                        "class C { object M() => ..b switch { _ => 1 }; }"
                        "class C { object M() => a.. switch { _ => 1 }; }"
                        "class C { object M() => -a switch { _ => 1 }; }"
                        "class C { object M() => a + b switch { _ => 1 }; }"
                        "class C { int P { get { return field; } } = field; }"
                        "class C { int P => field; int Q { get; } = field; }"
                        "class C { int M(object x) => x switch { a[0] => 0, _ => 1 }; }"
                        "class C { int M(object x) => x switch { a[1+2] => 0, _ => 1 }; }"
                        "class C { bool M(object x) => x is a[0]; }"
                        "class C { bool M(object x) => x is A && x is [1, 2]; }"
                        "class C { bool M(object x) => x is T?[]; }"
                    ] do
                    let tree = Csff.Parser.SyntaxTree()

                    Expect.equal
                        (NodeOracle.check "test.cs" source tree)
                        (Ok())
                        "CST nodes and token spans match the independent parser."

                    stable source Settings.Default |> ignore
            }
            test "raw interpolation uses all CSharp whitespace and line separators" {
                let sources =
                    [
                        for whitespace in [ '\v'; '\f'; '\u00a0'; '\u3000' ] do
                            yield
                                "class C { string M() => $$\"\"\""
                                + string whitespace
                                + "\n  {{1+2}}\n  \"\"\"; }"
                        for newline in [ "\r"; "\n"; "\r\n"; "\u0085"; "\u2028"; "\u2029" ] do
                            yield
                                "class C { string M() => $$\"\"\""
                                + newline
                                + "  {{1+2}}"
                                + newline
                                + "  \"\"\"; }"
                    ]

                for source in sources do
                    let tree = Csff.Parser.SyntaxTree()

                    Expect.equal
                        (NodeOracle.check "test.cs" source tree)
                        (Ok())
                        "Raw string delimiter/text spans match Roslyn."

                    stable source Settings.Default |> ignore
            }
            test "a blank line after a region directive leaves the closing brace its own indent" {
                for source, expected in
                    [
                        "class C\n{\n    #region R\n\n    int A;\n\n    #endregion\nBLANK}\n",
                        "class C\n{\n    #region R\n\n    int A;\n\n    #endregion\n}\n"
                        "class C\n{\n    void M()\n    {\n        #region R\n\n        A();\n\n        #endregion\nBLANK    }\n}\n",
                        "class C\n{\n    void M()\n    {\n        #region R\n\n        A();\n\n        #endregion\n    }\n}\n"
                        "class C\n{\n    int A;\n\n    #region R\nBLANK}\n",
                        "class C\n{\n    int A;\n\n    #region R\n}\n"
                    ] do
                    for blank in [ ""; "\n"; "\n\n" ] do
                        Expect.equal
                            (stable (source.Replace("BLANK", blank)) Settings.Default)
                            expected
                            "A blank line before the closing brace cannot move it."
            }
            test "indexed constant patterns continue through following operators" {
                for expression in [ "a[0] + 1"; "a[0] ?? 1"; "(a[0] + 1)"; "(a?[0] + 1)" ] do
                    for template in
                        [
                            "class C { void M(int x) { switch (x) { case VALUE: break; } } }"
                            "class C { bool M(object x) => x is [VALUE]; }"
                            "class C { bool M(object x) => x is { P: VALUE }; }"
                            "class C { int M(object x) => x switch { (VALUE) => 1, _ => 0 }; }"
                            "class C { bool M(object x) => x is VALUE; }"
                        ] do
                        let source = template.Replace("VALUE", expression)

                        Expect.isEmpty
                            (CSharpSyntaxTree
                                .ParseText(source, CSharpParseOptions(LanguageVersion.Preview))
                                .GetDiagnostics()
                             |> Seq.filter (fun diagnostic ->
                                 diagnostic.Severity = DiagnosticSeverity.Error)
                             |> Seq.toArray)
                            "The regression input has valid CSharp syntax."

                        let tree = Csff.Parser.SyntaxTree()

                        Expect.equal
                            (NodeOracle.check "test.cs" source tree)
                            (Ok())
                            "An indexed operand with an operator is a constant expression."

                        stable source Settings.Default |> ignore

                for source in
                    [
                        "class C { bool M(object x) => x is not T[] && x is A; }"
                        "class C { bool M(object x) => x is T[0] + 1; }"
                    ] do
                    let tree = Csff.Parser.SyntaxTree()

                    Expect.equal
                        (NodeOracle.check "test.cs" source tree)
                        (Ok())
                        "Operators outside an is pattern retain their precedence."

                    stable source Settings.Default |> ignore
            }
            test "CR raw strings preserve their layout on a second pass" {
                for newline in [ "\n"; "\r\n"; "\r" ] do
                    for prefix, content in [ "\"\"\"", "hello"; "$$\"\"\"", "{{1+2}} hello" ] do
                        let literal = prefix + newline + "  " + content + newline + "  \"\"\""
                        let source = "class C { object P => " + literal + "; }"

                        let settings =
                            {
                                Printer =
                                    { PrinterOptions.Default with
                                        Width = 40
                                        EndOfLine = EndOfLine.Cr
                                    }
                                AutoEndOfLine = false
                            }

                        let output = stable source settings
                        Expect.isFalse (output.Contains('\n')) "The configured line ending is CR."
            }
            test "empty raw interpolation lines are stable across line endings" {
                for newline in [ "\n"; "\r\n"; "\r" ] do
                    for ending, endOfLine in
                        [ "\n", EndOfLine.Lf; "\r\n", EndOfLine.CrLf; "\r", EndOfLine.Cr ] do
                        for content in [ ""; "value {1}   " ] do
                            let source =
                                "class C { string S = $\"\"\""
                                + newline
                                + "    "
                                + content
                                + newline
                                + "    "
                                + newline
                                + "    \"\"\"; }"

                            let settings =
                                {
                                    Printer =
                                        { PrinterOptions.Default with
                                            EndOfLine = endOfLine
                                        }
                                    AutoEndOfLine = false
                                }

                            let output = stable source settings
                            let beforeBlank = if content.Length = 0 then "$\"\"\"" else content

                            Expect.stringContains
                                output
                                (beforeBlank + ending + ending)
                                "Empty lines have no layout spaces; content keeps its trailing spaces."
            }
            test "stdout and writing decode the same legacy source" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "Input.cs")

                    let bytes =
                        Array.concat
                            [
                                Encoding.ASCII.GetBytes("// dash ")
                                [| 0x96uy |]
                                Encoding.ASCII.GetBytes("\nclass C{}\n")
                            ]

                    File.WriteAllBytes(path, bytes)
                    let code, output, errors = invoke [| "--write-stdout"; path |]
                    Expect.equal code 0 errors

                    Expect.stringContains
                        output
                        "// dash –\n"
                        "Legacy bytes are decoded without replacement."

                    Expect.equal (File.ReadAllBytes path) bytes "Stdout preserves source bytes."
                    let code, _, errors = invoke [| "--no-cache"; path |]
                    Expect.equal code 0 errors

                    Expect.equal
                        (SourceEncoding.read path)
                        output
                        "Both paths produce the same characters."

                    Expect.isTrue
                        (Array.contains 0x96uy (File.ReadAllBytes path))
                        "Writing preserves legacy encoding.")
            }
            test "stdout retains BOM decoding and rejects damaged UTF source" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "Input.cs")

                    for encoding in
                        [
                            UTF8Encoding(true, true) :> Encoding
                            UnicodeEncoding(false, true, true)
                            UnicodeEncoding(true, true, true)
                            UTF32Encoding(false, true, true)
                        ] do
                        File.WriteAllText(path, "// café\nclass C{}", encoding)
                        let code, output, errors = invoke [| "--write-stdout"; path |]
                        Expect.equal code 0 errors

                        Expect.stringContains
                            output
                            "// café"
                            "Supported BOMs preserve decoded source."

                    File.WriteAllBytes(path, [| 0xefuy; 0xbbuy; 0xbfuy; 0x96uy |])
                    let code, output, _ = invoke [| "--write-stdout"; path |]

                    Expect.equal
                        (code, output)
                        (2, "")
                        "A damaged BOM-marked UTF file is rejected.")
            }
            test "flow YAML configurations keep JSON compatibility" {
                withDirectory (fun root ->
                    let config = Path.Combine(root, ".csffrc.yaml")

                    for text in
                        [
                            "{ printWidth: 40, indentSize: 2 }"
                            "---\n{ printWidth: 40, indentSize: 2 }"
                            "{\"printWidth\":40,\"indentSize\":2}"
                        ] do
                        File.WriteAllText(config, text)
                        let path = Path.Combine(root, "Input.cs")
                        File.WriteAllText(path, "class C{int x;}")
                        let code, _, errors = invoke [| "--no-cache"; path |]
                        Expect.equal code 0 errors

                        Expect.equal
                            (File.ReadAllText path)
                            "class C\n{\n  int x;\n}\n"
                            "Flow maps and JSON have identical settings.")
            }
            test "EditorConfig CR survives formatting and cache resolution" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "Input.cs")

                    File.WriteAllText(
                        Path.Combine(root, ".editorconfig"),
                        "root=true\n[*.cs]\nend_of_line=cr\n"
                    )

                    File.WriteAllText(path, "class C{int x;}")
                    let code, _, errors = invoke [| path |]
                    Expect.equal code 0 errors

                    Expect.equal
                        (File.ReadAllText path)
                        "class C\r{\r    int x;\r}\r"
                        "CR is emitted explicitly."

                    let code, _, errors = invoke [| "--check"; path |]
                    Expect.equal code 0 errors

                    File.WriteAllText(
                        Path.Combine(root, ".editorconfig"),
                        "root=true\n[*.cs]\nend_of_line=lf\n"
                    )

                    let code, _, errors = invoke [| path |]
                    Expect.equal code 0 errors

                    Expect.equal
                        (File.ReadAllText path)
                        "class C\n{\n    int x;\n}\n"
                        "Changing EOL cannot reuse an incompatible cache key.")

                let settings =
                    { Settings.Default with
                        Printer =
                            { PrinterOptions.Default with
                                EndOfLine = EndOfLine.Cr
                            }
                        AutoEndOfLine = false
                    }

                stable "class C { string S = \"\"\"\n    hello\n    \"\"\"; }" settings
                |> ignore

                Expect.equal
                    (stable "class C\r{int x;}\r" Settings.Default)
                    "class C\r{\r    int x;\r}\r"
                    "Auto detects CR-only input."
            }
            test "unsupported EditorConfig EOL is ignored" {
                withDirectory (fun root ->
                    File.WriteAllText(
                        Path.Combine(root, ".editorconfig"),
                        "root=true\n[*.cs]\nend_of_line=unsupported\n"
                    )

                    let path = Path.Combine(root, "Input.cs")
                    File.WriteAllText(path, "class C{}")
                    let code, _, errors = invoke [| "--no-cache"; path |]
                    Expect.equal code 0 errors

                    Expect.equal
                        (File.ReadAllText path)
                        "class C { }\n"
                        "An unsupported editor value uses the default.")
            }
            test "trailing ignore spaces respect backslash parity" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, ".gitignore")

                    for count in 0..4 do
                        File.WriteAllText(path, "foo" + String('\\', count) + " \n")
                        let rules = Discovery.readIgnore root path
                        let name = "foo" + String('\\', count / 2)
                        let matcher = rules.Rules[0].Pattern

                        Expect.equal
                            (matcher.IsMatch name)
                            (count % 2 = 0)
                            "Only odd backslash runs escape the trailing space."

                        Expect.equal
                            (matcher.IsMatch(name + " "))
                            (count % 2 = 1)
                            "Escaped spaces remain significant.")
            }
            test "the claim order is longest first and the reported order is not" {
                withDirectory (fun root ->
                    let names = [| "a.cs"; "b.cs"; "c.cs"; "d.cs" |]

                    let bodies =
                        [|
                            "class A{int M(){return 0;}}\n"
                            String.replicate 60 "class B{int M(){return 0;}}\n"
                            String.replicate 20 "class C{int M(){return 0;}}\n"
                            print
                                (String.replicate 90 "class D{int M(){return 0;}}\n")
                                Settings.Default
                        |]

                    for index = 0 to names.Length - 1 do
                        File.WriteAllText(Path.Combine(root, names[index]), bodies[index])

                    let files = Discovery.files [| root |] None None false 1

                    let lengths =
                        names |> Array.map (fun name -> FileInfo(Path.Combine(root, name)).Length)

                    Expect.sequenceEqual
                        (lengths |> Array.sortDescending)
                        [| lengths[3]; lengths[1]; lengths[2]; lengths[0] |]
                        "d is the longest file, then b, then c, then a."

                    Expect.equal
                        (lengths |> Array.distinct |> Array.length)
                        4
                        "No two of these files are the same length."

                    Expect.sequenceEqual
                        (files |> Array.map (fun file -> Path.GetFileName file.Path))
                        names
                        "Discovery still hands the files over in path order."

                    Expect.sequenceEqual
                        (Formatter.claimOrder files 4 null)
                        [| 3; 1; 2; 0 |]
                        "Workers claim the longest file first."

                    Expect.sequenceEqual
                        (Formatter.claimOrder files 1 null)
                        [| 0; 1; 2; 3 |]
                        "One worker has no tail to bound and pays nothing to find one."

                    let twins =
                        Array.init 8 (fun index ->
                            let path = Path.Combine(root, "same" + string index + ".cs")
                            File.WriteAllText(path, "class S { }\n")

                            { files[0] with Path = path })

                    Expect.sequenceEqual
                        (Formatter.claimOrder twins 4 null)
                        (Array.init 8 id)
                        "Files of one length keep the array's own order."

                    let code, _, errors = invoke [| "--check"; "--no-cache"; "--jobs"; "4"; root |]
                    Expect.equal code 1 errors

                    let reported =
                        errors.Split('\n')
                        |> Array.filter (fun line ->
                            line.StartsWith("Unformatted: ", StringComparison.Ordinal))
                        |> Array.map (fun line -> Path.GetFileName(line.Trim()))

                    Expect.sequenceEqual
                        reported
                        [| "a.cs"; "b.cs"; "c.cs" |]
                        "Each violation is reported under its own path, in path order.")
            }
            test "a link count reads one for a fresh file and two for a hard-linked pair" {
                withDirectory (fun root ->
                    Expect.equal
                        sizeof<LinkCount.DarwinStat>
                        144
                        "Darwin's 64-bit-inode struct stat is 144 bytes."

                    Expect.equal
                        sizeof<LinkCount.WindowsByHandleFileInformation>
                        52
                        "Windows's BY_HANDLE_FILE_INFORMATION is 52 bytes."

                    let original = Path.Combine(root, "One.cs")
                    let alias = Path.Combine(root, "Two.cs")
                    File.WriteAllText(original, "class C { }\n")

                    Expect.equal
                        (LinkCount.count (Path.Combine(root, "Absent.cs")))
                        0
                        "A path that names nothing has no readable link count."

                    Expect.equal (LinkCount.count root) 0 "A directory is not a regular file."

                    if not (OperatingSystem.IsMacOS() || OperatingSystem.IsWindows()) then
                        Expect.equal
                            (LinkCount.count original)
                            0
                            "Only macOS and Windows read a link count; every other platform gates."
                    else
                        Expect.equal (LinkCount.count original) 1 "A fresh file has one link."

                        let accented = Path.Combine(root, "\u00c9t\u00e9-\u65e5\u672c.cs")
                        File.WriteAllText(accented, "class C { }\n")

                        Expect.equal
                            (LinkCount.count accented)
                            1
                            "A path outside ASCII reaches the platform intact."

                        let deepDir =
                            Path.Combine(
                                root,
                                String.replicate 80 "a",
                                String.replicate 80 "b",
                                String.replicate 80 "c"
                            )

                        Directory.CreateDirectory deepDir |> ignore
                        let longPath = Path.Combine(deepDir, "LongPathFile.cs")
                        File.WriteAllText(longPath, "class C { }\n")

                        Expect.equal
                            (LinkCount.measure longPath)
                            (struct (true, 12L, 1))
                            "A path beyond MAX_PATH reads size and link count intact."

                        let start =
                            ProcessStartInfo(
                                if OperatingSystem.IsWindows() then "fsutil" else "ln"
                            )

                        if OperatingSystem.IsWindows() then
                            for arg in [ "hardlink"; "create"; alias; original ] do
                                start.ArgumentList.Add arg
                        else
                            start.ArgumentList.Add original
                            start.ArgumentList.Add alias

                        match Subprocess.run start with
                        | Subprocess.Exited(code, _, errors) -> Expect.equal code 0 errors
                        | Subprocess.Timeout _ -> failtest "Hard-link creation timed out."

                        Expect.equal (LinkCount.count original) 2 "The pair shares an inode."

                        Expect.equal
                            (LinkCount.count alias)
                            2
                            "Either spelling of the inode reports the same count."

                        File.Delete alias

                        Expect.equal
                            (LinkCount.count original)
                            1
                            "Removing the alias returns the inode to one link.")
            }
            test "the snapshot band holds only files that can have an alias" {
                withDirectory (fun root ->
                    let plain = Path.Combine(root, "Plain.cs")
                    let alias = Path.Combine(root, "Alias.cs")
                    File.WriteAllText(plain, "class C { }\n")

                    let start =
                        ProcessStartInfo(if OperatingSystem.IsWindows() then "fsutil" else "ln")

                    if OperatingSystem.IsWindows() then
                        for arg in [ "hardlink"; "create"; alias; plain ] do
                            start.ArgumentList.Add arg
                    else
                        start.ArgumentList.Add plain
                        start.ArgumentList.Add alias

                    match Subprocess.run start with
                    | Subprocess.Exited(code, _, errors) -> Expect.equal code 0 errors
                    | Subprocess.Timeout _ -> failtest "Hard-link creation timed out."

                    let single = FileAccessGate [| root |]
                    let several = FileAccessGate [| root; Path.Combine(root, "nested") |]

                    Expect.isTrue
                        (single.Participates 2)
                        "A file with a second link holds the band."

                    Expect.isFalse
                        (single.Participates 1)
                        "A file named by one directory entry does not."

                    Expect.isTrue
                        (single.Participates 0)
                        "An unreadable link count keeps the band."

                    Expect.isTrue
                        (several.Participates 1)
                        "More than one root keeps every file in the band."

                    let solo = Path.Combine(root, "Solo.cs")
                    File.WriteAllText(solo, "class S { }\n")
                    let files = Discovery.files [| root |] None None false 1
                    let links = Array.zeroCreate<int> files.Length
                    Formatter.claimOrder files 4 links |> ignore

                    let collected =
                        Array.init files.Length (fun index ->
                            Path.GetFileName files[index].Path, links[index])
                        |> Map.ofArray

                    if OperatingSystem.IsMacOS() || OperatingSystem.IsWindows() then
                        Expect.equal
                            collected
                            (Map.ofList [ "Alias.cs", 2; "Plain.cs", 2; "Solo.cs", 1 ])
                            "The claim order's stat carries each file's link count."

                        Expect.equal
                            (collected |> Map.map (fun _ count -> single.Participates count))
                            (Map.ofList [ "Alias.cs", true; "Plain.cs", true; "Solo.cs", false ])
                            "The gate's answer follows the count the claim order read.")
            }
            test "parallel hard-link writes accept already verified output" {
                withDirectory (fun root ->
                    let original = Path.Combine(root, "A.cs")
                    let alias = Path.Combine(root, "B.cs")

                    let source =
                        "class C{"
                        + String.concat
                            ""
                            [ for index in 0..1499 -> $"int M{index}() => {index};" ]
                        + "}"

                    File.WriteAllText(original, source)

                    let start =
                        ProcessStartInfo(if OperatingSystem.IsWindows() then "fsutil" else "ln")

                    if OperatingSystem.IsWindows() then
                        for arg in [ "hardlink"; "create"; alias; original ] do
                            start.ArgumentList.Add arg
                    else
                        start.ArgumentList.Add original
                        start.ArgumentList.Add alias

                    match Subprocess.run start with
                    | Subprocess.Exited(code, _, errors) -> Expect.equal code 0 errors
                    | Subprocess.Timeout _ -> failtest "Hard-link creation timed out."

                    if OperatingSystem.IsMacOS() || OperatingSystem.IsWindows() then
                        let discovered = Discovery.files [| root |] None None false 1
                        let links = Array.zeroCreate<int> discovered.Length
                        Formatter.claimOrder discovered 2 links |> ignore

                        Expect.sequenceEqual
                            links
                            [| 2; 2 |]
                            "The claim order reads both spellings as aliased."

                        let gate = FileAccessGate [| root |]

                        Expect.isTrue
                            (links |> Array.forall gate.Participates)
                            "Both spellings of the shared inode engage the gate."

                    for noCache in [ true; false ] do
                        for _ in 1..4 do
                            File.WriteAllText(original, source)

                            let args =
                                [|
                                    yield "--jobs"
                                    yield "2"
                                    if noCache then
                                        yield "--no-cache"
                                    yield root
                                |]

                            let code, _, errors = invoke args
                            Expect.equal code 0 errors
                            let output = File.ReadAllText original
                            Expect.isTrue (output <> source) "The shared inode was formatted."

                            Expect.equal
                                (File.ReadAllText alias)
                                output
                                "Both links still name the same formatted bytes."

                            Expect.equal
                                (stable output Settings.Default)
                                output
                                "The verified result is stable.")
            }
            test "the pre-write read-back accepts the snapshot and refuses every other file" {
                withDirectory (fun root ->
                    use worker = new Worker()
                    let path = Path.Combine(root, "Target.cs")
                    let sentinel = DateTime(2001, 2, 3, 4, 5, 6, DateTimeKind.Utc)

                    let bytes (text: string) = Encoding.UTF8.GetBytes text
                    let filler = String('x', 40000)

                    let scenarios =
                        [
                            (bytes ("class C{}\n" + filler), bytes ("class C { }\n" + filler))
                            (bytes "class C {    }\n", bytes "class C { }\n")
                            (bytes "aaaaaaaaa\n", bytes "bbbbbbbbb\n")
                            (bytes ("class C{}\n" + String('q', ReadBack.limit)),
                             bytes ("class C { }\n" + String('q', ReadBack.limit)))
                        ]

                    for snapshot, formatted in scenarios do
                        let commit () =
                            worker.Commit(
                                path,
                                snapshot,
                                snapshot.Length,
                                formatted,
                                formatted.Length,
                                0,
                                true
                            )

                        let edited (content: byte array) index =
                            let copy = Array.copy content
                            copy[index] <- copy[index] ^^^ 1uy
                            copy

                        let refuses (content: byte array) why =
                            File.WriteAllBytes(path, content)
                            File.SetLastWriteTimeUtc(path, sentinel)
                            let mutable message = null

                            try
                                commit ()
                            with error ->
                                message <- error.Message

                            Expect.equal message "File changed before writing." why

                            Expect.equal
                                (File.ReadAllBytes path)
                                content
                                "A refused commit leaves the bytes alone."

                            Expect.equal
                                (File.GetLastWriteTimeUtc path)
                                sentinel
                                "A refused commit does not touch the file."

                        File.WriteAllBytes(path, snapshot)
                        commit ()

                        Expect.equal
                            (File.ReadAllBytes path)
                            formatted
                            "A file still holding the snapshot takes the output."

                        File.SetLastWriteTimeUtc(path, sentinel)
                        commit ()

                        Expect.equal
                            (File.GetLastWriteTimeUtc path)
                            sentinel
                            "A hard-link alias already holding the output is not rewritten."

                        refuses
                            (edited snapshot (snapshot.Length - 1))
                            "A same-length edit of the snapshot is not the snapshot."

                        refuses
                            (edited formatted (formatted.Length - 1))
                            "A same-length edit of the output is not the output."

                        refuses
                            (edited snapshot 0)
                            "The first byte is compared like every other one."

                        refuses
                            (Array.append snapshot [| byte 'z' |])
                            "A length matching neither candidate is an unseen file.")
            }
            test
                "a file whose output would exceed the 64 MiB verification limit is skipped with a notice" {
                withDirectory (fun root ->
                    let depth = 4000

                    let source =
                        "class C { int M() => "
                        + String.replicate depth "F(1, "
                        + "1"
                        + String.replicate depth ")"
                        + "; }"

                    let path = Path.Combine(root, "HugeExpr.cs")
                    File.WriteAllText(path, source)

                    let notice (file: string) =
                        file
                        + ": source or formatted output exceeds the 64 MiB syntax verification limit; the file is unchanged."

                    Worker.Run(fun () ->
                        use worker = new Worker()

                        let result =
                            worker.Format(
                                {
                                    Path = path
                                    Settings = Settings.Default
                                    Root = 0
                                },
                                null,
                                false,
                                false
                            )

                        Expect.isNull result.Error "Runaway expansion fails nothing."

                        Expect.isNull
                            result.Unverified
                            "Runaway expansion is not an unproven file."

                        Expect.isTrue result.Skipped "Runaway expansion skips the file."

                        Expect.equal
                            result.Notice
                            (notice path)
                            "The notice names the file first, as an unverified line does."

                        Expect.equal
                            (File.ReadAllText path)
                            source
                            "Rejected expansion leaves the file untouched."

                        let mutable thrown: exn = null

                        try
                            worker.PrintChecked(path, source, Settings.Default) |> ignore
                        with error ->
                            thrown <- error

                        Expect.isTrue
                            (thrown :? VerificationLimitException)
                            "PrintChecked refuses runaway output expansion with the limit's own exception."

                        Expect.stringStarts
                            thrown.Message
                            (path
                             + ": source or formatted output exceeds the 64 MiB syntax verification limit")
                            "PrintChecked names the file and the limit."

                        let oversizedSource =
                            "class C { }\n" + String.replicate VerificationLimit.Characters " "

                        let oversizedPath = Path.Combine(root, "Oversized.cs")
                        File.WriteAllText(oversizedPath, oversizedSource)

                        let oversizedResult =
                            worker.Format(
                                {
                                    Path = oversizedPath
                                    Settings = Settings.Default
                                    Root = 0
                                },
                                null,
                                false,
                                false
                            )

                        Expect.isNull
                            oversizedResult.Error
                            "An input over the limit fails nothing."

                        Expect.isTrue
                            oversizedResult.Skipped
                            "An input over the limit is skipped."

                        Expect.equal
                            oversizedResult.Notice
                            (notice oversizedPath)
                            "An input over the limit is named the same way."

                        let generatedPath = Path.Combine(root, "OversizedGenerated.cs")

                        File.WriteAllText(
                            generatedPath,
                            "// <auto-generated />\n" + oversizedSource
                        )

                        let generatedResult =
                            worker.Format(
                                {
                                    Path = generatedPath
                                    Settings = Settings.Default
                                    Root = 0
                                },
                                null,
                                false,
                                false
                            )

                        Expect.isNull
                            generatedResult.Error
                            "Oversized generated files do not fail."

                        Expect.isTrue
                            generatedResult.Skipped
                            "Oversized generated files are skipped."

                        let conditionalHeader =
                            "class C{void M(){\n#if !A\nint x=1+2+3+4+5;\n#else\n"

                        let conditionalFooter = "int y=1;\n#endif\n}}\n"

                        let conditionalSource =
                            conditionalHeader
                            + String.replicate
                                (VerificationLimit.Characters
                                 - conditionalHeader.Length
                                 - conditionalFooter.Length)
                                " "
                            + conditionalFooter

                        Expect.isNull
                            (worker.PrintChecked(path, conditionalSource, Settings.Default))
                            "The conditional file's formatting is proven."

                        Expect.isTrue
                            (worker.OutputText.Length < 256)
                            "Conditional file whose inactive whitespace shrinks on later passes succeeds.")

                    let shrinking = "class C{}" + String.replicate 200 " "
                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse shrinking tree
                    use document = new DocumentBuffer()
                    use syntax = new SyntaxDocumentBuilder()
                    use printer = new Printer()
                    syntax.MaxOutputLength <- 100
                    printer.MaxOutputLength <- 100
                    syntax.Build(shrinking, tree, document, PrinterOptions.Default)
                    printer.Print(shrinking, document, PrinterOptions.Default)

                    Expect.equal
                        printer.OutputText
                        "class C { }\n"
                        "Shrinking renders whose emitted output fits MaxOutputLength succeed.")
            }
            test "deeply left-nested tuple expressions parse linearly" {
                let makeSource depth =
                    "class C\n{\n    // csff-ignore\n    object M() => "
                    + String.replicate depth "("
                    + "x"
                    + String.replicate depth ", x)"
                    + ";\n}\n"

                let mutable small = 0.0
                let mutable large = 0.0
                let mutable error: exn = null

                let thread =
                    System.Threading.Thread(
                        (fun () ->
                            try
                                let tree = Csff.Parser.SyntaxTree()
                                Parser.parse (makeSource 64) tree

                                let measure depth =
                                    let source = makeSource depth
                                    let watch = System.Diagnostics.Stopwatch.StartNew()
                                    Parser.parse source tree
                                    watch.Stop()

                                    Expect.isTrue
                                        tree.IsComplete
                                        "Nested tuple expression parses completely."

                                    watch.Elapsed.TotalMilliseconds

                                small <- measure 1024
                                large <- measure 8192
                            with ex ->
                                error <- ex),
                        64 * 1024 * 1024
                    )

                thread.Start()
                thread.Join()

                if not (isNull error) then
                    raise error

                Expect.isTrue
                    (large < max 250.0 (small * 20.0))
                    $"Expected linear scaling for left-nested tuples, got 1024={small:F2}ms and 8192={large:F2}ms."
            }
            test "large lambda initializers verify trailing comma changes linearly" {
                let makePair count =
                    let before = System.Text.StringBuilder("var xs = new System.Func<int>[] {\n")
                    let after = System.Text.StringBuilder("var xs = new System.Func<int>[]\n{\n")

                    for index = 0 to count - 1 do
                        before.Append("    () => 1") |> ignore

                        if index < count - 1 then
                            before.Append(',') |> ignore

                        before.Append('\n') |> ignore
                        after.Append("    () => 1,\n") |> ignore

                    before.Append("};\n") |> ignore
                    after.Append("};\n") |> ignore
                    before.ToString(), after.ToString()

                let warmupBefore, warmupAfter = makePair 64
                let checker = Csff.Conformance.TokenPreservation.Checker()

                Expect.isOk
                    (checker.Check(PrinterOptions.Default, "Test.cs", warmupBefore, warmupAfter))
                    "Warmup lambda initializer verifies cleanly."

                let measure count =
                    let before, after = makePair count
                    let watch = System.Diagnostics.Stopwatch.StartNew()
                    let result = checker.Check(PrinterOptions.Default, "Test.cs", before, after)
                    watch.Stop()
                    Expect.isOk result "Lambda initializer trailing comma is accepted."
                    watch.Elapsed.TotalMilliseconds

                let small = measure 1024
                let large = measure 8192

                Expect.isTrue
                    (large < max 250.0 (small * 20.0))
                    $"Expected linear scaling for lambda initializers, got 1024={small:F2}ms and 8192={large:F2}ms."
            }
            test "a bounded prefix decides generated-ness as a lex of the whole source does" {
                let oracle (source: string) =
                    let buffer = Csff.Lexer.TokenBuffer()
                    Csff.Lexer.Lexer.lex source buffer
                    let first = buffer.Token 0
                    let mutable found = false

                    for index = first.TriviaStart to first.TriviaStart + first.LeadingCount - 1 do
                        let trivia = buffer.Trivia index

                        if
                            trivia.Kind = Csff.Lexer.TriviaKind.SingleLineCommentTrivia
                            || trivia.Kind = Csff.Lexer.TriviaKind.MultiLineCommentTrivia
                        then
                            let text = source.AsSpan(trivia.Start, trivia.Length)

                            if
                                text.Contains("<auto-generated".AsSpan(), StringComparison.Ordinal)
                            then
                                found <- true

                    found

                let tails =
                    [
                        "<<<<<<< a\n// <auto-generated/>\nclass C{}"
                        "/* <auto-generated/> */ class C{}"
                        "// <auto-generated/>\nclass C{}"
                        "#if A\n// <auto-generated/>\n#endif\nclass C{}"
                        "class C{}// <auto-generated/>"
                    ]

                use worker = new Worker()
                let mutable agreed = 0
                let mutable positives = 0
                let mutable negatives = 0

                for tail in tails do
                    for offset in GeneratedPrefix.window - 48 .. GeneratedPrefix.window + 1 do
                        let source = "//" + String.replicate (offset - 3) "a" + "\n" + tail
                        let expected = oracle source

                        Expect.equal
                            (worker.IsGenerated source)
                            expected
                            $"Prefix and whole-source decisions agree at offset {offset} of {tail}."

                        agreed <- agreed + 1

                        if expected then
                            positives <- positives + 1
                        else
                            negatives <- negatives + 1

                Expect.equal agreed (tails.Length * 50) "Every boundary placement was compared."
                Expect.isGreaterThan positives 0 "The sweep contains generated sources."
                Expect.isGreaterThan negatives 0 "The sweep contains sources that are not."
            }
            test "a directive keeps a line of its own in each force-flat operand shape" {
                let formats source expected message =
                    Expect.equal (stable source Settings.Default) expected message

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                        ])
                    "An assignment whose right-hand side is a member access."

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        System.Span<byte> s = stackalloc byte["
                            "#if DEBUG"
                            "            4"
                            "#else"
                            "            512"
                            "#endif"
                            "        ];"
                            "    }"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        System.Span<byte> s = stackalloc byte["
                            "#if DEBUG"
                            "            4"
                            "#else"
                            "            512"
                            "#endif"
                            "        ];"
                            "    }"
                            "}"
                        ])
                    "A stackalloc length."

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    void M(Config c)"
                            "    {"
                            "        long v = c.GetValue<"
                            "#if DEBUG"
                            "            int"
                            "#else"
                            "            long"
                            "#endif"
                            "        >(\"K\");"
                            "    }"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    void M(Config c)"
                            "    {"
                            "        long v = c.GetValue<"
                            "#if DEBUG"
                            "        int"
                            "#else"
                            "        long"
                            "#endif"
                            "        >(\"K\");"
                            "    }"
                            "}"
                        ])
                    "A type argument list."

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if COND"
                            "        1;"
                            "#else"
                            "        2;"
                            "#endif"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if COND"
                            "        1;"
                            "#else"
                            "        2;"
                            "#endif"
                            "}"
                        ])
                    "A literal payload, which never reached a force-flat scope."
            }
            test "a directive keeps its line however deep it sits and wherever it ends" {
                let formats source expected message =
                    Expect.equal (stable source Settings.Default) expected message

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        void Inner()"
                            "        {"
                            "            Run(() =>"
                            "            {"
                            "                var x ="
                            "#if DEBUG"
                            "                    Limits.Low;"
                            "#else"
                            "                    Limits.High;"
                            "#endif"
                            "            });"
                            "        }"
                            "    }"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        void Inner()"
                            "        {"
                            "            Run(() =>"
                            "            {"
                            "                var x ="
                            "#if DEBUG"
                            "                    Limits.Low;"
                            "#else"
                            "                    Limits.High;"
                            "#endif"
                            "            });"
                            "        }"
                            "    }"
                            "}"
                        ])
                    "A lambda body inside a local function inside a method."

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int A ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "    void M() { }"
                            "    const int B ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int A ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            ""
                            "    void M() { }"
                            ""
                            "    const int B ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                        ])
                    "The first and the last member of a type."

                formats
                    (String.concat
                        "\n"
                        [
                            "class C"
                            "{"
                            "    const int A ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                            "#if DEBUG"
                            "#endif"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int A ="
                            "#if DEBUG"
                            "        Limits.Low;"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                            "#if DEBUG"
                            "#endif"
                        ])
                    "A directive pair at end of file, with no final newline."
            }
            test "touching directives each keep a line, and so does a region" {
                let formats source expected message =
                    Expect.equal (stable source Settings.Default) expected message

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if DEBUG"
                            "#if TRACE"
                            "        Limits.Trace;"
                            "#else"
                            "        Limits.Low;"
                            "#endif"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if DEBUG"
                            "#if TRACE"
                            "        Limits.Trace;"
                            "#else"
                            "        Limits.Low;"
                            "#endif"
                            "#else"
                            "        Limits.High;"
                            "#endif"
                            "}"
                        ])
                    "An #if opening on another #if, with both #else arms."

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#region R"
                            "        Limits.Low;"
                            "#endregion"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "        #region R"
                            "        Limits.Low;"
                            "        #endregion"
                            "}"
                        ])
                    "A region pair around the same operand."
            }
            test "no comment lands on a directive line, and skipped text keeps its column" {
                let formats source expected message =
                    Expect.equal (stable source Settings.Default) expected message

                formats
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if DEBUG"
                            "        // low"
                            "        Limits.Low;"
                            "#else"
                            "        /* high */ Limits.High;"
                            "#endif"
                            "}"
                        ])
                    (lines
                        [
                            "class C"
                            "{"
                            "    const int F ="
                            "#if DEBUG"
                            "        // low"
                            "        Limits.Low;"
                            "#else"
                            "        /* high */Limits.High;"
                            "#endif"
                            "}"
                        ])
                    "A single-line comment in one arm and a delimited comment in the other."

                Expect.equal
                    (stableUnprovable
                        (lines
                            [ "/* x"; "/** doc */ #if false"; "#if A"; "class Target{}"; "#endif" ])
                        Settings.Default)
                    (lines [ "/* x"; "/** doc */#if false"; "#if A"; "class Target { }"; "#endif" ])
                    "Directive-shaped skipped text stays where C# reads it."

                use worker = new Worker()

                let source =
                    lines [ "/* x"; "/** doc */ #if false"; "#if A"; "class Target{}"; "#endif" ]

                Expect.isNull
                    (worker.PrintChecked("test.cs", source, Settings.Default))
                    "The whitespace-only print is proven."

                Expect.equal
                    (worker.OutputText.ToString())
                    (lines [ "/* x"; "/** doc */#if false"; "#if A"; "class Target{}"; "#endif" ])
                    "It changes only whitespace."
            }
            test "a directive keeps its line at every width across the layout boundary" {
                let shapes =
                    [
                        "a local initializer whose payload is a member path",
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        var local ="
                                "#if COND"
                                "#endif"
                                "            Holder.First;"
                                "    }"
                                "}"
                            ]
                        "a stackalloc length",
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        var s = stackalloc int["
                                "#if COND"
                                "#endif"
                                "            4];"
                                "    }"
                                "}"
                            ]
                        "a region pair in the same scope",
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        var local ="
                                "#region R"
                                "#endregion"
                                "            Holder.First;"
                                "    }"
                                "}"
                            ]
                    ]

                for name, source in shapes do
                    for width in 30..62 do
                        let settings =
                            { Settings.Default with
                                Printer =
                                    { PrinterOptions.Default with
                                        Width = width
                                    }
                            }

                        for line in (stable source settings).Split('\n') do
                            let hash = line.IndexOf '#'

                            if hash >= 0 then
                                Expect.isTrue
                                    (line.AsSpan(0, hash).IsWhiteSpace())
                                    $"Nothing shares a directive's line at width {width} in {name}: {line}"
            }
            test "a comment keeps the line the source gave it under every end of line" {
                for name, source, expected in endOfLineCommentCells do
                    for eol, terminator in
                        [ EndOfLine.Lf, "\n"; EndOfLine.CrLf, "\r\n"; EndOfLine.Cr, "\r" ] do
                        let settings =
                            {
                                Printer =
                                    { PrinterOptions.Default with
                                        EndOfLine = eol
                                    }
                                AutoEndOfLine = false
                            }

                        Expect.equal
                            (stable source settings)
                            (expected.Replace("\n", terminator))
                            $"%s{name} under %A{eol}."
            }
            test "every end of line prints the same program at every width" {
                for name, source, _ in endOfLineCommentCells do
                    for width in 30..62 do
                        let format eol =
                            stable
                                source
                                {
                                    Printer =
                                        { PrinterOptions.Default with
                                            Width = width
                                            EndOfLine = eol
                                        }
                                    AutoEndOfLine = false
                                }

                        let reference = format EndOfLine.Lf

                        for eol, terminator in [ EndOfLine.CrLf, "\r\n"; EndOfLine.Cr, "\r" ] do
                            Expect.equal
                                ((format eol).Replace(terminator, "\n"))
                                reference
                                $"%s{name} prints the same program under %A{eol} at width %d{width}."
            }
            test
                "separatorsOnlyEqual with allowConditional does not skip disabled text before a trailing comma" {
                let source =
                    "class C\n{\n#if FOO\n    int  a  =  1;\n#else\n    int b = 1;\n#endif\n    int[] Items =\n    {\n        1,\n        2\n    };\n}\n"

                let corrupted =
                    "class C\n{\n#if FOO\n    int a = 999;\n#else\n    int b = 1;\n#endif\n    int[] Items =\n    {\n        1,\n        2,\n    };\n}\n"

                let witness =
                    { TransformationWitness.None with
                        ChangedTrailingCommas = true
                        SymbolSets = [| [| "FOO" |] |]
                        AllConfigurationsComplete = true
                    }

                let checker = TokenPreservation.Checker()
                let tree = Csff.Parser.SyntaxTree()
                Parser.parse source tree

                Expect.isFalse
                    (checker.LexicallyPreserved(source, corrupted, tree, witness))
                    "Lexical proof stops at the modified disabled branch."

                let defaultExpected =
                    checker.Normalize(
                        PrinterOptions.Default,
                        source,
                        corrupted,
                        sourceTree = tree,
                        witness = witness,
                        allowDirectProof = true
                    )

                Expect.isFalse
                    (checker.FastEquivalent(defaultExpected, corrupted))
                    "disabledRunsAgree must still inspect the disabled branch before the added trailing comma."

                let verifier = SyntaxPreservation.Checker()

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "Corrupted.cs",
                        source,
                        corrupted,
                        tree,
                        witness
                    )
                with
                | SyntaxPreservation.Verification.Unprovable _ -> ()
                | other ->
                    failtest
                        $"Expected Unprovable for corrupted disabled branch before trailing comma, got %A{other}."

                let falseSource =
                    "class C\n{\n#if false\n    int  a  =  1;\n#endif\n    int[] Items =\n    {\n        1,\n        2\n    };\n}\n"

                let falseCorrupted =
                    "class C\n{\n#if false\n    int a = 999;\n#endif\n    int[] Items =\n    {\n        1,\n        2,\n    };\n}\n"

                let falseWitness =
                    { TransformationWitness.None with
                        ChangedTrailingCommas = true
                        SymbolSets = [||]
                        AllConfigurationsComplete = true
                    }

                let falseTree = Csff.Parser.SyntaxTree()
                Parser.parse falseSource falseTree

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "FalseCorrupted.cs",
                        falseSource,
                        falseCorrupted,
                        falseTree,
                        falseWitness
                    )
                with
                | SyntaxPreservation.Verification.Unprovable _ -> ()
                | other ->
                    failtest
                        $"Expected Unprovable for corrupted #if false branch before trailing comma, got %A{other}."
            }
            test
                "ungated native commit and snapshot read respect exclusive file locks and intermediate conditional render budget" {
                withDirectory (fun directory ->
                    let path = Path.Combine(directory, "Locked.cs")
                    let original = "class C{void M(){}}\n"
                    let formatted = "class C\n{\n    void M() { }\n}\n"
                    let originalBytes = Encoding.UTF8.GetBytes original
                    let formattedBytes = Encoding.UTF8.GetBytes formatted
                    File.WriteAllBytes(path, originalBytes)

                    use readerHandle =
                        File.OpenHandle(path, FileMode.Open, FileAccess.Read, FileShare.Read)

                    use worker = new Worker()

                    Expect.throws
                        (fun () ->
                            worker.CommitSpan(
                                path,
                                originalBytes,
                                originalBytes.Length,
                                formattedBytes.AsSpan(),
                                0,
                                false
                            ))
                        "An ungated native commit must not bypass an active shared lock."

                    readerHandle.Dispose()

                    use writerHandle =
                        File.OpenHandle(path, FileMode.Open, FileAccess.ReadWrite, FileShare.None)

                    let mutable buf = ArrayPool<byte>.Shared.Rent 64

                    try
                        Expect.throws
                            (fun () ->
                                Worker.ReadIntoBuffer(
                                    null,
                                    ArrayPool<byte>.Shared,
                                    &buf,
                                    path,
                                    1,
                                    int64 originalBytes.Length
                                )
                                |> ignore)
                            "A native snapshot read must not bypass an active exclusive lock."
                    finally
                        ArrayPool<byte>.Shared.Return buf)

                let source =
                    "class C { void M() {\n#if A\n{\n#else\n"
                    + String.replicate 20 "{"
                    + "\n#endif\n"
                    + String.replicate 200 "F();\n"
                    + "#if A\n}\n#else\n"
                    + String.replicate 20 "}"
                    + "\n#endif\n}}"

                let tree = Csff.Parser.SyntaxTree()
                Parser.parse source tree
                use printer = new Printer()
                printer.MaxOutputLength <- 8000
                use syntax = new SyntaxDocumentBuilder(printer)
                syntax.MaxOutputLength <- 32000
                use doc = new DocumentBuffer()
                syntax.BuildAndPrint(source, tree, doc, PrinterOptions.Default)
                let output = printer.OutputText

                Expect.isTrue
                    (output.Length < 8000)
                    "Final conditional render fits within printer.MaxOutputLength even when the intermediate pass needed syntax.MaxOutputLength."
            }
            test
                "raw I/O read loop handles short reads, EINTR retries, and concurrent file growth without truncation or hybrid corruption" {
                let makeShortReader (backing: byte array) (maxChunk: int) (interruptAtCall: int) =
                    let mutable calls = 0

                    fun (dst: byte array) (offset: int) (remaining: int) ->
                        calls <- calls + 1

                        if calls = interruptAtCall then
                            -2
                        elif offset >= backing.Length then
                            0
                        else
                            let n = min remaining (min maxChunk (backing.Length - offset))
                            Buffer.BlockCopy(backing, offset, dst, offset, n)
                            n

                let payload = Array.init 700 (fun i -> byte ((i * 31 + 7) &&& 0xFF))
                let readBuf = Array.zeroCreate<byte>(payload.Length + 1)
                let shortReader = makeShortReader payload 13 3

                let n = LinkCount.readUpToWith shortReader readBuf (payload.Length + 1)

                Expect.equal n payload.Length "Chunked short reads with EINTR must reach true EOF."

                Expect.equal
                    readBuf[.. payload.Length - 1]
                    payload
                    "Accumulated bytes must match backing data."

                let mutable errCalls = 0

                let errReader (dst: byte array) (offset: int) (remaining: int) =
                    errCalls <- errCalls + 1

                    if errCalls = 1 then
                        let n = min remaining 16
                        Buffer.BlockCopy(payload, offset, dst, offset, n)
                        n
                    else
                        -1

                Expect.equal
                    (LinkCount.readUpToWith errReader readBuf (payload.Length + 1))
                    -1
                    "Read error after partial read must return -1 rather than partial length as EOF."

                let hinted = 65_536
                let appended = Array.init (hinted + 256) (fun i -> byte ((i + 3) &&& 0xFF))
                let growBuf = Array.zeroCreate<byte>(hinted + 1)
                let rpcLimitedReader = makeShortReader appended hinted -1

                let detectedLen = LinkCount.readUpToWith rpcLimitedReader growBuf (hinted + 1)

                Expect.equal
                    detectedLen
                    (hinted + 1)
                    "Short read capped at hinted must still read past hinted when appended bytes exist."

                let snapshot = Encoding.UTF8.GetBytes(String('a', 64))
                let shorterOut = Encoding.UTF8.GetBytes(String('b', 32))
                let longerOut = Encoding.UTF8.GetBytes(String('c', 96))

                for label, formatted in [ "shorter", shorterOut; "longer", longerOut ] do
                    let diskAfterAppend =
                        Array.append snapshot (Encoding.UTF8.GetBytes "APPENDED_TAIL")

                    let maxLen = max snapshot.Length formatted.Length
                    let window = Array.zeroCreate<byte>(maxLen + 1)
                    let chunkAtOriginalReader = makeShortReader diskAfterAppend snapshot.Length -1

                    let currentLen =
                        LinkCount.readUpToWith chunkAtOriginalReader window (maxLen + 1)

                    let verdict =
                        Worker.CheckCommitWindow(
                            snapshot,
                            snapshot.Length,
                            formatted.AsSpan(),
                            window,
                            currentLen
                        )

                    Expect.equal
                        verdict
                        -1
                        $"Commit window ({label}) must reject concurrently appended file even when chunk size equals snapshot length."

                let validMaxLen = max snapshot.Length shorterOut.Length
                let validWindow = Array.zeroCreate<byte>(validMaxLen + 1)
                let origShortReader = makeShortReader snapshot 11 2
                let origLen = LinkCount.readUpToWith origShortReader validWindow (validMaxLen + 1)

                let origVerdict =
                    Worker.CheckCommitWindow(
                        snapshot,
                        snapshot.Length,
                        shorterOut.AsSpan(),
                        validWindow,
                        origLen
                    )

                Expect.equal
                    origVerdict
                    snapshot.Length
                    "Chunked snapshot commit must return true EOF length for truncation."

                let alreadyReader = makeShortReader shorterOut 7 2
                let alreadyLen = LinkCount.readUpToWith alreadyReader validWindow (validMaxLen + 1)

                let alreadyVerdict =
                    Worker.CheckCommitWindow(
                        snapshot,
                        snapshot.Length,
                        shorterOut.AsSpan(),
                        validWindow,
                        alreadyLen
                    )

                Expect.equal
                    alreadyVerdict
                    -2
                    "Already-formatted file read in short chunks must return no-op sentinel (-2)."

                withDirectory (fun directory ->
                    let largePath = Path.Combine(directory, "Large.cs")

                    let largeBytes =
                        Encoding.UTF8.GetBytes("class C {\n" + String(' ', 70_000) + "\n}\n")

                    File.WriteAllBytes(largePath, largeBytes)

                    let mutable buf = ArrayPool<byte>.Shared.Rent 64

                    try
                        let struct (readLen, _) =
                            Worker.ReadIntoBuffer(
                                null,
                                ArrayPool<byte>.Shared,
                                &buf,
                                largePath,
                                1,
                                int64 (largeBytes.Length - 1)
                            )

                        Expect.equal
                            readLen
                            largeBytes.Length
                            "ReadIntoBuffer must detect concurrent growth beyond stale hintLength and return full bytes."

                        Expect.equal
                            buf[.. readLen - 1]
                            largeBytes
                            "ReadIntoBuffer must return exact bytes when file grows beyond hint."
                    finally
                        ArrayPool<byte>.Shared.Return buf

                    let emptyPath = Path.Combine(directory, "Empty.cs")
                    File.WriteAllBytes(emptyPath, Array.empty)

                    if LinkCount.isAvailable () then
                        let smallPath = Path.Combine(directory, "Small.cs")
                        let smallBytes = Encoding.UTF8.GetBytes("class S { }")
                        File.WriteAllBytes(smallPath, smallBytes)

                        let fd = LinkCount.openFile (smallPath, 0x01000014)
                        Expect.isTrue (fd >= 0) "POSIX test open should succeed."

                        try
                            let exactBuf = Array.zeroCreate<byte>(smallBytes.Length + 1)

                            Expect.equal
                                (LinkCount.preadAll fd exactBuf (smallBytes.Length + 1))
                                smallBytes.Length
                                "preadAll must return exact length at EOF."

                            Expect.equal
                                exactBuf[.. smallBytes.Length - 1]
                                smallBytes
                                "preadAll must preserve file contents."

                            let boundedBuf = Array.zeroCreate<byte> 5

                            Expect.equal
                                (LinkCount.preadAll fd boundedBuf 5)
                                5
                                "preadAll must stop cleanly at caller maxBytes bound."
                        finally
                            LinkCount.closeFd fd |> ignore

                    use worker = new Worker()

                    worker.CommitSpan(
                        emptyPath,
                        Array.empty,
                        0,
                        Encoding.UTF8.GetBytes("class E {}\n").AsSpan(),
                        0,
                        false
                    )

                    Expect.equal
                        (File.ReadAllText emptyPath)
                        "class E {}\n"
                        "CommitSpan must expand a zero-byte snapshot cleanly."

                    Expect.throws
                        (fun () ->
                            worker.CommitSpan(
                                largePath,
                                largeBytes[.. largeBytes.Length - 10],
                                largeBytes.Length - 9,
                                Encoding.UTF8.GetBytes("class C { }\n").AsSpan(),
                                0,
                                false
                            ))
                        "CommitSpan must reject a file larger than snapshot length even when prefix matches.")
            }
            test "dual-character class globs match without compiling regexes" {
                let cases =
                    [|
                        "**/[Bb]in",
                        FastGlobKind.AnyDualSegment,
                        [| "src/Bin", true; "src/bin", true; "src/Bin/x", false; "src/cin", false |]
                        "**/[Dd]ebug*",
                        FastGlobKind.AnyDualSegmentPrefix,
                        [|
                            "src/Debug", true
                            "src/debug_out", true
                            "src/Debug/x", false
                            "src/rebug", false
                        |]
                        "**/*.[Cc]ache",
                        FastGlobKind.AnyDualSuffix,
                        [|
                            "src/a.Cache", true
                            "src/a.cache", true
                            "src/.Cache", true
                            "src/a.dache", false
                        |]
                    |]

                for pattern, expectedKind, samples in cases do
                    let fast = Glob.fastCompile false pattern
                    Expect.equal fast.Kind expectedKind pattern

                    for candidate, expected in samples do
                        let mutable rx1: System.Text.RegularExpressions.Regex = null
                        let mutable rx2: System.Text.RegularExpressions.Regex = null
                        let lastSlash = candidate.LastIndexOf('/')
                        let segment = candidate.AsSpan(lastSlash + 1)

                        Expect.equal
                            (Glob.isMatchScanned false fast &rx1 candidate)
                            expected
                            (pattern + " scanned " + candidate)

                        Expect.equal
                            (Glob.isMatchSpan fast &rx2 (candidate.AsSpan()) segment)
                            expected
                            (pattern + " span " + candidate)

                        Expect.isNull rx1 "Fast dual glob must not compile a regex."
                        Expect.isNull rx2 "Fast dual span glob must not compile a regex."

                let bracketFollower = "**/[x]].cs"
                let bracketRegex = Glob.compileIgnore bracketFollower
                let bracketFast = Glob.fastCompile false bracketFollower
                let mutable rx3 = bracketRegex

                for candidate in [| "src/x].cs"; "src/x.cs"; "src/].cs" |] do
                    let lastSlash = candidate.LastIndexOf('/')
                    let segment = candidate.AsSpan(lastSlash + 1)
                    let expected = bracketRegex.IsMatch candidate

                    Expect.equal
                        (Glob.isMatchScanned false bracketFast &rx3 candidate)
                        expected
                        ("scanned " + candidate)

                    Expect.equal
                        (Glob.isMatchSpan bracketFast &rx3 (candidate.AsSpan()) segment)
                        expected
                        ("span " + candidate)
            }
            test "nested #endif before #else or #elif does not insert or grow blank lines" {
                let cases =
                    [
                        "empty nested #if before #else",
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ]
                        "empty nested #if before #elif",
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                "#elif B"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                "#elif B"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ]
                        "doubly nested empty #if before #else",
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#if M"
                                "#endif"
                                "#endif"
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#if M"
                                "#endif"
                                "#endif"
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ]
                        "non-empty nested #if before #else",
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "    void F() { }"
                                "#endif"
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                ""
                                "#if !A"
                                "#if N"
                                "    void F() { }"
                                "#endif"
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ]
                        "existing blank line before #else preserved once",
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                ""
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                ""
                                "#else"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ]
                        "empty nested #if before member in outer #if",
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void E() { }"
                                "#if !A"
                                "#if N"
                                "#endif"
                                "    void H() { }"
                                "#endif"
                                "}"
                            ]
                        "namespace declarations with nested #if before #else",
                        lines
                            [
                                "namespace N"
                                "{"
                                "    class E { }"
                                "#if !A"
                                "#if M"
                                "#endif"
                                "#else"
                                "    class H { }"
                                "#endif"
                                "}"
                            ],
                        lines
                            [
                                "namespace N"
                                "{"
                                "    class E { }"
                                "#if !A"
                                "#if M"
                                "#endif"
                                "#else"
                                "    class H { }"
                                "#endif"
                                "}"
                            ]
                    ]

                for label, source, expected in cases do
                    Expect.equal (stable source Settings.Default) expected label
            }
            test
                "triple-slash doc comments after a comma in delimited lists move to the next line without blank lines" {
                let actual =
                    stable
                        "class C\n{\n    int[] h =\n    {\n        1, ///s\n        2,\n    };\n}\n"
                        Settings.Default

                Expect.equal
                    actual
                    "class C\n{\n    int[] h =\n    {\n        1,\n        ///s\n        2,\n    };\n}\n"
                    "Single-line doc comment after initializer comma moves to its own line without adding a blank line."

                let objectInit =
                    stable
                        "class C\n{\n    D d = new D\n    {\n        A = 1, /// doc\n        B = 2,\n    };\n}\n"
                        Settings.Default

                Expect.equal
                    objectInit
                    "class C\n{\n    D d = new D\n    {\n        A = 1,\n        /// doc\n        B = 2,\n    };\n}\n"
                    "Single-line doc comment after object initializer comma moves to its own line without adding a blank line."
            }
            test
                "own-line comments in object creation chains and binary pattern operands stay on their own line" {
                let creationChain =
                    stable
                        "class C\n{\n    object o = new D\n    {\n        // c\n    }.P;\n    object p = new D(a,\n        // c\n        b) { }.V;\n    object q = new D(\n        /*o*/ null) { }.V;\n}\n"
                        Settings.Default

                Expect.equal
                    creationChain
                    "class C\n{\n    object o = new D\n    {\n        // c\n    }.P;\n    object p = new D(\n        a,\n        // c\n        b\n    )\n    { }.V;\n    object q = new D(\n        /*o*/null\n    )\n    { }.V;\n}\n"
                    "Comments in object creation chains and empty initializers expand without joining."

                let binaryInCreationChain =
                    stable
                        "class C\n{\n    void M()\n    {\n        Profiles = new CollectionViewSource\n        {\n            Source = a ||\n                // All tags must match\n                b,\n        }.View;\n    }\n}\n"
                        Settings.Default

                Expect.equal
                    binaryInCreationChain
                    "class C\n{\n    void M()\n    {\n        Profiles = new CollectionViewSource\n        {\n            Source =\n                a\n                ||\n                // All tags must match\n                b,\n        }.View;\n    }\n}\n"
                    "Own-line comment inside binary expression in object creation chain stays on its own line."

                let binaryPatternCall =
                    stable
                        "class C\n{\n    void M()\n    {\n        if (plain is { Length: > 0 }\n            && ProgressiveDelivery.TryBuild(\n                wire,\n                transcoded,\n                responseEdited,\n                // comment\n                minWireBytes: 1) is { } plan)\n        {\n            return;\n        }\n    }\n}\n"
                        Settings.Default

                Expect.equal
                    binaryPatternCall
                    "class C\n{\n    void M()\n    {\n        if (\n            plain is { Length: > 0 }\n            && ProgressiveDelivery.TryBuild(\n                wire,\n                transcoded,\n                responseEdited,\n                // comment\n                minWireBytes: 1\n            )\n                is { } plan\n        )\n        {\n            return;\n        }\n    }\n}\n"
                    "Own-line comment before argument in binary pattern operand stays on its own line."
            }
            test "doc comments after an enum comma re-indent continuation lines on the first pass" {
                let singleLineDoc =
                    stable "enum E\n{\n    A, ///< a\n       ///< b\n    B,\n}\n" Settings.Default

                Expect.equal
                    singleLineDoc
                    "enum E\n{\n    A,\n\n    ///< a\n    ///< b\n    B,\n}\n"
                    "Multi-line /// doc comment after enum comma re-indents continuation lines on the first pass."

                let col0Doc =
                    stable "enum E\n{\n    A, ///< a\n///< b\n    B,\n}\n" Settings.Default

                Expect.equal
                    col0Doc
                    "enum E\n{\n    A,\n\n    ///< a\n    ///< b\n    B,\n}\n"
                    "Column-0 /// continuation line after enum comma re-indents on the first pass."

                let multiLineBlockDoc =
                    stable "enum E\n{\n    A, /**< a\n\t\t * b\n\t\t */\n}\n" Settings.Default

                Expect.equal
                    multiLineBlockDoc
                    "enum E\n{\n    A,\n    /**< a\n         * b\n         */\n}\n"
                    "Multi-line /** doc comment after enum comma shifts continuation lines on the first pass."
            }
            test "trailing comment on the last element of a list keeps lambda layout stable" {
                let pdfPig comma =
                    lines
                        [
                            "namespace N"
                            "{"
                            "    public class C"
                            "    {"
                            "        public void M()"
                            "        {"
                            "            List<Tuple<EdgeType, Func<PdfRectangle, double>>> a ="
                            "            ["
                            "                Tuple.Create<EdgeType, Func<PdfRectangle, double>>(EdgeType.Right, x => Math.Round(x.Right, 0))"
                            + comma
                            + " // use right"
                            "            ];"
                            "        }"
                            "    }"
                            "}"
                        ]

                let expectedPdfPig =
                    lines
                        [
                            "namespace N"
                            "{"
                            "    public class C"
                            "    {"
                            "        public void M()"
                            "        {"
                            "            List<Tuple<EdgeType, Func<PdfRectangle, double>>> a ="
                            "            ["
                            "                Tuple.Create<EdgeType, Func<PdfRectangle, double>>(EdgeType.Right, x =>"
                            "                    Math.Round(x.Right, 0)"
                            "                ), // use right"
                            "            ];"
                            "        }"
                            "    }"
                            "}"
                        ]

                for comma in [ ""; "," ] do
                    Expect.equal
                        (stable (pdfPig comma) Settings.Default)
                        expectedPdfPig
                        ("Collection expression with trailing lambda and comment (" + comma + ")")

                let ravenDb comma =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        var query ="
                            "            from e in session.Query<Employee, Employees_ByFirstName>()"
                            "            select new"
                            "            {"
                            "                FirstName = e.FirstName,"
                            "                _ = RavenQuery.Include<Employee>(a => a.Company.Split('#', StringSplitOptions.None)[1])"
                            + comma
                            + " // Inside select"
                            "            };"
                            "    }"
                            "}"
                        ]

                let expectedRavenDb =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        var query ="
                            "            from e in session.Query<Employee, Employees_ByFirstName>()"
                            "            select new"
                            "            {"
                            "                FirstName = e.FirstName,"
                            "                _ = RavenQuery.Include<Employee>(a =>"
                            "                    a.Company.Split('#', StringSplitOptions.None)[1]"
                            "                ), // Inside select"
                            "            };"
                            "    }"
                            "}"
                        ]

                for comma in [ ""; "," ] do
                    Expect.equal
                        (stable (ravenDb comma) Settings.Default)
                        expectedRavenDb
                        ("Anonymous object with lambda argument and comment (" + comma + ")")

                let numSharp comma =
                    lines
                        [
                            "namespace NumSharp.Tests.Selection"
                            "{"
                            "    public class IndexingProbeMatrix_Tests"
                            "    {"
                            "        private static readonly ECase[] CombSetErr ="
                            "        {"
                            "            new(\"cse03_multiadv_gridmismatch\", () =>"
                            "            {"
                            "                var a = B();"
                            "                a[IA(), \":\", IB()] = np.array(new long[] { 1, 2, 3, 4, 5 });"
                            "                return a;"
                            "            })" + comma + " // (5,) !-> grid (2,3)"
                            "        };"
                            "    }"
                            "}"
                        ]

                let expectedNumSharp =
                    lines
                        [
                            "namespace NumSharp.Tests.Selection"
                            "{"
                            "    public class IndexingProbeMatrix_Tests"
                            "    {"
                            "        private static readonly ECase[] CombSetErr = { new(\"cse03_multiadv_gridmismatch\", () =>"
                            "            {"
                            "                var a = B();"
                            "                a[IA(), \":\", IB()] = np.array(new long[] { 1, 2, 3, 4, 5 });"
                            "                return a;"
                            "            }), // (5,) !-> grid (2,3)"
                            "        };"
                            "    }"
                            "}"
                        ]

                for comma in [ ""; "," ] do
                    Expect.equal
                        (stable (numSharp comma) Settings.Default)
                        expectedNumSharp
                        ("Array initializer with block lambda and comment (" + comma + ")")

                let commentBeforeCommaCases =
                    [
                        "class C { object[] a = { F(a, () => { A(); }) /* c */, }; }"
                        "class C { object[] a = { F(a, () => { A(); }) // c\n, }; }"
                        "class C { object[] a = { F(a, (x) => { A(); }) // c\n, }; }"
                    ]

                for source in commentBeforeCommaCases do
                    ignore (stable source Settings.Default)
            }
            test "directives inside cross-branch block comments retain their directive column" {
                let cases =
                    [
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "#if V1"
                                "/*"
                                "#endif"
                                "#pragma warning restore 618"
                                "#if V1"
                                "*/"
                                "#endif"
                                "    }"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "#if V1"
                                "        /*"
                                "#endif"
                                "#pragma warning restore 618"
                                "#if V1"
                                "        */"
                                "#endif"
                                "    }"
                                "}"
                            ]
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "#if V1"
                                "/*"
                                "#else"
                                "#pragma warning disable 618"
                                "#nullable enable"
                                "#endif"
                                "#if V1"
                                "*/"
                                "#endif"
                                "    }"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "#if V1"
                                "        /*"
                                "#else"
                                "#pragma warning disable 618"
                                "#nullable enable"
                                "#endif"
                                "#if V1"
                                "        */"
                                "#endif"
                                "    }"
                                "}"
                            ]
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "#if !V1"
                                "/*"
                                "#endif"
                                "#pragma warning restore 618"
                                "#if !V1"
                                "*/"
                                "#endif"
                                "#if V1"
                                "        F();"
                                "#endif"
                                "    }"
                                "}"
                            ],
                        lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "#if !V1"
                                "        /*"
                                "#endif"
                                "#pragma warning restore 618"
                                "#if !V1"
                                "        */"
                                "#endif"
                                "#if V1"
                                "        F();"
                                "#endif"
                                "    }"
                                "}"
                            ]
                    ]

                for source, expected in cases do
                    Expect.equal
                        (stable source Settings.Default)
                        expected
                        "Cross-branch comment directive formatting matches expected."
            }

            test "using after extern alias with leading blank line and comment sorts idempotently" {
                let source =
                    lines
                        [
                            "extern alias viewer;"
                            "using ViewerSideWindowCommand = viewer::DiffEngine.WindowCommand;"
                            ""
                            "// The viewer's own half of the app."
                            "using CommandKind = viewer::CommandKind;"
                            "public class C { }"
                        ]

                let expected =
                    lines
                        [
                            "extern alias viewer;"
                            "// The viewer's own half of the app."
                            ""
                            "using CommandKind = viewer::CommandKind;"
                            "using ViewerSideWindowCommand = viewer::DiffEngine.WindowCommand;"
                            ""
                            "public class C { }"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Blank line before a commented using after extern alias settles on pass 1."

                let docSeparated =
                    lines
                        [
                            "extern alias e;"
                            "/// Zebra"
                            "using Z;"
                            ""
                            "/// Alpha"
                            "using A;"
                            "class X { }"
                        ]

                let docExpected =
                    lines
                        [
                            "extern alias e;"
                            "/// Zebra"
                            ""
                            "/// Alpha"
                            "using A;"
                            "using Z;"
                            ""
                            "class X { }"
                        ]

                Expect.equal
                    (stable docSeparated Settings.Default)
                    docExpected
                    "Distinct documentation-comment blocks after extern alias remain separated."

                let afterIgnoreRange =
                    lines
                        [
                            "extern alias e;"
                            "// csff-ignore-start"
                            "using Z;"
                            "// csff-ignore-end"
                            ""
                            "// B"
                            "using B;"
                            "class X { }"
                        ]

                let afterIgnoreExpected =
                    lines
                        [
                            "extern alias e;"
                            "// B"
                            ""
                            "using B;"
                            ""
                            "// csff-ignore-start"
                            "using Z;"
                            "// csff-ignore-end"
                            ""
                            "class X { }"
                        ]

                Expect.equal
                    (stable afterIgnoreRange Settings.Default)
                    afterIgnoreExpected
                    "Consumed ignore-end markers do not block header blank normalization."
            }

            test "vertical tab and form feed before comments are stripped idempotently" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "\x0b            // Save the work book"
                            "\x0c            /* Block comment */"
                            "    }"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        // Save the work book"
                            "        /* Block comment */"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Vertical tab and form feed before comments are stripped like spaces and tabs."
            }

            test "conditional using block followed by region around using preserves directive order" {
                let source =
                    lines
                        [
                            "#if A"
                            "using B;"
                            "#endif"
                            "#region R"
                            "using C;"
                            "#endregion"
                            "class X { }"
                        ]

                let expected =
                    lines
                        [
                            "using C;"
                            "#if A"
                            "using B;"
                            "#endif"
                            "#region R"
                            "#endregion"
                            "class X { }"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Trailing #region after #if/#endif using block stays after #endif."
            }

            test
                "forged TransformationWitness fields and unparsed sourceTree cannot fabricate Proven" {
                let verifier = SyntaxPreservation.Checker()

                let expectUnprovable (label: string) (v: SyntaxPreservation.Verification) =
                    match v with
                    | SyntaxPreservation.Verification.Unprovable _ -> ()
                    | other -> failtest $"Expected Unprovable for %s{label}, got %A{other}."

                let ifSource =
                    lines
                        [
                            "#if FOO"
                            "class C { int a = 1; }"
                            "#endif"
                            "class D { int[] xs = new[] { 1, 2 }; }"
                        ]

                let ifCorrupted =
                    lines
                        [
                            "#if FOO"
                            "class C { int a = ; }"
                            "#endif"
                            "class D { int[] xs = new[] { 1, 2, }; }"
                        ]

                let emptySetsWitness =
                    { TransformationWitness.Searched with
                        SymbolSets = [||]
                        AllConfigurationsComplete = true
                    }

                let ifTree = Csff.Parser.SyntaxTree()
                Parser.parse ifSource ifTree

                expectUnprovable
                    "#if FOO with SymbolSets = [||] via Decide"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "ForgedSets.cs",
                        ifSource,
                        ifCorrupted,
                        sourceTree = ifTree,
                        witness = emptySetsWitness
                    ))

                expectUnprovable
                    "#if FOO with SymbolSets = [||] via DecideDirect"
                    (verifier.DecideDirect(
                        PrinterOptions.Default,
                        "ForgedSets.cs",
                        ifSource,
                        ifCorrupted,
                        ifTree,
                        emptySetsWitness
                    ))

                expectUnprovable
                    "#if FOO with SymbolSets = [||] via DecideDirectSpan"
                    (verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "ForgedSets.cs",
                        ifSource,
                        ifCorrupted.AsSpan(),
                        ifTree,
                        emptySetsWitness
                    ))

                let partialSource =
                    lines
                        [
                            "#if FOO"
                            "class A { }"
                            "#endif"
                            "#if BAR"
                            "class B { int y = 2; }"
                            "#endif"
                        ]

                let partialCorrupted =
                    lines
                        [
                            "#if FOO"
                            "class A { }"
                            "#endif"
                            "#if BAR"
                            "class B { int y = 99; }"
                            "#endif"
                        ]

                let partialWitness =
                    { TransformationWitness.Searched with
                        SymbolSets = [| [| "FOO" |] |]
                        AllConfigurationsComplete = true
                    }

                expectUnprovable
                    "omitted BAR symbol set"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "PartialSets.cs",
                        partialSource,
                        partialCorrupted,
                        witness = partialWitness
                    ))

                let brokenUsingSource = lines [ "using B;"; "using A;"; "class C { int x = ; }" ]

                let brokenUsingFormatted = lines [ "using A;"; "using B;"; "class C { int x = ; }" ]

                expectUnprovable
                    "broken default-config syntax with AllConfigurationsComplete = true"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "BrokenDefault.cs",
                        brokenUsingSource,
                        brokenUsingFormatted,
                        witness = emptySetsWitness
                    ))

                let brokenIfSource =
                    lines
                        [
                            "#if FOO"
                            "using B;"
                            "using A;"
                            "class C { int[] xs = new[] { 1, 2 }; int x = ; }"
                            "#endif"
                        ]

                let brokenIfFormatted =
                    lines
                        [
                            "#if FOO"
                            "using A;"
                            "using B;"
                            "class C { int[] xs = new[] { 1, 2, }; int x = ; }"
                            "#endif"
                        ]

                expectUnprovable
                    "broken #if FOO syntax with AllConfigurationsComplete = true"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "BrokenIf.cs",
                        brokenIfSource,
                        brokenIfFormatted,
                        witness = partialWitness
                    ))

                let unparsedSource = lines [ "class C { int[] xs = new[] { 1, 2 }; int x = ; }" ]

                let unparsedFormatted =
                    lines [ "class C { int[] xs = new[] { 1, 2, }; int x = ; }" ]

                let unparsedTree = Csff.Parser.SyntaxTree()

                expectUnprovable
                    "unparsed sourceTree with AllConfigurationsComplete = true"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "UnparsedTree.cs",
                        unparsedSource,
                        unparsedFormatted,
                        sourceTree = unparsedTree,
                        witness = emptySetsWitness
                    ))

                let recoveredIfSource =
                    lines [ "#if FOO"; "class C { int[] xs = new[] { 1, 2 }; ) ; }"; "#endif" ]

                let recoveredIfFormatted =
                    lines [ "#if FOO"; "class C { int[] xs = new[] { 1, 2, }; ) ; }"; "#endif" ]

                let trailingCommaWitness =
                    { TransformationWitness.None with
                        ChangedTrailingCommas = true
                        SymbolSets = [| [| "FOO" |] |]
                        AllConfigurationsComplete = true
                    }

                expectUnprovable
                    "recovered #if FOO syntax with AllConfigurationsComplete = true"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "RecoveredIf.cs",
                        recoveredIfSource,
                        recoveredIfFormatted,
                        witness = trailingCommaWitness
                    ))
            }

            test "discover #if directives hidden by a block comment that crosses a conditional" {
                let source =
                    lines
                        [
                            "#define HIDDEN"
                            "#if !A"
                            "/*"
                            "#endif"
                            "#if B"
                            "#endif"
                            "#undef HIDDEN"
                            "#if !A"
                            "// */"
                            "#endif"
                            "#if !HIDDEN"
                            "class BOnly{int x=1;}"
                            "#endif"
                        ]

                let expected =
                    lines
                        [
                            "#define HIDDEN"
                            "#if !A"
                            "/*"
                            "#endif"
                            "#if B"
                            "#endif"
                            "#undef HIDDEN"
                            "#if !A"
                            "// */"
                            "#endif"
                            "#if !HIDDEN"
                            "class BOnly"
                            "{"
                            "    int x = 1;"
                            "}"
                            "#endif"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Formats branch unlocked when #if !A false edge removes a crossing block comment without quotes."

                let docCommentSource =
                    lines
                        [
                            "#define HIDDEN"
                            "#if !A"
                            "/**"
                            "#endif"
                            "#if B"
                            "#endif"
                            "#undef HIDDEN"
                            "#if !A"
                            "// */"
                            "#endif"
                            "#if !HIDDEN"
                            "class DocB{int x=1;}"
                            "#endif"
                        ]

                let docCommentExpected =
                    lines
                        [
                            "#define HIDDEN"
                            "#if !A"
                            "/**"
                            "#endif"
                            "#if B"
                            "#endif"
                            "#undef HIDDEN"
                            "#if !A"
                            "// */"
                            "#endif"
                            "#if !HIDDEN"
                            "class DocB"
                            "{"
                            "    int x = 1;"
                            "}"
                            "#endif"
                        ]

                Expect.equal
                    (stable docCommentSource Settings.Default)
                    docCommentExpected
                    "Formats branch unlocked when #if !A false edge removes a crossing multiline doc comment without quotes."

                let compositeAlternativeSource =
                    lines
                        [
                            "class Prelude { string T = @\""
                            "#if Z"
                            "\"; }"
                            "#if A||B"
                            "#if A"
                            "#endif"
                            "class Holder { string S = @\""
                            "#endif"
                            "#if A||B"
                            "\"; }"
                            "/** */ #if !A"
                            "class Target{int x=1;}"
                            "#endif"
                            "/** */ #endif"
                        ]

                let compositeTree = Csff.Parser.SyntaxTree()
                Csff.Parser.Parser.parse compositeAlternativeSource compositeTree

                Expect.equal
                    (Preprocessor.symbolSets compositeAlternativeSource compositeTree)
                    [| [| "A" |]; [| "B" |] |]
                    "Preprocessor.symbolSets discovers both {A} and {B} for newly exposed #if !A inside #if A||B."

                let formattedAlternativeSource =
                    lines
                        [
                            "#if A || B"
                            "#if A"
                            "#endif"
                            "class Holder"
                            "{"
                            "    string S = @\""
                            "#endif"
                            "#if false"
                            "\";"
                            "}"
                            "#if !A"
                            "class Target{int x=1;}"
                            "#endif"
                            "#endif"
                        ]

                let formattedAlternativeExpected =
                    lines
                        [
                            "#if A || B"
                            "#if A"
                            "#endif"
                            "class Holder"
                            "{"
                            "    string S ="
                            "        @\""
                            "#endif"
                            "#if false"
                            "\";"
                            "}"
                            ""
                            "#if !A"
                            "class Target"
                            "{"
                            "    int x = 1;"
                            "}"
                            "#endif"
                            "#endif"
                        ]

                Expect.equal
                    (stable formattedAlternativeSource Settings.Default)
                    formattedAlternativeExpected
                    "Formats alternative {B} branch for newly exposed #if !A inside #if A||B."

                let undefAfterStringSource =
                    lines
                        [
                            "#if !C"
                            "#if !A"
                            "#endif"
                            "class Holder { string S = @\""
                            "#endif"
                            "#undef B"
                            "#if false"
                            "\"; }"
                            "#elif A==!B"
                            "class Target{int x=1;}"
                            "#endif"
                        ]

                let undefAfterStringExpected =
                    lines
                        [
                            "#if !C"
                            "#if !A"
                            "#endif"
                            "class Holder"
                            "{"
                            "    string S ="
                            "        @\""
                            "#endif"
                            "#undef B"
                            "#if false"
                            "\";"
                            "}"
                            "#elif A==!B"
                            "class Target"
                            "{"
                            "    int x = 1;"
                            "}"
                            "#endif"
                        ]

                Expect.equal
                    (stable undefAfterStringSource Settings.Default)
                    undefAfterStringExpected
                    "Re-solves visible #elif when a false outer branch exposes #undef B and changes the required symbol set."

                let independentStringBranches =
                    let sb =
                        System.Text.StringBuilder(
                            "#if !Z\nclass D0 { string s = @\"\n#if false\n#endif\n\"; }\n#endif\n#if Z\nclass Z0 { }\n#endif\n"
                        )

                    for i = 1 to 16 do
                        sb.Append(
                            $"#if B{i}\nclass D{i} {{ string s = @\"\n#if false\n#endif\n\"; }}\n#endif\n"
                        )
                        |> ignore

                    sb.ToString()

                let indTree = Csff.Parser.SyntaxTree()
                Csff.Parser.Parser.parse independentStringBranches indTree
                let sw = System.Diagnostics.Stopwatch.StartNew()
                let sets = Preprocessor.symbolSets independentStringBranches indTree
                sw.Stop()

                Expect.equal
                    sets.Length
                    17
                    "Independent string branches with balanced directive text must not combine exponentially."

                Expect.isLessThan
                    sw.Elapsed.TotalSeconds
                    2.0
                    "Discovery across 16 independent string branches completes quickly."

                for sameLine in [ false; true ] do
                    let suffix = if sameLine then "" else "\n"

                    let hiddenDefineBeforeEq =
                        $"#if !B\nclass Holder {{ string S = @\"\n#endif\n#define A\n#if false\n\"; }}\n#endif\n#if !A\nclass Other {{ }}\n#endif\n#if A == !B\nclass Target {{ int x = 1; }}\n#endif{suffix}"

                    let hiddenTree = Csff.Parser.SyntaxTree()
                    Csff.Parser.Parser.parse hiddenDefineBeforeEq hiddenTree

                    Expect.equal
                        (Preprocessor.symbolSets hiddenDefineBeforeEq hiddenTree)
                        [| [| "B" |]; [| "A" |] |]
                        $"Discovers [|\"A\"|] when skipped #if !B branch hides #define A before #if A == !B (trailingNewline={not sameLine})."
            }

            test
                "Glob handles triple-star, segment-bound double-star, end-of-string anchors, and surrogate pairs in classes" {
                let triple = Glob.compile "***/Foo.cs"
                Expect.isTrue (triple.IsMatch "Foo.cs") "***/Foo.cs matches root Foo.cs."
                Expect.isTrue (triple.IsMatch "dir/Foo.cs") "***/Foo.cs matches one subdir."
                Expect.isTrue (triple.IsMatch "a/b/Foo.cs") "***/Foo.cs matches nested subdir."

                let nestedTriple = Glob.compile "a/***/Foo.cs"

                Expect.isTrue
                    (nestedTriple.IsMatch "a/Foo.cs")
                    "a/***/Foo.cs collapses intermediate slash."

                Expect.isTrue
                    (nestedTriple.IsMatch "a/b/c/Foo.cs")
                    "a/***/Foo.cs crosses directories."

                let tripleIgnore = Glob.compileIgnore "***/Foo.cs"
                Expect.isTrue (tripleIgnore.IsMatch "Foo.cs") "***/Foo.cs matches root Foo.cs."
                Expect.isTrue (tripleIgnore.IsMatch "dir/Foo.cs") "***/Foo.cs matches one subdir."

                Expect.isTrue
                    (tripleIgnore.IsMatch "a/b/Foo.cs")
                    "***/Foo.cs matches nested subdir."

                let segTrailing = Glob.compileIgnore "gen**/Foo.cs"
                Expect.isTrue (segTrailing.IsMatch "gen/Foo.cs") "gen**/Foo.cs matches gen/Foo.cs."

                Expect.isTrue
                    (segTrailing.IsMatch "genX/Foo.cs")
                    "gen**/Foo.cs matches genX/Foo.cs."

                Expect.isFalse
                    (segTrailing.IsMatch "genFoo.cs")
                    "gen**/Foo.cs does not match genFoo.cs."

                Expect.isFalse
                    (segTrailing.IsMatch "gen/sub/Foo.cs")
                    "gen**/Foo.cs does not cross separator."

                let segLeading = Glob.compileIgnore "**gen/Foo.cs"
                Expect.isTrue (segLeading.IsMatch "gen/Foo.cs") "**gen/Foo.cs matches gen/Foo.cs."
                Expect.isTrue (segLeading.IsMatch "xgen/Foo.cs") "**gen/Foo.cs matches xgen/Foo.cs."

                Expect.isFalse
                    (segLeading.IsMatch "x/gen/Foo.cs")
                    "**gen/Foo.cs does not cross separator."

                let segMiddle = Glob.compileIgnore "foo**bar/Foo.cs"

                Expect.isTrue
                    (segMiddle.IsMatch "foobar/Foo.cs")
                    "foo**bar/Foo.cs matches foobar/Foo.cs."

                Expect.isFalse
                    (segMiddle.IsMatch "foo/bar/Foo.cs")
                    "foo**bar/Foo.cs does not cross separator."

                let escapedRight = Glob.compileGitIgnore @"src/**\/Foo.cs"

                Expect.isFalse
                    (escapedRight.IsMatch "src/Foo.cs")
                    @"src/**\/Foo.cs requires at least one subdirectory after src/."

                Expect.isTrue
                    (escapedRight.IsMatch "src/a/Foo.cs")
                    @"src/**\/Foo.cs matches one subdir."

                Expect.isTrue
                    (escapedRight.IsMatch "src/a/b/Foo.cs")
                    @"src/**\/Foo.cs crosses nested dirs before escaped slash."

                for compile in [ Glob.compileGitIgnore; Glob.compileIgnore ] do
                    let escapedLeft = compile @"a\/**/F.cs"

                    Expect.isTrue
                        (escapedLeft.IsMatch "a/F.cs")
                        @"a\/**/F.cs matches zero intermediate directories after escaped slash."

                    Expect.isTrue
                        (escapedLeft.IsMatch "a/b/F.cs")
                        @"a\/**/F.cs matches one intermediate directory."

                    Expect.isTrue
                        (escapedLeft.IsMatch "a/b/c/F.cs")
                        @"a\/**/F.cs matches nested intermediate directories."

                    let escapedRootLeft = compile @"src\/**/Foo.cs"

                    Expect.isTrue
                        (escapedRootLeft.IsMatch "src/Foo.cs")
                        @"src\/**/Foo.cs matches zero intermediate directories."

                    Expect.isFalse
                        (escapedRootLeft.IsMatch "srcX/Foo.cs")
                        @"src\/**/Foo.cs does not treat escaped slash as non-slash."

                let escapedAltBoundary = Glob.compileEditorConfig @"{src\/,lib}**/Foo.cs"

                Expect.isTrue
                    (escapedAltBoundary.IsMatch "src/Foo.cs")
                    @"{src\/,lib}**/Foo.cs matches direct child on escaped-slash branch."

                Expect.isTrue
                    (escapedAltBoundary.IsMatch "libsub/Foo.cs")
                    @"{src\/,lib}**/Foo.cs matches non-boundary continuation on non-slash branch."

                Expect.isFalse
                    (escapedAltBoundary.IsMatch "srcFoo.cs")
                    @"{src\/,lib}**/Foo.cs requires slash after src on escaped-slash branch."

                let editorConfigDoubleStar = Glob.compileEditorConfig "src/**.cs"

                Expect.isTrue
                    (editorConfigDoubleStar.IsMatch "src/Foo.cs")
                    "EditorConfig src/**.cs matches direct child."

                Expect.isTrue
                    (editorConfigDoubleStar.IsMatch "src/sub/Foo.cs")
                    "EditorConfig src/**.cs crosses directory separators."

                let gitNegatedEmoji = Glob.compileGitIgnore "[!a].cs"

                Expect.isFalse
                    (gitNegatedEmoji.IsMatch "😀.cs")
                    ".gitignore [!a].cs uses byte semantics so multi-byte emoji stays excluded under *.cs + ![!a].cs."

                let gitEmojiClass = Glob.compileGitIgnore "[😀].cs"

                Expect.isFalse
                    (gitEmojiClass.IsMatch "😀.cs")
                    ".gitignore [😀].cs uses byte semantics and does not match UTF-8 emoji as one scalar."

                let gitEmojiRange = Glob.compileGitIgnore "[😀-😄].cs"

                Expect.isFalse
                    (gitEmojiRange.IsMatch "😀.cs")
                    ".gitignore [😀-😄].cs compiles cleanly and does not match UTF-8 emoji."

                let anchor = Glob.compile "Foo.cs"
                Expect.isTrue (anchor.IsMatch "Foo.cs") "Exact match succeeds."

                Expect.isFalse
                    (anchor.IsMatch "Foo.cs\n")
                    "Anchor does not match before trailing newline."

                let emojiClass = Glob.compile "[😀].cs"
                Expect.isTrue (emojiClass.IsMatch "😀.cs") "[😀].cs matches 😀.cs."

                Expect.isFalse
                    (emojiClass.IsMatch "\uD83D.cs")
                    "[😀].cs rejects lone high surrogate."

                Expect.isFalse (emojiClass.IsMatch "\uDE00.cs") "[😀].cs rejects lone low surrogate."

                let emojiFast = Glob.fastCompileWithFlags false false "**/[😀].cs"
                let mutable rxFast: System.Text.RegularExpressions.Regex = null
                let emojiSpan = "src/😀.cs"

                Expect.isTrue
                    (Glob.isMatchSpan emojiFast &rxFast (emojiSpan.AsSpan()) ("😀.cs".AsSpan()))
                    "FastGlob span matches **/ [😀].cs outside Git ignore."

                Expect.isFalse
                    (Glob.isMatchSpan
                        emojiFast
                        &rxFast
                        ("src/\uD83D.cs".AsSpan())
                        ("\uD83D.cs".AsSpan()))
                    "FastGlob rejects lone surrogate under **/ [😀].cs."

                let emojiRange = Glob.compile "[😀-😄].cs"
                Expect.isTrue (emojiRange.IsMatch "😀.cs") "[😀-😄].cs matches start."
                Expect.isTrue (emojiRange.IsMatch "😁.cs") "[😀-😄].cs matches middle."
                Expect.isTrue (emojiRange.IsMatch "😄.cs") "[😀-😄].cs matches end."
                Expect.isFalse (emojiRange.IsMatch "😅.cs") "[😀-😄].cs excludes out-of-range emoji."

                let mixedRange = Glob.compile "[a-😄].cs"
                Expect.isTrue (mixedRange.IsMatch "z.cs") "[a-😄].cs matches BMP ASCII."
                Expect.isTrue (mixedRange.IsMatch "😁.cs") "[a-😄].cs matches astral codepoint."
                Expect.isFalse (mixedRange.IsMatch "/.cs") "[a-😄].cs excludes slash."

                let negatedEmoji = Glob.compile "[!😀].cs"
                Expect.isFalse (negatedEmoji.IsMatch "😀.cs") "[!😀].cs excludes 😀."
                Expect.isTrue (negatedEmoji.IsMatch "😃.cs") "[!😀].cs matches other emoji."
                Expect.isTrue (negatedEmoji.IsMatch "a.cs") "[!😀].cs matches BMP char."
                Expect.isFalse (negatedEmoji.IsMatch "/.cs") "[!😀].cs excludes slash."

                let dualPair = Glob.compile "**/[😀😃]in"
                let dualFast = Glob.fastCompileWithFlags false false "**/[😀😃]in"
                let mutable rxDual: System.Text.RegularExpressions.Regex = null
                Expect.isTrue (dualPair.IsMatch "dir/😃in") "**/[😀😃]in regex matches 😃."

                Expect.isTrue
                    (Glob.isMatchSpan dualFast &rxDual ("dir/😀in".AsSpan()) ("😀in".AsSpan()))
                    "FastGlob matches **/ [😀😃]in outside Git ignore."

                let braceAltGlobstar = Glob.compileEditorConfig "src/{**/Foo.cs,Other.cs}"

                Expect.isTrue
                    (braceAltGlobstar.IsMatch "src/Foo.cs")
                    "EditorConfig {**/Foo.cs,Other.cs} matches zero directories after {."

                Expect.isTrue
                    (braceAltGlobstar.IsMatch "src/a/b/Foo.cs")
                    "EditorConfig {**/Foo.cs,Other.cs} matches nested directories."

                Expect.isTrue
                    (braceAltGlobstar.IsMatch "src/Other.cs")
                    "EditorConfig {**/Foo.cs,Other.cs} matches second alternative."

                let commaAltGlobstar = Glob.compileEditorConfig "src/{Other.cs,**/Foo.cs}"

                Expect.isTrue
                    (commaAltGlobstar.IsMatch "src/Foo.cs")
                    "EditorConfig {Other.cs,**/Foo.cs} matches zero directories after comma."

                let wildScalarNegatedEmoji = Glob.compile "*[!😀].cs"

                Expect.isFalse
                    (wildScalarNegatedEmoji.IsMatch "😀.cs")
                    "*[!😀].cs cannot split surrogate pair to match excluded emoji."

                Expect.isTrue
                    (wildScalarNegatedEmoji.IsMatch "a.cs")
                    "*[!😀].cs matches BMP filename."

                let negatedEmojiWild = Glob.compile "[!😀]*.cs"

                Expect.isFalse
                    (negatedEmojiWild.IsMatch "😀a.cs")
                    "[!😀]*.cs cannot split surrogate pair to match excluded emoji."

                let wildNegatedBmp = Glob.compile "*[!a].cs"

                Expect.isTrue
                    (wildNegatedBmp.IsMatch "😀.cs")
                    "*[!a].cs matches single astral emoji."

                let gitTripleNewline = Glob.compileGitIgnore "***"

                Expect.isTrue
                    (gitTripleNewline.IsMatch "a\nb.cs")
                    ".gitignore *** matches filenames containing LF."

                let slashBraceGlobstar = Glob.compileEditorConfig "{src/,tests/}**/Foo.cs"

                Expect.isTrue
                    (slashBraceGlobstar.IsMatch "src/Foo.cs")
                    "EditorConfig {src/,tests/}**/Foo.cs matches zero directories after src/."

                Expect.isTrue
                    (slashBraceGlobstar.IsMatch "tests/Foo.cs")
                    "EditorConfig {src/,tests/}**/Foo.cs matches zero directories after tests/."

                Expect.isTrue
                    (slashBraceGlobstar.IsMatch "src/a/b/Foo.cs")
                    "EditorConfig {src/,tests/}**/Foo.cs matches nested directories."

                Expect.isFalse
                    (slashBraceGlobstar.IsMatch "srcFoo.cs")
                    "EditorConfig {src/,tests/}**/Foo.cs still requires directory slash."

                let nonBoundaryBraceGlobstar = Glob.compileEditorConfig "a{**/Foo.cs,Bar.cs}"

                Expect.isFalse
                    (nonBoundaryBraceGlobstar.IsMatch "aFoo.cs")
                    "EditorConfig a{**/Foo.cs,Bar.cs} must not treat after-{ without '/' as boundary."

                Expect.isTrue
                    (nonBoundaryBraceGlobstar.IsMatch "a/Foo.cs")
                    "EditorConfig a{**/Foo.cs,Bar.cs} matches a/Foo.cs."

                let mixedBraceGlobstar = Glob.compileEditorConfig "{a,b/}**/Foo.cs"

                Expect.isTrue
                    (mixedBraceGlobstar.IsMatch "b/Foo.cs")
                    "EditorConfig {a,b/}**/Foo.cs matches zero directories for slash-terminated alternative."

                Expect.isTrue
                    (mixedBraceGlobstar.IsMatch "a/Foo.cs")
                    "EditorConfig {a,b/}**/Foo.cs matches directory after non-slash alternative."

                Expect.isFalse
                    (mixedBraceGlobstar.IsMatch "aFoo.cs")
                    "EditorConfig {a,b/}**/Foo.cs must not collapse missing slash on first alternative."

                let emptyOptBraceGlobstar = Glob.compileEditorConfig "{,src/}**/Foo.cs"

                Expect.isTrue
                    (emptyOptBraceGlobstar.IsMatch "Foo.cs")
                    "EditorConfig {,src/}**/Foo.cs matches root Foo.cs."

                Expect.isTrue
                    (emptyOptBraceGlobstar.IsMatch "src/Foo.cs")
                    "EditorConfig {,src/}**/Foo.cs matches zero directories under src/."

                let nestedBraceGlobstar = Glob.compileEditorConfig "p/{a/,{b/,c/}}**/Foo.cs"

                Expect.isTrue
                    (nestedBraceGlobstar.IsMatch "p/c/Foo.cs")
                    "EditorConfig nested brace boundaries preserve zero-directory matching."
            }

            test "scoped declaration expressions parse in tuple deconstructions and arguments" {
                for source in
                    [
                        "class C { void M() { (scoped var x, var y) = (1, 2); } }\n"
                        "class C { void M() { (var x, scoped var y) = (1, 2); } }\n"
                        "class C { void M() { (scoped int x, scoped Span<int> y) = (1, default); } }\n"
                        "class C { void M() { (scoped ref int x, var y) = (1, 2); } }\n"
                        "class C { void M() { (scoped (int a, int b) x, var y) = ((1, 2), 3); } }\n"
                        "class C { void M() { ((scoped var x, var y), scoped var z) = ((1, 2), 3); } }\n"
                        "class C { void M() { (a: scoped var x, b: var y) = (1, 2); } }\n"
                        "class C { void M() { var t = (scoped var x, 1); } }\n"
                        "class C { void F(out int x) { x = 1; } void M() { F(out scoped var y); } }\n"
                        "class C { void M(int scoped) { var t = (scoped, 1); } }\n"
                        "class scoped { }\nclass C { void M() { (scoped x, var y) = (new(), 2); } }\n"
                        "class C { void M() { var (scoped, y) = (1, 2); } }\n"
                        "class C { int scoped(int a, int b) => a + b; void M() { var t = (scoped(1, 2), 3); } }\n"
                    ] do
                    let tree = Csff.Parser.SyntaxTree()

                    Expect.equal
                        (NodeOracle.check "test.cs" source tree)
                        (Ok())
                        $"CST matches Roslyn for: {source}"

                    stable source Settings.Default |> ignore
            }

            test
                "shebang, global using, using global:: cross-frame, and #if SYM directive violations diagnose accurately" {
                let checker = SyntaxPreservation.Checker()

                let expectProven name verdict =
                    Expect.equal verdict SyntaxPreservation.Verification.Proven name

                let shebangGlobalUsingSrc =
                    lines
                        [
                            "#!/usr/bin/env dotnet"
                            "#if FOO"
                            "using M;"
                            "#endif"
                            "global using Z;"
                            "global using A;"
                            ""
                            "class C { }"
                        ]

                let shebangGlobalUsingFmt =
                    GeneratedOutput.format PrinterOptions.Default shebangGlobalUsingSrc

                Expect.isNull
                    (TriviaPreservation.difference shebangGlobalUsingSrc shebangGlobalUsingFmt)
                    "Moving global usings past a closed #if frame must not miscount global tokens."

                expectProven
                    "shebang with sorted global using across closed #if frame"
                    (checker.Decide(
                        PrinterOptions.Default,
                        "ShebangGlobalUsing.cs",
                        shebangGlobalUsingSrc,
                        shebangGlobalUsingFmt
                    ))

                let shebangScriptSrc =
                    lines
                        [
                            "#!/usr/bin/env dotnet"
                            "using Z;"
                            "using A;"
                            "#if SYM"
                            "static public class C"
                            "{"
                            "    int[] xs = { 1, 2, };"
                            "    string S() => \"\"\""
                            "            hello"
                            "            \"\"\";"
                            "}"
                            "#endif"
                        ]

                let shebangScriptFmt =
                    GeneratedOutput.format PrinterOptions.Default shebangScriptSrc

                expectProven
                    "shebang script with using sort, modifier sort, trailing comma, raw string, and #if SYM"
                    (checker.Decide(
                        PrinterOptions.Default,
                        "Script.cs",
                        shebangScriptSrc,
                        shebangScriptFmt
                    ))

                Expect.isError
                    (checker.Check(
                        PrinterOptions.Default,
                        "MovedShebang.cs",
                        "#!/usr/bin/env dotnet\nclass C {}\n",
                        "\n#!/usr/bin/env dotnet\nclass C { }\n"
                    ))
                    "Moving a shebang off line 1 must still be refused."

                Expect.isError
                    (checker.Check(
                        PrinterOptions.Default,
                        "ChangedShebang.cs",
                        "#!/usr/bin/env dotnet\nclass C {}\n",
                        "#!/usr/bin/env other\nclass C { }\n"
                    ))
                    "Changing a shebang payload must still be refused."

                let globalQualifiedCrossFrameSrc =
                    lines
                        [
                            "using Z;"
                            "#if FOO"
                            "using M;"
                            "#endif"
                            "using global::A;"
                            ""
                            "class C { }"
                        ]

                let globalQualifiedCrossFrameFmt =
                    GeneratedOutput.format PrinterOptions.Default globalQualifiedCrossFrameSrc

                expectProven
                    "using global:: sorted across closed #if frame"
                    (checker.Decide(
                        PrinterOptions.Default,
                        "GlobalQualified.cs",
                        globalQualifiedCrossFrameSrc,
                        globalQualifiedCrossFrameFmt
                    ))

                let condDirectiveSource =
                    lines [ "#if SYM"; "#pragma warning disable CS0168"; "class C { }"; "#endif" ]

                let condDirectiveCorrupted =
                    lines [ "#if SYM"; "#pragma warning invalid"; "class C { }"; "#endif" ]

                match
                    checker.Decide(
                        PrinterOptions.Default,
                        "CondDirective.cs",
                        condDirectiveSource,
                        condDirectiveCorrupted
                    )
                with
                | SyntaxPreservation.Verification.Violation _ -> ()
                | other ->
                    failtest $"Directive corruption under #if SYM must be Violation, got %A{other}"
            }

            test "union declarations follow type declaration modifier rules" {
                let verifier = SyntaxPreservation.Checker()
                let unionFileSource = "sealed file union U(int);\n"
                let unionFileFormatted = stable unionFileSource Settings.Default

                Expect.equal
                    unionFileFormatted
                    "file sealed union U(int);\n"
                    "file sorts before sealed on union."

                let tree = Csff.Parser.SyntaxTree()
                Parser.parse unionFileSource tree

                Expect.equal
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "UnionFile.cs",
                        unionFileSource,
                        unionFileFormatted,
                        sourceTree = tree
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Decide proves file sealed union."

                Expect.equal
                    (verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "UnionFile.cs",
                        unionFileSource,
                        unionFileFormatted.AsSpan(),
                        tree,
                        TransformationWitness.Searched
                    ))
                    SyntaxPreservation.Verification.Proven
                    "DecideDirectSpan proves file sealed union."

                let externSrc = "namespace N\n{\n    public extern union U(int);\n}\n"
                let externMoved = "namespace N\n{\n    extern public union U(int);\n}\n"
                let externTree = Csff.Parser.SyntaxTree()
                Parser.parse externSrc externTree

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "UnionExtern.cs",
                        externSrc,
                        externMoved,
                        sourceTree = externTree
                    )
                with
                | SyntaxPreservation.Verification.Unprovable _ -> ()
                | other -> failtest $"Expected Unprovable for extern move on union, got %A{other}."

                match
                    verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "UnionExtern.cs",
                        externSrc,
                        externMoved.AsSpan(),
                        externTree,
                        TransformationWitness.Searched
                    )
                with
                | SyntaxPreservation.Verification.Unprovable _ -> ()
                | other ->
                    failtest
                        $"Expected Unprovable via DecideDirectSpan for extern move on union, got %A{other}."

                Expect.isError
                    (verifier.Check(
                        PrinterOptions.Default,
                        "UnionExtern.cs",
                        externSrc,
                        externMoved
                    ))
                    "Check refuses extern move on union."
            }

            test "null-conditional assignments match Roslyn CST and format stably" {
                for source in
                    [
                        "class C { void M() { c?.X = 1; } }\n"
                        "class C { void M() { c?.S ??= \"a\"; } }\n"
                        "class C { void M() { a?[0].X = 1; } }\n"
                        "class C { void M() { a?.B?.C = 1; } }\n"
                        "class C { void M() { c?.M()?.X = 1; } }\n"
                        "class C { void M() { a?.B += c?.D ?? 0; } }\n"
                        "class C { void M() { c?.X = d?.Y = 1; } }\n"
                        "class C { void M() { var r = 1 + c?.X = 2; } }\n"
                        "class C { void M() { var r = cond ? c?.X = 1 : d?.Y = 2; } }\n"
                        "class C { void M() { (c?.X) = 1; } }\n"
                        "class C { void M() { a.Foo().Bar?.Baz = veryLongValue1 + veryLongValue2 + veryLongValue3 + veryLongValue4 + veryLongValue5; } }\n"
                    ] do
                    let tree = Csff.Parser.SyntaxTree()

                    Expect.equal
                        (NodeOracle.check "test.cs" source tree)
                        (Ok())
                        $"CST matches Roslyn for: {source}"

                    stable source Settings.Default |> ignore
            }

            test "csffrc matches override, formatter, and duplicate keys case-insensitively" {
                withDirectory (fun root ->
                    let writeCfg name (content: string) =
                        let path = Path.Combine(root, name)
                        File.WriteAllText(path, content)
                        path

                    for name, badContent, expectedError in
                        [
                            ".csffrc.json",
                            """{"overrides":[{"files":"*.cs","Formatter":"javascript","indentSize":2}]}""",
                            "csff overrides support only the csharp formatter."
                            ".csffrc.yaml",
                            "overrides:\n  - Files: '*.cs'\n    Formatter: javascript\n",
                            "csff overrides support only the csharp formatter."
                            ".csffrc.json",
                            """{"printWidth":80,"PrintWidth":120}""",
                            "Duplicate configuration key"
                            ".csffrc.json",
                            """{"overrides":[{"files":"*.cs","indentSize":2,"IndentSize":4}]}""",
                            "Duplicate configuration key"
                            ".csffrc.yaml",
                            "printWidth: 80\nPrintWidth: 120\n",
                            "Duplicate configuration key"
                            ".csffrc.json",
                            """{"Overrides":[{"Files":123}]}""",
                            "overrides.files must be a string."
                        ] do
                        let path = writeCfg name badContent

                        try
                            Configuration.read path |> ignore
                            failtest $"Expected rejection for {badContent}"
                        with :? ArgumentException as ex ->
                            Expect.stringContains
                                ex.Message
                                expectedError
                                $"Mismatch for {badContent}"

                    let okPath =
                        writeCfg
                            ".csffrc.json"
                            """{"PrintWidth":90,"Overrides":[{"Files":"sub/*.cs","Formatter":"CSharp","IndentSize":2}]}"""

                    let config = Configuration.read okPath

                    let baseSettings =
                        Configuration.forFile (Some config) (Path.Combine(root, "a.cs"))

                    let subSettings =
                        Configuration.forFile (Some config) (Path.Combine(root, "sub/a.cs"))

                    Expect.equal baseSettings.Printer.Width 90 "Base PrintWidth applies."

                    Expect.equal
                        subSettings.Printer.IndentSize
                        2
                        "Uppercase Overrides/Files/IndentSize apply."

                    Expect.equal subSettings.Printer.Width 90 "Override inherits PrintWidth.")
            }

            test "keep a list pattern's variable designation out of the delimited elements" {
                let actual1 =
                    stable "class C { bool M(int[] xs) => xs is [1, 2,] rest; }" Settings.Default

                Expect.equal
                    actual1
                    "class C\n{\n    bool M(int[] xs) => xs is [1, 2] rest;\n}\n"
                    "Single-line list pattern with trailing comma and designation"

                let actual2 =
                    stable "class C { bool M(int[] xs) => xs is [] rest; }" Settings.Default

                Expect.equal
                    actual2
                    "class C\n{\n    bool M(int[] xs) => xs is [] rest;\n}\n"
                    "Empty list pattern with designation"

                let actual3 =
                    stable "class C { bool M(int[] xs) => xs is [1, 2,] _; }" Settings.Default

                Expect.equal
                    actual3
                    "class C\n{\n    bool M(int[] xs) => xs is [1, 2] _;\n}\n"
                    "List pattern with trailing comma and discard designation"

                let longList =
                    "class C { bool M(int[] xs) => xs is [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24] rest; }"

                let actualLong = stable longList Settings.Default

                Expect.isTrue
                    (actualLong.Contains("24,\n            ] rest;"))
                    "Broken list pattern places trailing comma before closing bracket and separates designation"

                let withCommentInside =
                    stable
                        "class C { bool M(int[] xs) => xs is [1, 2 /* c */ ] rest; }"
                        Settings.Default

                Expect.isTrue
                    (withCommentInside.Contains("] rest;"))
                    "Comment inside list pattern does not merge bracket with designation"

                let withCommentBeforeDesignation =
                    stable
                        "class C { bool M(int[] xs) => xs is [1, 2] /* c */ rest; }"
                        Settings.Default

                Expect.isTrue
                    (withCommentBeforeDesignation.Contains("] /* c */\n            rest;"))
                    "Comment before designation preserves valid spacing and layout"

                let withSlice =
                    stable
                        "class C { bool M(int[] xs) => xs is [1, 2, .. var middle] rest; }"
                        Settings.Default

                Expect.equal
                    withSlice
                    "class C\n{\n    bool M(int[] xs) => xs is [1, 2, .. var middle] rest;\n}\n"
                    "List pattern with slice pattern and outer designation"
            }

            test "do not sort usings across an unclosed #region" {
                let singleUnclosed = "using Z;\n#region R\nusing A;\n#endregion\n\nclass C { }\n"

                Expect.equal
                    (stable singleUnclosed Settings.Default)
                    singleUnclosed
                    "Single unclosed #region keeps using order."

                let nestedUnclosed =
                    "using Z;\n#region Outer\nusing M;\n#region Inner\nusing A;\n#endregion\n#endregion\n\nclass C { }\n"

                Expect.equal
                    (stable nestedUnclosed Settings.Default)
                    nestedUnclosed
                    "Nested unclosed #region keeps region nesting and using order."

                let postIfUnclosed =
                    "#if X\n#region R\nusing Z;\n#endif\nusing A;\n#endregion\n\nclass C { }\n"

                Expect.equal
                    (stable postIfUnclosed Settings.Default)
                    postIfUnclosed
                    "Unclosed #region after initial #if keeps using order."

                let enclosingHeader = "#region R\nusing Z;\nusing A;\n#endregion\n\nclass C { }\n"

                let expectedEnclosing = "#region R\nusing A;\nusing Z;\n#endregion\n\nclass C { }\n"

                Expect.equal
                    (stable enclosingHeader Settings.Default)
                    expectedEnclosing
                    "Top-level enclosing #region still sorts usings inside it."

                let primeSource = "#if true\nusing Z;\nusing M;\n#endif\nclass P { }\n"

                let reusedTarget =
                    "#if true\nusing B;\n#endif\n#region R\nusing C;\n#endregion\nclass X { }\n"

                use worker = new Worker()

                Expect.isNull
                    (worker.PrintChecked("Prime.cs", primeSource, Settings.Default))
                    "Prime file verifies."

                worker.Print(reusedTarget, Settings.Default)
                let firstPass = worker.OutputText
                worker.Print(firstPass, Settings.Default)
                let secondPass = worker.OutputText

                Expect.equal
                    secondPass
                    firstPass
                    "Reused Worker keeps identical region-depth state across files."

                Expect.isNull
                    (worker.PrintChecked("Target.cs", reusedTarget, Settings.Default))
                    "Target file verifies."
            }

            test
                "modifier runs follow CSharpier around comments and keep partial or required in place" {
                let ownLine =
                    lines
                        [
                            "namespace N"
                            "{"
                            "    static // <Title>T</Title>"
                            "    // <Description>"
                            "    public class C { }"
                            "}"
                        ]

                Expect.equal
                    (stable
                        (lines
                            [
                                "namespace N"
                                "{"
                                "    static // <Title>T</Title>"
                                "           // <Description>"
                                "    public class C {}"
                                "}"
                            ])
                        Settings.Default)
                    ownLine
                    "A comment in front of a later word keeps the run as written."

                Expect.equal
                    (stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    [DllImport(\"x\")]"
                                "    // comment"
                                "    extern static int M();"
                                "    [A]"
                                "    // c2"
                                "    static internal bool N() { return true; }"
                                "}"
                            ])
                        Settings.Default)
                    (lines
                        [
                            "class C"
                            "{"
                            "    [DllImport(\"x\")]"
                            "    // comment"
                            "    static extern int M();"
                            ""
                            "    [A]"
                            "    // c2"
                            "    internal static bool N()"
                            "    {"
                            "        return true;"
                            "    }"
                            "}"
                        ])
                    "The run's leading comment prints in front of the sorted run."

                let documented =
                    stable
                        "class B { internal virtual int Prop => 0; }\nclass Foo : B\n{\n    sealed /** is \"sealed\" checked? */ internal override int Prop => 0;\n}\n"
                        Settings.Default

                let sealedAt = documented.IndexOf("sealed", StringComparison.Ordinal)
                let commentAt = documented.IndexOf("/**", StringComparison.Ordinal)
                let internalAt = documented.IndexOf("internal override", StringComparison.Ordinal)

                Expect.isTrue
                    (0 <= sealedAt && sealedAt < commentAt && commentAt < internalAt)
                    $"The documentation comment stays inside the run: {documented}"

                for source in
                    [
                        "public partial static class T { }\n"
                        "class C\n{\n    public required virtual int P { get; set; }\n}\n"
                    ] do
                    Expect.equal
                        (stable source Settings.Default)
                        source
                        "A misplaced partial or required keeps its run in source order."

                Expect.equal
                    (stable "static public partial class T { }\n" Settings.Default)
                    "public static partial class T { }\n"
                    "A trailing partial does not stop the sort."
            }
            test
                "stop ModifiersMultiple from sorting across directives, ignore comments, and contextual modifiers" {
                let nullableSource =
                    lines
                        [
                            "class C"
                            "{"
                            "    readonly"
                            "#nullable enable"
                            "    static"
                            "#nullable disable"
                            "    public string? X;"
                            "}"
                        ]

                Expect.equal
                    (stable nullableSource Settings.Default)
                    nullableSource
                    "#nullable between modifiers preserves modifier order."

                let pragmaSource =
                    lines [ "#pragma warning disable CS1591"; "static public class C { }" ]

                Expect.equal
                    (stable pragmaSource Settings.Default)
                    pragmaSource
                    "Leading #pragma before first modifier preserves modifier order."

                let lineAndRegionSource =
                    lines
                        [
                            "class C"
                            "{"
                            "#line 10"
                            "    static public int A;"
                            "    #region R"
                            "    readonly"
                            "    #endregion"
                            "    public int B;"
                            "}"
                        ]

                Expect.equal
                    (stable lineAndRegionSource Settings.Default)
                    lineAndRegionSource
                    "#line and #region in modifier run preserve modifier order."

                let ignoreSource =
                    lines
                        [
                            "class C"
                            "{"
                            "    readonly"
                            "    // csff-ignore-start"
                            "    static"
                            "    // csff-ignore-end"
                            "    public int X = 1;"
                            "}"
                        ]

                let ignoreOut = stable ignoreSource Settings.Default

                let startIdx = ignoreOut.IndexOf("// csff-ignore-start", StringComparison.Ordinal)
                let endIdx = ignoreOut.IndexOf("// csff-ignore-end", StringComparison.Ordinal)

                Expect.isTrue
                    (startIdx >= 0 && endIdx > startIdx)
                    "Ignore markers stay paired in source order."

                Expect.stringContains ignoreOut "readonly\n" "readonly stays before ignore-start."

                Expect.stringContains
                    ignoreOut
                    "    // csff-ignore-end\n    public int X = 1;"
                    "public stays after ignore-end."

                let ctorAsync = "class C\n{\n    async public C() { }\n}\n"

                Expect.equal
                    (stable ctorAsync Settings.Default)
                    ctorAsync
                    "async constructor preserves modifier order instead of becoming method return type."

                let externType = "namespace N\n{\n    extern public class D { }\n}\n"

                Expect.equal
                    (stable externType Settings.Default)
                    externType
                    "extern on type declaration preserves modifier order."

                let methodAsyncPartial =
                    "class C\n{\n    static public async partial Task M() { }\n}\n"

                Expect.equal
                    (stable methodAsyncPartial Settings.Default)
                    methodAsyncPartial
                    "async with partial on method preserves modifier order."

                let validAsyncMethod = "class C\n{\n    async static public Task M() { }\n}\n"

                Expect.equal
                    (stable validAsyncMethod Settings.Default)
                    "class C\n{\n    public static async Task M() { }\n}\n"
                    "Plain async method modifiers still sort cleanly."

                let localFunc =
                    "class C\n{\n    void Outer()\n    {\n        async static void Local() { }\n    }\n}\n"

                Expect.equal
                    (stable localFunc Settings.Default)
                    "class C\n{\n    void Outer()\n    {\n        static async void Local() { }\n    }\n}\n"
                    "Local function with permitted async/static modifiers still sorts cleanly."
            }

            test
                "do not split type-argument, array-rank, or calling-convention commas before a block lambda" {
                let dictShortIn =
                    "class C { void G() { M(typeof(Dictionary<,>), x => { Return(); }); } }\n"

                let dictShortExpected =
                    "class C\n{\n    void G()\n    {\n        M(typeof(Dictionary<,>), x =>\n        {\n            Return();\n        });\n    }\n}\n"

                Expect.equal
                    (stable dictShortIn Settings.Default)
                    dictShortExpected
                    "Short typeof(Dictionary<,>) before block lambda keeps comma intact."

                let dictLongIn =
                    "class C { void G() { VeryLongMethodNameToForceArgumentListBreakAcrossLinesBeyondHundredCols(typeof(Dictionary<,>), x => { Return(); }); } }\n"

                let dictLongExpected =
                    "class C\n{\n    void G()\n    {\n        VeryLongMethodNameToForceArgumentListBreakAcrossLinesBeyondHundredCols(\n            typeof(Dictionary<,>),\n            x =>\n            {\n                Return();\n            }\n        );\n    }\n}\n"

                Expect.equal
                    (stable dictLongIn Settings.Default)
                    dictLongExpected
                    "Broken typeof(Dictionary<,>) keeps type-argument comma attached."

                let arrayIn =
                    "class C { void G() { VeryLongMethodNameThatDefinitelyForcesTheArgumentListBeyondOneHundredColumnsNow(typeof(int[,]), x => { Return(); }); } }\n"

                let arrayExpected =
                    "class C\n{\n    void G()\n    {\n        VeryLongMethodNameThatDefinitelyForcesTheArgumentListBeyondOneHundredColumnsNow(\n            typeof(int[,]),\n            x =>\n            {\n                Return();\n            }\n        );\n    }\n}\n"

                Expect.equal
                    (stable arrayIn Settings.Default)
                    arrayExpected
                    "Broken typeof(int[,]) keeps array-rank comma attached."

                let fnPtrIn =
                    "class C { unsafe void G() { VeryLongMethodNameToForceArgumentListBreakAcrossLinesBeyondHundredCols(typeof(delegate* unmanaged[A, B]<void>), x => { Return(); }); } }\n"

                let fnPtrExpected =
                    "class C\n{\n    unsafe void G()\n    {\n        VeryLongMethodNameToForceArgumentListBreakAcrossLinesBeyondHundredCols(\n            typeof(delegate* unmanaged[A, B]<void>),\n            x =>\n            {\n                Return();\n            }\n        );\n    }\n}\n"

                Expect.equal
                    (stable fnPtrIn Settings.Default)
                    fnPtrExpected
                    "Broken unmanaged calling convention list keeps its comma attached."

                let dictEarlyIn =
                    "class C { void G() { VeryLongMethodNameThatDefinitelyForcesTheArgumentListBeyondOneHundredColumnsNow(typeof(Dictionary<,>), new { A = 1 }, x => { Return(); }); } }\n"

                let dictEarlyExpected =
                    "class C\n{\n    void G()\n    {\n        VeryLongMethodNameThatDefinitelyForcesTheArgumentListBeyondOneHundredColumnsNow(\n            typeof(Dictionary<,>),\n            new\n            {\n                A = 1,\n            },\n            x =>\n            {\n                Return();\n            }\n        );\n    }\n}\n"

                Expect.equal
                    (stable dictEarlyIn Settings.Default)
                    dictEarlyExpected
                    "Early typeof(Dictionary<,>) argument does not misclassify nested type comma."

                let shortEarlyIn =
                    "class C { void G() { M(typeof(Dictionary<,>), new { A = 1 }, x => { Return(); }); } }\n"

                let shortEarlyExpected =
                    "class C\n{\n    void G()\n    {\n        M(\n            typeof(Dictionary<,>),\n            new\n            {\n                A = 1,\n            },\n            x =>\n            {\n                Return();\n            }\n        );\n    }\n}\n"

                Expect.equal
                    (stable shortEarlyIn Settings.Default)
                    shortEarlyExpected
                    "Early typeof(Dictionary<,>) keeps type comma when later argument forces break."
            }

            test
                "check ForeignLiteral in Interpolated so another configuration raw string keeps its value" {
                let outerRawSource =
                    lines
                        [
                            "class C"
                            "{"
                            "    string M()"
                            "    {"
                            "        return"
                            "#if A"
                            "\"\"\"\""
                            "#endif"
                            "          $\"\"\""
                            "            hello {1}"
                            "            \"\"\""
                            "#if A"
                            "\"\"\"\""
                            "#endif"
                            "            ;"
                            "    }"
                            "}"
                        ]

                let outerRawOut = stable outerRawSource Settings.Default

                Expect.stringContains
                    outerRawOut
                    "          $\"\"\"\n            hello {1}\n            \"\"\""
                    "Foreign-owned multiline interpolated raw string keeps its exact source indentation and content."

                let singleLineInsideOuterRaw =
                    lines
                        [
                            "class C"
                            "{"
                            "    string M()"
                            "    {"
                            "        return"
                            "#if A"
                            "\"\"\"\""
                            "#endif"
                            "          $\"val={1 + 2}\""
                            "#if A"
                            "\"\"\"\""
                            "#endif"
                            "            ;"
                            "    }"
                            "}"
                        ]

                let singleLineOut = stable singleLineInsideOuterRaw Settings.Default

                Expect.stringContains
                    singleLineOut
                    "          $\"val={1 + 2}\""
                    "Foreign-owned interpolated string inside another configuration's raw literal keeps exact bytes."
            }

            test
                "keep a space between a keyword and a following tuple type or string literal in Spaced" {
                let source =
                    lines
                        [
                            "static class C"
                            "{"
                            "    public C() { }"
                            "    public C(int a) : this() { }"
                            "    public static void Ext(this (int A, int B) x) { }"
                            "    public static void ScopedExt(this scoped (int A, int B) x) { }"
                            "    public static void ScopedOnly(scoped (int A, int B) x) { }"
                            "    public static ref readonly (int A, int B) RefRo(ref readonly (int A, int B) x) => ref x;"
                            "    public static object Query(int[] items, string[] other) =>"
                            "        from (int A, int B) t in items"
                            "        join (int C, int D) y in other on \"k1\" equals \"k2\""
                            "        orderby \"k\" descending, 'a' ascending"
                            "        group \"v\" by \"k\";"
                            "}"
                        ]

                let formatted = stable source Settings.Default

                Expect.stringContains
                    formatted
                    ": this() { }"
                    "Constructor this initializer keeps no space before ()."

                Expect.stringContains
                    formatted
                    "Ext(this (int A, int B) x)"
                    "this parameter keeps space before tuple type."

                Expect.stringContains
                    formatted
                    "ScopedExt(this scoped (int A, int B) x)"
                    "this scoped keeps space before tuple type."

                Expect.stringContains
                    formatted
                    "ScopedOnly(scoped (int A, int B) x)"
                    "scoped parameter keeps space before tuple type."

                Expect.stringContains
                    formatted
                    "ref readonly (int A, int B) RefRo"
                    "ref readonly return keeps space before tuple type."

                Expect.stringContains
                    formatted
                    "RefRo(ref readonly (int A, int B) x)"
                    "ref readonly parameter keeps space before tuple type."

                Expect.stringContains
                    formatted
                    "from (int A, int B) t in items"
                    "from keeps space before tuple type."

                Expect.stringContains
                    formatted
                    "join (int C, int D) y in other"
                    "join keeps space before tuple type."

                Expect.stringContains
                    formatted
                    "on \"k1\" equals \"k2\""
                    "on and equals keep spaces around string literals."

                Expect.stringContains
                    formatted
                    "orderby \"k\" descending, 'a' ascending"
                    "ascending and descending keep spaces after literals."

                Expect.stringContains
                    formatted
                    "group \"v\" by \"k\";"
                    "group and by keep spaces around string literals."
            }

            test
                "keep Shared slices and StartIfBreak group IDs valid across DocumentBuffer Remove, Insert and AppendGroups" {
                use doc = new DocumentBuffer()
                doc.AddText("ab", 0, 2)
                doc.AddText("cd", 0, 2)
                doc.AddText("ef", 0, 2)
                doc.AddShared(1, 2)
                doc.Remove 0
                Expect.equal doc.Storage[2].A 0 "Remove before Shared shifts start."
                Expect.equal doc.Storage[2].B 2 "Remove before Shared keeps length."
                doc.Remove 1
                Expect.equal doc.Storage[1].A 0 "Remove inside Shared keeps start."
                Expect.equal doc.Storage[1].B 1 "Remove inside Shared shrinks length."

                doc.Insert(
                    0,
                    {
                        Kind = ElementKind.StaticToken
                        Flags = 0uy
                        Tail = 0uy
                        Facts = 0uy
                        Width = 1u
                        A = int StaticToken.Space
                        B = 0
                    }
                )

                Expect.equal doc.Storage[2].A 1 "Insert at/before Shared shifts start."
                Expect.equal doc.Storage[2].B 1 "Insert before Shared preserves length."
                use sliceDoc = new DocumentBuffer()
                sliceDoc.AddText("aa", 0, 2)
                sliceDoc.AddText("bb", 0, 2)
                sliceDoc.AddShared(0, 2)

                sliceDoc.Insert(
                    1,
                    {
                        Kind = ElementKind.StaticToken
                        Flags = 0uy
                        Tail = 0uy
                        Facts = 0uy
                        Width = 1u
                        A = int StaticToken.Space
                        B = 0
                    }
                )

                Expect.equal sliceDoc.Storage[3].A 0 "Insert strictly inside Shared keeps start."
                Expect.equal sliceDoc.Storage[3].B 3 "Insert strictly inside Shared grows length."

                use src = new DocumentBuffer()
                let outerGroup = src.StartGroup()
                src.AddText("prefix", 0, 6)
                src.AddTag(Tag.EndGroup)
                src.AddText("before", 0, 6)
                let copyStart = src.Count
                let innerGroup = src.StartGroup()
                src.AddTag(Tag.StartIfBreak, outerGroup)
                src.AddText("in", 0, 2)
                src.AddTag Tag.EndIfBreak
                src.AddTag(Tag.StartIfBreak, innerGroup)
                src.AddTag Tag.EndIfBreak
                src.AddTag Tag.EndGroup
                src.AddShared(1, 1)
                src.AddShared(copyStart + 2, 1)
                let copyLen = src.Count - copyStart

                use dst = new DocumentBuffer()
                let _ = dst.StartGroup()
                let _ = dst.StartGroup()
                dst.AddTag Tag.EndGroup
                dst.AddTag Tag.EndGroup
                dst.Append(src, copyStart, copyLen)

                let copiedInnerId = dst.Storage[4].A

                Expect.equal
                    dst.Storage[5].A
                    outerGroup
                    "Out-of-range StartIfBreak keeps its original ID."

                Expect.equal
                    dst.Storage[8].A
                    copiedInnerId
                    "In-range StartIfBreak uses remapped inner group ID."

                Expect.equal dst.Storage[11].A 1 "Pre-start Shared slice keeps its original offset."

                Expect.equal
                    dst.Storage[12].A
                    (4 + 2)
                    "In-range Shared slice shifts by destination offset."
            }

            test
                "keep forced-break groups when an AddShared slice recorded under StartForceFlat is replayed" {
                let ternarySource =
                    lines
                        [
                            "class C"
                            "{"
                            "    string M()"
                            "    {"
                            "        return Check([[1, 2], [3, 4]], veryLongArgumentNameThatForcesTernaryConditionOverHundredColumns) != null ? \"first\" : \"second\";"
                            "    }"
                            "}"
                        ]

                let ternaryExpected =
                    lines
                        [
                            "class C"
                            "{"
                            "    string M()"
                            "    {"
                            "        return"
                            "            Check("
                            "                ["
                            "                    [1, 2],"
                            "                    [3, 4],"
                            "                ],"
                            "                veryLongArgumentNameThatForcesTernaryConditionOverHundredColumns"
                            "            ) != null"
                            "            ? \"first\""
                            "            : \"second\";"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable ternarySource Settings.Default)
                    ternaryExpected
                    "Detached ternary condition replayed via AddShared preserves nested collection forced break."

                let lambdaSource =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        Run(async x => await CreateAsync(argumentOne, argumentTwo, argumentThree, new Item { Alpha = 1, Beta = 2, Gamma = 3 }));"
                            "    }"
                            "}"
                        ]

                let lambdaExpected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        Run(async x =>"
                            "            await CreateAsync("
                            "                argumentOne,"
                            "                argumentTwo,"
                            "                argumentThree,"
                            "                new Item"
                            "                {"
                            "                    Alpha = 1,"
                            "                    Beta = 2,"
                            "                    Gamma = 3,"
                            "                }"
                            "            )"
                            "        );"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable lambdaSource Settings.Default)
                    lambdaExpected
                    "Detached await lambda body replayed via AddShared preserves object-initializer forced break."
            }

            test "honor csff-ignore and foreign-configuration nodes on right side of coalesce chain" {
                let ignoreChain =
                    lines
                        [
                            "class C"
                            "{"
                            "    object M(object a, object b, object c)"
                            "    {"
                            "        return a ??"
                            "        // csff-ignore"
                            "        b   ??   c;"
                            "    }"
                            "}"
                        ]

                let ignoreOut = stable ignoreChain Settings.Default

                Expect.stringContains
                    ignoreOut
                    "// csff-ignore\n        b   ??   c;"
                    "Ignored right-side CoalesceExpression preserves exact tokens and spacing."

                let deeperChain =
                    lines
                        [
                            "class C"
                            "{"
                            "    object M(object a, object b, object c, object d)"
                            "    {"
                            "        return a ?? b ??"
                            "        // csff-ignore"
                            "        c   ??   d;"
                            "    }"
                            "}"
                        ]

                let deeperOut = stable deeperChain Settings.Default

                Expect.stringContains
                    deeperOut
                    "// csff-ignore\n        c   ??   d;"
                    "Deeper ignored right-side CoalesceExpression in a chain is preserved."

                let foreignCoalesce =
                    lines
                        [
                            "#if !B && !C"
                            "class Broken {"
                            "#endif"
                            "class C"
                            "{"
                            "    string M(string a, string b, string c)"
                            "    {"
                            "        return a"
                            "            ??"
                            "#if B"
                            "            @\""
                            "#endif"
                            "            b   ??   c"
                            "#if B"
                            "            \""
                            "#endif"
                            "        ;"
                            "    }"
                            "}"
                        ]

                let foreignOut = stable foreignCoalesce Settings.Default

                Expect.stringContains
                    foreignOut
                    "            b   ??   c"
                    "Foreign-owned right-side CoalesceExpression keeps exact spacing for alternate verbatim literal."

                let foreignDepth3 =
                    lines
                        [
                            "#if !B && !C"
                            "class Broken {"
                            "#endif"
                            "class C"
                            "{"
                            "    string M(string a, string b, string c, string d)"
                            "    {"
                            "        return a ?? b"
                            "            ??"
                            "#if B"
                            "            @\""
                            "#endif"
                            "            c   ??   d"
                            "#if B"
                            "            \""
                            "#endif"
                            "        ;"
                            "    }"
                            "}"
                        ]

                let foreignDepth3Out = stable foreignDepth3 Settings.Default

                Expect.stringContains
                    foreignDepth3Out
                    "        return a\n            ?? b\n            ??"
                    "Leading outer coalesce nodes still format normally before a foreign right-side chain."

                Expect.stringContains
                    foreignDepth3Out
                    "            c   ??   d"
                    "Deeper foreign-owned right-side CoalesceExpression keeps exact spacing for alternate verbatim literal."

                let partialRangeEntry =
                    lines
                        [
                            "class C"
                            "{"
                            "    object M(object a, object b, object c)"
                            "    {"
                            "        return a ??"
                            "        // csff-ignore-start"
                            "        b ??"
                            "        // csff-ignore-end"
                            "        c;"
                            "    }"
                            "}"
                        ]

                let partialEntryOut = stable partialRangeEntry Settings.Default

                Expect.stringContains
                    partialEntryOut
                    "// csff-ignore-start"
                    "Partial ignore range at chain entry keeps start marker."

                Expect.stringContains
                    partialEntryOut
                    "// csff-ignore-end"
                    "Partial ignore range at chain entry keeps end marker."

                let partialRangeDeeper =
                    lines
                        [
                            "class C"
                            "{"
                            "    object M(object a, object b, object c, object d)"
                            "    {"
                            "        return a ?? b ??"
                            "        // csff-ignore-start"
                            "        c ??"
                            "        // csff-ignore-end"
                            "        d;"
                            "    }"
                            "}"
                        ]

                let partialDeeperOut = stable partialRangeDeeper Settings.Default

                Expect.stringContains
                    partialDeeperOut
                    "// csff-ignore-start"
                    "Partial ignore range deeper in chain keeps start marker."

                Expect.stringContains
                    partialDeeperOut
                    "// csff-ignore-end"
                    "Partial ignore range deeper in chain keeps end marker."
            }

            test
                "Cli edge cases: alwaysIgnored casing, bare relative filenames, stdin auto-generated check, duplicate %TAG, and 0X hex scalars" {
                let write root rel (content: string) =
                    let p = Path.Combine(root, rel)
                    Directory.CreateDirectory(Path.GetDirectoryName p) |> ignore
                    File.WriteAllText(p, content)
                    p

                withDirectory (fun root ->
                    let configPath = write root ".csffrc.json" "{\"indentSize\":2}\n"
                    ignore configPath
                    let barePath = write root "BareRelative.cs" "class C{int x;}\n"
                    ignore barePath

                    let originalDirectory = Environment.CurrentDirectory

                    try
                        Environment.CurrentDirectory <- root

                        let settings =
                            Discovery.settingsForFile "BareRelative.cs" None
                            |> Option.defaultWith (fun () ->
                                failtest "Expected settings for bare filename.")

                        Expect.equal
                            settings.Printer.IndentSize
                            2
                            "Discovery.settingsForFile resolves bare filename against current directory."

                        let discovered = Discovery.files [| "BareRelative.cs" |] None None false 1

                        Expect.equal
                            discovered.Length
                            1
                            "Discovery.files accepts bare relative filenames."

                        Expect.equal
                            discovered[0].Settings.Printer.IndentSize
                            2
                            "Discovery.files loads directory configuration for bare relative filenames."
                    finally
                        Environment.CurrentDirectory <- originalDirectory

                    write root "Bin/Ignored.cs" "class BinIgnored {}\n" |> ignore
                    write root "OBJ/Ignored.cs" "class ObjIgnored {}\n" |> ignore
                    write root ".GIT/Ignored.cs" "class GitIgnored {}\n" |> ignore
                    write root "Keep/Kept.cs" "class Kept {}\n" |> ignore

                    let walked = Discovery.files [| root |] None None false 1
                    let relPaths = walked |> Array.map (fun f -> Path.GetFileName f.Path)

                    if OperatingSystem.IsWindows() || OperatingSystem.IsMacOS() then
                        Expect.equal
                            (Array.sort relPaths)
                            [| "BareRelative.cs"; "Kept.cs" |]
                            "Bin, OBJ, and .GIT are always ignored case-insensitively on Windows and macOS."
                        |> ignore
                    else
                        Expect.contains
                            (Array.toList relPaths)
                            "Ignored.cs"
                            "Case-distinct directory names remain included on Linux."

                    let binExplicit =
                        Discovery.files
                            [| Path.Combine(root, "Bin/Ignored.cs") |]
                            None
                            None
                            false
                            1

                    if OperatingSystem.IsWindows() || OperatingSystem.IsMacOS() then
                        Expect.equal
                            binExplicit.Length
                            0
                            "Explicit file inside Bin/ is also excluded on Windows and macOS."

                    let savedIn = Console.In
                    let savedOut = Console.Out
                    let savedErr = Console.Error

                    let runStdin args input =
                        use outW = new StringWriter()
                        use errW = new StringWriter()

                        try
                            Console.SetIn(new StringReader(input))
                            Console.SetOut outW
                            Console.SetError errW
                            let code = Program.run args
                            code, outW.ToString(), errW.ToString()
                        finally
                            Console.SetIn savedIn
                            Console.SetOut savedOut
                            Console.SetError savedErr

                    let genSrc = "// <auto-generated />\nclass G{int x;}\n"
                    let code1, out1, _ = runStdin [| "--write-stdout"; "-" |] genSrc

                    Expect.equal
                        code1
                        2
                        "Stdin --write-stdout refuses auto-generated source by default."

                    Expect.equal out1 "" "Refused auto-generated stdin writes nothing to stdout."

                    let code2, out2, _ =
                        runStdin [| "--write-stdout"; "--include-generated"; "-" |] genSrc

                    Expect.equal
                        code2
                        0
                        "Stdin --write-stdout formats auto-generated source with --include-generated."

                    Expect.stringContains
                        out2
                        "int x;"
                        "Formatted auto-generated stdin reaches stdout.")

                Expect.throws
                    (fun () ->
                        Yaml.parse "test.yaml" "%TAG ! !a!\n%TAG ! !b!\n---\na: 1\n" |> ignore)
                    "Duplicate %TAG ! directive is rejected."

                Expect.throws
                    (fun () ->
                        Yaml.parse "test.yaml" "%TAG !! tag:a/\n%TAG !! tag:b/\n---\na: 1\n"
                        |> ignore)
                    "Duplicate %TAG !! directive is rejected."

                withDirectory (fun root ->
                    let cfgPath =
                        write root ".csffrc.yaml" "printWidth: !!int +0X50\nindentSize: 0X04\n"

                    let cfg = Configuration.read cfgPath
                    Expect.equal cfg.Settings.Printer.Width 80 "!!int +0X50 parses as 80."
                    Expect.equal cfg.Settings.Printer.IndentSize 4 "untagged 0X04 parses as 4.")

                use doc =
                    System.Text.Json.JsonDocument.Parse(
                        Configuration.yamlJson "test.yaml" "w: 0X50\nbig: 0XFFFFFFFFFFFFFFB0\n"
                    )

                Expect.equal
                    (doc.RootElement.GetProperty("w").GetInt64())
                    80L
                    "Untagged 0X50 parses as hex."

                Expect.equal
                    (doc.RootElement.GetProperty("big").GetUInt64())
                    0xFFFFFFFFFFFFFFB0UL
                    "Untagged 0XFFFFFFFFFFFFFFB0 keeps unsigned 64-bit magnitude."
            }

            test
                "SyntaxDocumentBuilder.MaxOutputLength enforces limit without an external Printer and across conditional passes" {
                let singleExpanded =
                    "class C { int M() => "
                    + String.replicate 40 "F(1, "
                    + "1"
                    + String.replicate 40 ")"
                    + "; }"

                let singleTree = Csff.Parser.SyntaxTree()
                Parser.parse singleExpanded singleTree

                use ownedSyntax = new SyntaxDocumentBuilder()
                ownedSyntax.MaxOutputLength <- 200
                use doc1 = new DocumentBuffer()

                Expect.throwsT<VerificationLimitException>
                    (fun () ->
                        ownedSyntax.BuildAndPrint(
                            singleExpanded,
                            singleTree,
                            doc1,
                            PrinterOptions.Default
                        ))
                    "Owned-printer BuildAndPrint honors SyntaxDocumentBuilder.MaxOutputLength."

                use doc1Build = new DocumentBuffer()

                let singleNested =
                    "class C { int M() => "
                    + String.replicate 120 "F("
                    + "1"
                    + String.replicate 120 ")"
                    + "; }"

                let singleNestedTree = Csff.Parser.SyntaxTree()
                Parser.parse singleNested singleNestedTree

                ownedSyntax.MaxOutputLength <- Array.MaxLength
                ownedSyntax.Build(singleNested, singleNestedTree, doc1Build, PrinterOptions.Default)
                Expect.isGreaterThan doc1Build.Count 0 "Unlimited Build succeeds on singleNested."

                ownedSyntax.MaxOutputLength <- 200

                Expect.throwsT<VerificationLimitException>
                    (fun () ->
                        ownedSyntax.Build(
                            singleNested,
                            singleNestedTree,
                            doc1Build,
                            PrinterOptions.Default
                        ))
                    "Owned-printer Build honors SyntaxDocumentBuilder.MaxOutputLength even when renderFinal is false."

                let multiSource =
                    "#if A\nclass A { }\n#else\nclass B { int M() => "
                    + String.replicate 40 "F(1, "
                    + "1"
                    + String.replicate 40 ")"
                    + "; }\n#endif\n"

                let multiTree = Csff.Parser.SyntaxTree()
                Parser.parse multiSource multiTree

                use sharedPrinter = new Printer()
                use multiSyntax = new SyntaxDocumentBuilder(sharedPrinter)
                multiSyntax.MaxOutputLength <- 200
                use doc2 = new DocumentBuffer()

                Expect.throwsT<VerificationLimitException>
                    (fun () ->
                        multiSyntax.BuildAndPrint(
                            multiSource,
                            multiTree,
                            doc2,
                            PrinterOptions.Default
                        ))
                    "Multi-configuration Pass 2+ and final verification preserve SyntaxDocumentBuilder.MaxOutputLength even with an unlimited shared Printer."

                Expect.equal
                    sharedPrinter.MaxOutputLength
                    Array.MaxLength
                    "Shared Printer.MaxOutputLength is restored after SyntaxDocumentBuilder.BuildAndPrint aborts."
            }

            test "accessor body and accessor list closing comments indent with inner items" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    bool P"
                            "    {"
                            "        get"
                            "        {"
                            "            return false;"
                            "            // not seekable yet"
                            "        }"
                            "        // after get"
                            "    }"
                            "    int Q"
                            "    {"
                            "        get;"
                            "        // auto accessor comment"
                            "    }"
                            "    int R"
                            "    {"
                            "        get"
                            "        {"
                            "            // empty accessor comment"
                            "        }"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    source
                    "Comments before closing braces of accessor bodies and accessor lists stay indented inside the block."
            }

            test "accessor list with attribute expands when pushing line over width" {
                let source =
                    lines
                        [
                            "interface I"
                            "{"
                            "    IHubClients<T> Clients { [RequiresDynamicCode(\"Creating a proxy instance requires generating code at runtime\")] get; }"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "interface I"
                            "{"
                            "    IHubClients<T> Clients"
                            "    {"
                            "        [RequiresDynamicCode(\"Creating a proxy instance requires generating code at runtime\")]"
                            "        get;"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Decorated auto-property accessor list expands rather than overflowing width."
            }

            test
                "conditional access chain A.B?.C(args) keeps receiver attached when arguments break" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        LogContext.Warning?.Log(retryContext.Exception, \"Retrying {Delay}: {Message}\", retryContext.Delay, retryContext.Exception.Message);"
                            "    }"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        LogContext.Warning?.Log("
                            "            retryContext.Exception,"
                            "            \"Retrying {Delay}: {Message}\","
                            "            retryContext.Delay,"
                            "            retryContext.Exception.Message"
                            "        );"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "A.B?.C(args) stays together on the head line like A.B.C(args)."
            }

            test "predefined type keeps first call attached at head of chain" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        var url = string.Format(NopCommonDefaults.NopInstallationCompletedPath, NopVersion.FULL_VERSION, isLocal).ToLowerInvariant();"
                            "    }"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        var url = string.Format("
                            "                NopCommonDefaults.NopInstallationCompletedPath,"
                            "                NopVersion.FULL_VERSION,"
                            "                isLocal"
                            "            )"
                            "            .ToLowerInvariant();"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Predefined keyword type string stays attached to .Format(...) at head of chain."
            }

            test "property pattern without type stays flat after broken is when it fits" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        if (frames.Count > 0 && renderTreeStackOfSomeLongName.PeekTheTopMostElementOfTheStack(position) is { IsVirtualize: true } virtualizeFrame && ok)"
                            "        {"
                            "            return;"
                            "        }"
                            "    }"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        if ("
                            "            frames.Count > 0"
                            "            && renderTreeStackOfSomeLongName.PeekTheTopMostElementOfTheStack(position)"
                            "                is { IsVirtualize: true } virtualizeFrame"
                            "            && ok"
                            "        )"
                            "        {"
                            "            return;"
                            "        }"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Bare property pattern stays flat on its broken is line when it fits."
            }

            test "base list and constraint comma stay on their line when directive sits in header" {
                let source =
                    lines
                        [
                            "namespace N"
                            "{"
                            "#if !BUILDTASK"
                            "    public"
                            "#endif"
                            "    class ExpressionParseException : Exception { }"
                            ""
                            "    internal class ClientOperationCollection :"
                            "#if MOBILE"
                            "        KeyedCollection<string, ClientOperation>"
                            "#else"
                            "        SynchronizedKeyedCollection<string, ClientOperation>"
                            "#endif"
                            "    { }"
                            ""
                            "    public interface IFoo<T>"
                            "        where T : IComparable<T>"
                            "#if NET9_0_OR_GREATER"
                            "            , allows ref struct"
                            "#endif"
                            "    { }"
                            ""
                            "    public interface IBar<T>"
                            "        where T : IComparable<T>,"
                            "#if NET9_0_OR_GREATER"
                            "            allows ref struct"
                            "#endif"
                            "    { }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    source
                    "Directives in declaration headers, base lists, or constraint clauses do not strand ':' or ',' alone."

                let overflowAfterDirective =
                    lines
                        [
                            "#if !BUILDTASK"
                            "public"
                            "#endif"
                            "class VeryLongExpressionParseExceptionNameThatExceedsTheHundredColumnLineLimitHere : VeryLongBaseException { }"
                        ]

                let overflowExpected =
                    lines
                        [
                            "#if !BUILDTASK"
                            "public"
                            "#endif"
                            "class VeryLongExpressionParseExceptionNameThatExceedsTheHundredColumnLineLimitHere"
                            "    : VeryLongBaseException { }"
                        ]

                Expect.equal
                    (stable overflowAfterDirective Settings.Default)
                    overflowExpected
                    "Long header after leading directive still breaks before ':' when exceeding width."

                let shortCommaBase =
                    lines
                        [
                            "class Derived :"
                            "#if MOBILE"
                            "    IFirst,"
                            "        ISecond"
                            "#else"
                            "    IShort"
                            "#endif"
                            "{ }"
                        ]

                let shortCommaExpected =
                    lines
                        [
                            "class Derived :"
                            "#if MOBILE"
                            "    IFirst, ISecond"
                            "#else"
                            "    IShort"
                            "#endif"
                            "{ }"
                        ]

                Expect.equal
                    (stable shortCommaBase Settings.Default)
                    shortCommaExpected
                    "Fitting base list with directive keeps ':' on the header line."

                let splitCommaBase =
                    lines
                        [
                            "class Derived :"
                            "#if MOBILE"
                            "    IFirstVeryLongBaseInterfaceNameHere, ISecondVeryLongBaseInterfaceNameHere, IThirdVeryLongBaseInterfaceNameHere"
                            "#else"
                            "    IShort"
                            "#endif"
                            "{ }"
                        ]

                let splitCommaExpected =
                    lines
                        [
                            "class Derived"
                            "    :"
                            "#if MOBILE"
                            "    IFirstVeryLongBaseInterfaceNameHere,"
                            "        ISecondVeryLongBaseInterfaceNameHere,"
                            "        IThirdVeryLongBaseInterfaceNameHere"
                            "#else"
                            "    IShort"
                            "#endif"
                            "{ }"
                        ]

                Expect.equal
                    (stable splitCommaBase Settings.Default)
                    splitCommaExpected
                    "Multiple long base types break before ':' when exceeding width while keeping commas unwrapped past directives."
            }

            test
                "generic field declaration breaks after equals before breaking declared type arguments" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    private ImmutableDictionary<string, ExtensionFolder> _folderPathToExtensionFolder = ImmutableDictionary<string, ExtensionFolder>.Empty;"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    private ImmutableDictionary<string, ExtensionFolder> _folderPathToExtensionFolder ="
                            "        ImmutableDictionary<string, ExtensionFolder>.Empty;"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Generic field declaration keeps declared type arguments flat and breaks after '='."

                let propertyPin =
                    lines
                        [
                            "class P"
                            "{"
                            "    public static Dictionary<string, (Type type, Stream stream)> ActivatorWithoutDrawingVeryLongName { get; } = new D();"
                            "}"
                        ]

                let propertyExpected =
                    lines
                        [
                            "class P"
                            "{"
                            "    public static Dictionary<"
                            "        string,"
                            "        (Type type, Stream stream)"
                            "    > ActivatorWithoutDrawingVeryLongName { get; } = new D();"
                            "}"
                        ]

                Expect.equal
                    (stable propertyPin Settings.Default)
                    propertyExpected
                    "Auto-property with generic type and non-generic initializer still preserves its pinned layout."

                let rhsGenericMemberPin =
                    lines
                        [
                            "class M"
                            "{"
                            "    void F()"
                            "    {"
                            "        param4.m_aguiGeneric1 = new AA<sbyte, byte, uint, uint, long, bool, string, object, decimal>().m_aguiGeneric1;"
                            "    }"
                            "}"
                        ]

                let rhsGenericMemberExpected =
                    lines
                        [
                            "class M"
                            "{"
                            "    void F()"
                            "    {"
                            "        param4.m_aguiGeneric1 = new AA<"
                            "            sbyte,"
                            "            byte,"
                            "            uint,"
                            "            uint,"
                            "            long,"
                            "            bool,"
                            "            string,"
                            "            object,"
                            "            decimal"
                            "        >().m_aguiGeneric1;"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable rhsGenericMemberPin Settings.Default)
                    rhsGenericMemberExpected
                    "Assignment with generic creation member RHS still preserves its pinned layout."

                let overflowingRhsSource =
                    lines
                        [
                            "class W"
                            "{"
                            "    ImmutableDictionary<string, ExtensionFolder> d = ImmutableDictionary<string, ExtensionFolderWithAReallyLongSecondTypeArgumentThatOverflowsEvenOnNextLine>.Empty;"
                            "}"
                        ]

                let overflowingRhsExpected =
                    lines
                        [
                            "class W"
                            "{"
                            "    ImmutableDictionary<string, ExtensionFolder> d ="
                            "        ImmutableDictionary<"
                            "            string,"
                            "            ExtensionFolderWithAReallyLongSecondTypeArgumentThatOverflowsEvenOnNextLine"
                            "        >.Empty;"
                            "}"
                        ]

                Expect.equal
                    (stable overflowingRhsSource Settings.Default)
                    overflowingRhsExpected
                    "Detached generic static-member initializer still expands when the continuation line overflows."

                let narrowSource =
                    lines
                        [
                            "class N"
                            "{"
                            "    ImmutableDictionary<string, object> d = ImmutableDictionary<string, object>.Empty;"
                            "}"
                        ]

                let narrowExpected =
                    lines
                        [
                            "class N"
                            "{"
                            "    ImmutableDictionary<"
                            "        string,"
                            "        object"
                            "    > d ="
                            "        ImmutableDictionary<"
                            "            string,"
                            "            object"
                            "        >.Empty;"
                            "}"
                        ]

                Expect.equal
                    (stable
                        narrowSource
                        { Settings.Default with
                            Printer =
                                { Settings.Default.Printer with
                                    Width = 40
                                }
                        })
                    narrowExpected
                    "Both declared and detached generic static-member type arguments expand at width 40."
            }

            test
                "initializers inside lambdas expand rather than moving flat braces onto the next line" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    async Task M()"
                            "    {"
                            "        var q = AssertQuery("
                            "            ss => ss.Set<NumberTypesEntity>().Select(e => new { e.Id, Value = (byte)(e.SByte / (e.SByte - 1)) }),"
                            "            x => x.Id"
                            "        );"
                            "        await Check(async () => await Run(first, new Options { Count = 5, Factory = _ => throw new FormatException(), Other = 12 }));"
                            "        await Check(async () => await Run(new Options { Count = 5 }));"
                            "        await Check(() => Run(new Options { Count = 5 }));"
                            "        await Check(async () => await Run(x.Bar + 1));"
                            "    }"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    async Task M()"
                            "    {"
                            "        var q = AssertQuery("
                            "            ss =>"
                            "                ss.Set<NumberTypesEntity>()"
                            "                    .Select(e => new"
                            "                    {"
                            "                        e.Id,"
                            "                        Value = (byte)(e.SByte / (e.SByte - 1)),"
                            "                    }),"
                            "            x => x.Id"
                            "        );"
                            "        await Check(async () =>"
                            "            await Run("
                            "                first,"
                            "                new Options"
                            "                {"
                            "                    Count = 5,"
                            "                    Factory = _ => throw new FormatException(),"
                            "                    Other = 12,"
                            "                }"
                            "            )"
                            "        );"
                            "        await Check(async () =>"
                            "            await Run("
                            "                new Options"
                            "                {"
                            "                    Count = 5,"
                            "                }"
                            "            )"
                            "        );"
                            "        await Check(() =>"
                            "            Run("
                            "                new Options"
                            "                {"
                            "                    Count = 5,"
                            "                }"
                            "            )"
                            "        );"
                            "        await Check(async () => await Run(x.Bar + 1));"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Lambdas with nested anonymous or object initializers expand instead of flattening braces."

                let commentSource =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        Test(x => x, static () => new { Value = /*keep*/ 1 });"
                            "    }"
                            "}"
                        ]

                let commentExpected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        Test("
                            "            x => x,"
                            "            static () =>"
                            "                new"
                            "                {"
                            "                    Value = /*keep*/"
                            "                    1,"
                            "                }"
                            "        );"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable
                        commentSource
                        { Settings.Default with
                            Printer =
                                { Settings.Default.Printer with
                                    Width = 40
                                }
                        })
                    commentExpected
                    "Static lambda alternative preserves comments by emitting its body once."

                let mutable nested = "new { A = 1 }"

                for _ = 1 to 14 do
                    nested <- $"Run(x => x, static () => {nested})"

                let nestedSource = $"class C {{ void M() {{ {nested}; }} }}\n"
                ignore (stable nestedSource Settings.Default)
            }

            test
                "breaks long assignments, type-parameter attributes, is-patterns, and chains cleanly" {
                let assertMaxLineLength (label: string) (output: string) =
                    for line in output.Split('\n') do
                        Expect.isLessThanOrEqual
                            line.Length
                            Settings.Default.Printer.Width
                            $"{label}: line exceeded width {Settings.Default.Printer.Width}: {line}"

                let nonGenericDefault =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        var veryLongCancellationTokenVariableForDefault = default(System.Threading.CancellationTokenWithLongName);"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "non-generic default" nonGenericDefault

                Expect.stringContains
                    nonGenericDefault
                    "        var veryLongCancellationTokenVariableForDefault =\n            default(System.Threading.CancellationTokenWithLongName);\n"
                    "Long non-generic default(T) should break after '='."

                let genericDefault =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        var builder = default(ArrayBuilder<KeyValuePair<string, VeryLongGenericTypeArgumentNameForTesting>>);"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                Expect.stringContains
                    genericDefault
                    "        var builder = default(ArrayBuilder<\n"
                    "Long generic default(T<...>) should continue breaking inside generic arguments."

                let longConditionalAssignment =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M(object? _reuseDispatcherSynchronizationContextInstance, object? currentValue)"
                                "    {"
                                "        _reuseDispatcherSynchronizationContextInstance = currentValue != null ? currentValue : new object();"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "conditional assignment" longConditionalAssignment

                Expect.stringContains
                    longConditionalAssignment
                    "        _reuseDispatcherSynchronizationContextInstance =\n            currentValue != null ? currentValue : new object();\n"
                    "Long conditional assignment should break after '='."

                let csf224Ternary =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    int M(bool flag)"
                                "    {"
                                "        var result = flag"
                                "            ? FirstVeryLongMethodCallToForceTernaryExpansion(1, 2, 3)"
                                "            : SecondVeryLongMethodCallToForceTernaryExpansion(4, 5, 6);"
                                "        return result;"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                Expect.stringContains
                    csf224Ternary
                    "        var result = flag\n            ? FirstVeryLongMethodCallToForceTernaryExpansion(1, 2, 3)\n            : SecondVeryLongMethodCallToForceTernaryExpansion(4, 5, 6);\n"
                    "Multiline ternary on short assignment LHS should stay attached on LHS line."

                let propertyLambda =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    public Action<string> AfterPlatformServicesSetupCallback { get; set; } = serviceName => HandleSetup(serviceName);"
                                "    public Action<string> AfterPlatformServicesSetupCallbackWithVeryLongName { get; set; } = serviceName => HandleSetup(serviceName);"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "property lambda initializer" propertyLambda

                Expect.stringContains
                    propertyLambda
                    "    public Action<string> AfterPlatformServicesSetupCallback { get; set; } = serviceName =>\n        HandleSetup(serviceName);\n"
                    "Fitting property lambda head should break after '=>'."

                Expect.stringContains
                    propertyLambda
                    "    public Action<string> AfterPlatformServicesSetupCallbackWithVeryLongName { get; set; } =\n        serviceName => HandleSetup(serviceName);\n"
                    "Overflowing property lambda head should break after '='."

                let blockLambdaAssignment =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        Action<int> handler = (veryLongParameterNameForTestingBlockLambdaAssignment) => { DoWork(veryLongParameterNameForTestingBlockLambdaAssignment); };"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                Expect.stringContains
                    blockLambdaAssignment
                    "        Action<int> handler = (veryLongParameterNameForTestingBlockLambdaAssignment) =>\n        {\n"
                    "Block lambda assignment should keep '=> {' breaking."

                let longDelegateProperty =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    public Action<string> AfterPlatformServicesSetupDelegateWithLongName { get; set; } = delegate(string serviceName) { HandleSetup(serviceName); };"
                                "    public Action<string> AfterPlatformServicesSetupDelegateWithVeryLongPropertyName { get; set; } = delegate(string serviceName) { HandleSetup(serviceName); };"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "delegate property initializer" longDelegateProperty

                Expect.stringContains
                    longDelegateProperty
                    "    public Action<string> AfterPlatformServicesSetupDelegateWithLongName { get; set; } = delegate(\n        string serviceName\n    )\n"
                    "Fitting delegate head should break parameter list while staying within width."

                Expect.stringContains
                    longDelegateProperty
                    "    public Action<string> AfterPlatformServicesSetupDelegateWithVeryLongPropertyName { get; set; } =\n        delegate(string serviceName)\n        {\n"
                    "Overflowing delegate property initializer should break after '='."

                let wrappedCallBreak =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M(bool c)"
                                "    {"
                                "        F(x = () => { return 1; });"
                                "        F(x = c ? new Y { A = 1 } : new Y { A = 2 });"
                                "        F(x = () => new Y { A = 1 });"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                Expect.stringContains
                    wrappedCallBreak
                    "        F(\n            x = () =>\n            {\n                return 1;\n            }\n        );\n"
                    "Block lambda assignment inside call argument should still break enclosing call."

                Expect.stringContains
                    wrappedCallBreak
                    "        F(\n            x = c\n                ? new Y\n                {\n"
                    "Initialized conditional assignment inside call argument should still break enclosing call."

                Expect.stringContains
                    wrappedCallBreak
                    "        F(\n            x = () => new Y\n            {\n                A = 1,\n            }\n        );\n"
                    "Initialized lambda assignment inside call argument should still break enclosing call."

                let nullForgivingChain =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        var serviceProvider = _veryLongConfigurationProviderField!.GetRequiredServiceProvider().BuildServiceProvider();"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "null-forgiving chain assignment" nullForgivingChain

                Expect.stringContains
                    nullForgivingChain
                    "        var serviceProvider = _veryLongConfigurationProviderField!\n            .GetRequiredServiceProvider()\n            .BuildServiceProvider();\n"
                    "Long null-forgiving chain should break member chain cleanly."

                let shortNullForgiving =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M(object? value)"
                                "    {"
                                "        var item = value!.ToString();"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                Expect.stringContains
                    shortNullForgiving
                    "        var item = value!.ToString();\n"
                    "Short null-forgiving access should stay on one line."

                let longTypeParamAttr =
                    stable
                        (lines
                            [
                                "class Container<[CustomTypeParameterAttribute(\"first\", \"second\", \"third\", \"fourth\", \"fifth\")] TElement>"
                                "{"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "type parameter attribute" longTypeParamAttr

                Expect.stringContains
                    longTypeParamAttr
                    "class Container<\n    [CustomTypeParameterAttribute(\"first\", \"second\", \"third\", \"fourth\", \"fifth\")] TElement\n> { }\n"
                    "Fitting type parameter attribute (91 cols) should stay on the same line as its type parameter."

                let shortTypeParamAttr =
                    stable
                        (lines [ "class Container<[NotNull] TElement>"; "{"; "}" ])
                        Settings.Default

                Expect.stringContains
                    shortTypeParamAttr
                    "class Container<[NotNull] TElement> { }\n"
                    "Short type parameter attribute should remain flat."

                let longIsPatterns =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M(object candidateExpressionNameForTesting)"
                                "    {"
                                "        if (candidateExpressionNameForTesting is VeryLongTargetPatternTypeNameExceedingColumns matchedValue)"
                                "        {"
                                "        }"
                                "        while (candidateExpressionNameForTesting is VeryLongTargetPatternTypeNameExceedingColumns loopMatched)"
                                "        {"
                                "        }"
                                "        var matched = candidateExpressionNameForTesting is VeryLongTargetPatternTypeNameExceedingColumns assignedMatch;"
                                "        if (candidateExpressionNameForTesting is RecursiveType { FirstProperty: 1, SecondProperty: 2 } recMatched)"
                                "        {"
                                "        }"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "long is patterns" longIsPatterns

                Expect.stringContains
                    longIsPatterns
                    "        if (\n            candidateExpressionNameForTesting\n            is VeryLongTargetPatternTypeNameExceedingColumns matchedValue\n        ) { }\n"
                    "Long 'is' pattern inside 'if' should break before 'is' at block indentation."

                Expect.stringContains
                    longIsPatterns
                    "        while (\n            candidateExpressionNameForTesting\n            is VeryLongTargetPatternTypeNameExceedingColumns loopMatched\n        ) { }\n"
                    "Long 'is' pattern inside 'while' should break before 'is' at block indentation."

                Expect.stringContains
                    longIsPatterns
                    "        var matched =\n            candidateExpressionNameForTesting\n                is VeryLongTargetPatternTypeNameExceedingColumns assignedMatch;\n"
                    "Long 'is' pattern in assignment should break before 'is' with indentation."

                Expect.stringContains
                    longIsPatterns
                    "        if (\n            candidateExpressionNameForTesting is RecursiveType\n            {\n"
                    "Recursive property pattern should keep 'is' before breaking braces."

                let chains =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        var props = CreateLongBuilderInstance().FirstVeryLongProperty.SecondVeryLongProperty.ThirdVeryLongProperty;"
                                "        var indexed = dictionaryLookupTable[longLookupKeyName].FirstVeryLongProperty.SecondVeryLongProperty.ThirdProperty;"
                                "        var called = this[longLookupKeyIdentifierName].VeryLongIntermediateProperty.ExecuteLongMethodCall(firstArg, secondArg);"
                                "        var conditional = sourceObject?.FirstIntermediateProperty?.SecondIntermediateProperty /* mid */ .InvokeTargetMethod(firstArg, secondArg, thirdArg, fourthArg);"
                                "        var singleTail = shortPrefix.Intermediate.ExecuteLongTailCall(firstLongArgumentValue, secondLongArgumentValue);"
                                "        var shortIndexed = dataSet.Tables[0]!.Columns[0]!.Expression;"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "chain breaking" chains

                Expect.stringContains
                    chains
                    ".FirstVeryLongProperty\n            .SecondVeryLongProperty\n            .ThirdVeryLongProperty;\n"
                    "Empty-arg call property chain should break across properties."

                Expect.stringContains
                    chains
                    "        var indexed = dictionaryLookupTable[longLookupKeyName]\n            .FirstVeryLongProperty\n            .SecondVeryLongProperty\n            .ThirdProperty;\n"
                    "Multi-dot indexer chain should break across properties."

                Expect.stringContains
                    chains
                    "        var called = this[longLookupKeyIdentifierName]\n            .VeryLongIntermediateProperty\n            .ExecuteLongMethodCall(firstArg, secondArg);\n"
                    "Indexer + property + call chain should break after indexer."

                Expect.stringContains
                    chains
                    "        var conditional =\n            sourceObject?.FirstIntermediateProperty?.SecondIntermediateProperty /* mid */\n            .InvokeTargetMethod(firstArg, secondArg, thirdArg, fourthArg);\n"
                    "Conditional chain with multi-arg call and comment should keep receiver together and lines within width."

                Expect.stringContains
                    chains
                    "        var singleTail = shortPrefix.Intermediate.ExecuteLongTailCall(\n            firstLongArgumentValue,\n            secondLongArgumentValue\n        );\n"
                    "Single trailing call on short receiver should keep chain head attached and break arguments."

                Expect.stringContains
                    chains
                    "        var shortIndexed = dataSet.Tables[0]!.Columns[0]!.Expression;\n"
                    "Short indexed expression should stay on one line."

                let watchCreatedPreserved =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        WatchCreated(firstArgumentValue, secondArgumentValue, thirdArgumentValue).ConfigureAwait(false);"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "WatchCreated preserved" watchCreatedPreserved

                Expect.stringContains
                    watchCreatedPreserved
                    "        WatchCreated(firstArgumentValue, secondArgumentValue, thirdArgumentValue)\n            .ConfigureAwait(false);\n"
                    "WatchCreated().ConfigureAwait(false) should keep lines within width."

                let nestedBreakPropagation =
                    stable
                        "class C\n{\n    void M()\n    {\n        F(a = (b = () => { return 1; }));\n    }\n}\n"
                        Settings.Default

                Expect.stringContains
                    nestedBreakPropagation
                    "        F(\n            a = (\n                b = () =>\n                {\n                    return 1;\n                }\n            )\n        );\n"
                    "Nested lambda assignment breaks should still break enclosing call arguments."

                let makeNestedLambdaAssignment depth =
                    let sb = StringBuilder("class C\n{\n    void M()\n    {\n        ")

                    for _ = 1 to depth do
                        sb.Append("f = () => ") |> ignore

                    sb.Append("1;\n    }\n}\n") |> ignore
                    sb.ToString()

                let chainSample = "class C { void M() { var x = source.F().G; } }\n"
                let chainTree = Csff.Parser.SyntaxTree()
                Parser.parse chainSample chainTree

                let mutable chainAlloc = -1L
                let mutable smallBuildMs = 0.0
                let mutable largeBuildMs = 0.0
                let mutable nestedError: exn = null

                let stackThread =
                    System.Threading.Thread(
                        System.Threading.ThreadStart(fun () ->
                            try
                                use doc = new DocumentBuffer()
                                use syntax = new SyntaxDocumentBuilder()
                                let nestedSmall = makeNestedLambdaAssignment 256
                                let nestedLarge = makeNestedLambdaAssignment 2048
                                let treeSmall = Csff.Parser.SyntaxTree()
                                let treeLarge = Csff.Parser.SyntaxTree()
                                Parser.parse nestedSmall treeSmall
                                Parser.parse nestedLarge treeLarge

                                for _ = 1 to 64 do
                                    doc.Reset()

                                    syntax.Build(
                                        chainSample,
                                        chainTree,
                                        doc,
                                        PrinterOptions.Default
                                    )

                                    doc.Reset()

                                    syntax.Build(
                                        nestedSmall,
                                        treeSmall,
                                        doc,
                                        PrinterOptions.Default
                                    )

                                let allocBefore = GC.GetAllocatedBytesForCurrentThread()
                                doc.Reset()
                                syntax.Build(chainSample, chainTree, doc, PrinterOptions.Default)
                                chainAlloc <- GC.GetAllocatedBytesForCurrentThread() - allocBefore

                                let measure (src: string) (tree: Csff.Parser.SyntaxTree) =
                                    let sw = Stopwatch.StartNew()
                                    doc.Reset()
                                    syntax.Build(src, tree, doc, PrinterOptions.Default)
                                    sw.Stop()
                                    sw.Elapsed.TotalMilliseconds

                                smallBuildMs <- measure nestedSmall treeSmall
                                largeBuildMs <- measure nestedLarge treeLarge
                            with ex ->
                                nestedError <- ex),
                        Worker.StackSize
                    )

                stackThread.Start()
                stackThread.Join()

                if not (isNull nestedError) then
                    System.Runtime.ExceptionServices.ExceptionDispatchInfo
                        .Capture(nestedError)
                        .Throw()

                Expect.equal chainAlloc 0L "Steady-state chain document build must not allocate."

                Expect.isLessThan
                    largeBuildMs
                    (max 30.0 (smallBuildMs * 20.0))
                    $"Nested lambda assignment build must scale linearly (256={smallBuildMs:F2}ms, 2048={largeBuildMs:F2}ms)."

                let chainAndAssignments =
                    stable
                        (lines
                            [
                                "class C"
                                "{"
                                "    void M()"
                                "    {"
                                "        F(obj?.Property.Call(new Y { A = 1 }).Result, firstVeryLongArgumentNameForTesting, secondVeryLongArgumentNameForTesting, thirdArgument);"
                                "        var veryLongVariableNameForTestingAssignmentLength = veryLongConfigurationSourceForTestingAssignmentLength.GetValue()!.Property;"
                                "        var anotherVeryLongVariableNameForTestingAssignmentLength = veryLongConfigurationSourceForTestingAssignmentLength[0]!.Property;"
                                "    }"
                                "}"
                            ])
                        Settings.Default

                assertMaxLineLength "conditional chain and long assignments" chainAndAssignments

                Expect.stringContains
                    chainAndAssignments
                    "        F(\n            obj?.Property.Call(\n                new Y\n                {\n                    A = 1,\n                }\n            ).Result,\n            firstVeryLongArgumentNameForTesting,\n            secondVeryLongArgumentNameForTesting,\n            thirdArgument\n        );\n"
                    "Conditional chain fallback group should propagate enclosed mandatory breaks to the enclosing argument list."

                Expect.stringContains
                    chainAndAssignments
                    "        var veryLongVariableNameForTestingAssignmentLength =\n            veryLongConfigurationSourceForTestingAssignmentLength.GetValue()!.Property;\n"
                    "Long null-forgiven invocation member access should detach after '=' when receiver overflows."

                Expect.stringContains
                    chainAndAssignments
                    "        var anotherVeryLongVariableNameForTestingAssignmentLength =\n            veryLongConfigurationSourceForTestingAssignmentLength[0]!.Property;\n"
                    "Long null-forgiven indexer member access should detach after '=' when receiver overflows."
            }

            test
                "keeps attributed type parameters on one line when they fit and indents when broken" {
                let sample =
                    lines
                        [
                            "class C"
                            "{"
                            "    private static string Resolve<[DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)] T>() => \"\";"
                            "}"
                            "class Outer"
                            "{"
                            "    class Inner"
                            "    {"
                            "        private static string Overflow<[DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)] TProperties>() => \"\";"
                            "    }"
                            "    static void MultiFit<[Foo][DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)] T>() { }"
                            "    static void MultiBreak<[VeryLongFirstAttributeNameHere][DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)] T>() { }"
                            "    interface IVar<[DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.NonPublicMethods)] out TOut, [DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.NonPublicMethods)] in TIn> { }"
                            "}"
                        ]

                let output = stable sample Settings.Default

                Expect.stringContains
                    output
                    "    private static string Resolve<\n        [DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)] T\n    >() => \"\";\n"
                    "Fitting attributed type parameter should remain on one line with its attribute."

                Expect.stringContains
                    output
                    "        private static string Overflow<\n            [DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)]\n                TProperties\n        >() => \"\";\n"
                    "Overflowing attributed type parameter should break and indent the type parameter."

                Expect.stringContains
                    output
                    "    static void MultiFit<\n        [Foo] [DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)] T\n    >() { }\n"
                    "Fitting multiple attributes and type parameter should stay on one line."

                Expect.stringContains
                    output
                    "    static void MultiBreak<\n        [VeryLongFirstAttributeNameHere]\n        [DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.PublicProperties)]\n            T\n    >() { }\n"
                    "Overflowing multiple attributes should break one attribute per line and indent the type parameter."

                Expect.stringContains
                    output
                    "        [DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.NonPublicMethods)] out TOut,\n        [DynamicallyAccessedMembers(DynamicallyAccessedMemberTypes.NonPublicMethods)] in TIn\n"
                    "Attributed type parameters with variance modifiers should stay on one line when they fit."
            }

            test
                "breaks after '=' for merged two-link member chains while preserving unmerged chain breaks" {
                let sample =
                    lines
                        [
                            "namespace N"
                            "{"
                            "    class C"
                            "    {"
                            "        void M()"
                            "        {"
                            "            IList<ParameterExpression> targetDelegateArguments = this.Delegate.RuntimeDelegateArguments;"
                            "            IList<ParameterExpression> itemDelegateArguments = item.Delegate.RuntimeDelegateArguments;"
                            "            IList<ParameterExpression> baseDelegateArguments = base.Delegate.RuntimeDelegateArguments;"
                            "            IList<ParameterExpression> forgivenDelegateArgs = this.BinderInvocation!.OperationLongName;"
                            "            IList<ParameterExpression> trailingForgivenArgs = this.VeryLongDelegateNameThatExceeds84CharactersEvenOnLine2.RuntimeDelegateArgumentsLongName!;"
                            "            IList<ParameterExpression> longRootDelegateArgs = sourceObj.Delegate.RuntimeDelegateArguments;"
                            "            IList<ParameterExpression> threeLinkDelegateArgs = this.Delegate.Inner.RuntimeDelegateArguments;"
                            "            var genericMid = Foo.Bar<VeryLongTypeArgumentOne, VeryLongTypeArgumentTwo, VeryLongTypeArgumentThree>.Baz;"
                            "            var genericEnd = Foo.Bar.Baz<VeryLongTypeArgumentOne, VeryLongTypeArgumentTwo, VeryLongTypeArgumentThree, VeryLongTypeArgumentFour>;"
                            "            var thisGenericMid = this.Bar<VeryLongTypeArgumentOne, VeryLongTypeArgumentTwo, VeryLongTypeArgumentThree>.Baz;"
                            "            var singleArgGeneric = Foo.Bar<int>.VeryLongPropertyNameCausingTotalLineToExceedOneHundredColumnsRightHereNow;"
                            "            var typeofForgiven = typeof(Dictionary<VeryLongTypeArgumentOne, VeryLongTypeArgumentTwo>).AssemblyQualifiedName!;"
                            "        }"
                            "    }"
                            "}"
                        ]

                let output = stable sample Settings.Default

                Expect.stringContains
                    output
                    "            IList<ParameterExpression> targetDelegateArguments =\n                this.Delegate.RuntimeDelegateArguments;\n"
                    "Two-link member chain on 'this' should break after '='."

                Expect.stringContains
                    output
                    "            IList<ParameterExpression> itemDelegateArguments =\n                item.Delegate.RuntimeDelegateArguments;\n"
                    "Two-link member chain on a 4-char identifier should break after '='."

                Expect.stringContains
                    output
                    "            IList<ParameterExpression> baseDelegateArguments =\n                base.Delegate.RuntimeDelegateArguments;\n"
                    "Two-link member chain on 'base' should break after '='."

                Expect.stringContains
                    output
                    "            IList<ParameterExpression> forgivenDelegateArgs =\n                this.BinderInvocation!.OperationLongName;\n"
                    "Two-link member chain on 'this' with null-forgiving first member should break after '='."

                Expect.stringContains
                    output
                    "            IList<ParameterExpression> trailingForgivenArgs =\n                this.VeryLongDelegateNameThatExceeds84CharactersEvenOnLine2.RuntimeDelegateArgumentsLongName!;\n"
                    "Two-link member chain on 'this' with trailing '!' should keep line 2 flat after breaking '='."

                Expect.stringContains
                    output
                    "            IList<ParameterExpression> longRootDelegateArgs = sourceObj\n                .Delegate\n                .RuntimeDelegateArguments;\n"
                    "Unmerged two-link member chain should keep its receiver beside '=' and break dots."

                Expect.stringContains
                    output
                    "            IList<ParameterExpression> threeLinkDelegateArgs = this.Delegate\n                .Inner\n                .RuntimeDelegateArguments;\n"
                    "Three-link member chain on 'this' should keep merged prefix beside '=' and break remaining dots."

                Expect.stringContains
                    output
                    "            var genericMid = Foo.Bar<\n                VeryLongTypeArgumentOne,\n                VeryLongTypeArgumentTwo,\n                VeryLongTypeArgumentThree\n            >\n                .Baz;\n"
                    "Two-link chain with expandable middle generic member should keep type-argument wrapping."

                Expect.stringContains
                    output
                    "            var genericEnd = Foo.Bar\n                .Baz<\n                    VeryLongTypeArgumentOne,\n                    VeryLongTypeArgumentTwo,\n                    VeryLongTypeArgumentThree,\n                    VeryLongTypeArgumentFour\n                >;\n"
                    "Two-link chain with expandable final generic member should keep type-argument wrapping."

                Expect.stringContains
                    output
                    "            var thisGenericMid = this.Bar<\n                VeryLongTypeArgumentOne,\n                VeryLongTypeArgumentTwo,\n                VeryLongTypeArgumentThree\n            >\n                .Baz;\n"
                    "Two-link 'this' chain with expandable middle generic member should keep type-argument wrapping."

                Expect.stringContains
                    output
                    "            var singleArgGeneric =\n                Foo.Bar<int>.VeryLongPropertyNameCausingTotalLineToExceedOneHundredColumnsRightHereNow;\n"
                    "Two-link short-root chain with single-arg unbreakable generic should break after '='."

                Expect.stringContains
                    output
                    "            var typeofForgiven =\n                typeof(Dictionary<\n                    VeryLongTypeArgumentOne,\n                    VeryLongTypeArgumentTwo\n                >).AssemblyQualifiedName!;\n"
                    "Null-forgiven member access on expandable typeof receiver should preserve internal type-argument wrapping."
            }

            test
                "conditional configurations verify comments and disabled text checks ordered non-whitespace characters including commas" {
                let verifier = SyntaxPreservation.Checker()
                let tokens = TokenPreservation.Checker()

                let lines (xs: string list) = String.concat "\n" xs + "\n"

                let expectViolation label verdict =
                    match verdict with
                    | SyntaxPreservation.Verification.Violation _ -> ()
                    | other -> failtest $"Expected Violation for {label}, got %A{other}."

                let expectUnprovable label verdict =
                    match verdict with
                    | SyntaxPreservation.Verification.Unprovable _ -> ()
                    | other -> failtest $"Expected Unprovable for {label}, got %A{other}."

                let expectProven label verdict =
                    Expect.equal
                        verdict
                        SyntaxPreservation.Verification.Proven
                        $"Expected Proven for {label}."

                let symWitness =
                    { TransformationWitness.None with
                        ChangedTrailingCommas = true
                        SymbolSets = [| [| "SYM" |] |]
                        AllConfigurationsComplete = true
                    }

                let symSrc =
                    lines
                        [
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1,];"
                            "    // important note, do not touch"
                            "#endif"
                            "}"
                        ]

                let symShuffledComment =
                    lines
                        [
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1];"
                            "    // ,not ,do note important touch"
                            "#endif"
                            "}"
                        ]

                let symSrcWithCommaComment =
                    lines
                        [
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1,];"
                            "    // ,,,"
                            "#endif"
                            "}"
                        ]

                let symFmtStrippedCommaComment =
                    lines
                        [
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1];"
                            "    //"
                            "#endif"
                            "}"
                        ]

                let symTree = Csff.Parser.SyntaxTree()
                Parser.parse symSrc symTree

                expectViolation
                    "shuffled comment inside #if SYM via Decide"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "SymComment.cs",
                        symSrc,
                        symShuffledComment,
                        sourceTree = symTree,
                        witness = symWitness
                    ))

                expectViolation
                    "shuffled comment inside #if SYM via DecideDirectSpan"
                    (verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "SymComment.cs",
                        symSrc,
                        symShuffledComment.AsSpan(),
                        symTree,
                        symWitness
                    ))

                expectViolation
                    "shuffled comment inside #if SYM via AdjudicateDecision"
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "SymComment.cs",
                        symSrc,
                        symShuffledComment
                    ))

                expectViolation
                    "stripped commas in comment inside #if SYM"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "SymCommaComment.cs",
                        symSrcWithCommaComment,
                        symFmtStrippedCommaComment,
                        witness = symWitness
                    ))

                let shebangSymSrc = "#!/usr/bin/env dotnet\n" + symSrc
                let shebangSymShuffled = "#!/usr/bin/env dotnet\n" + symShuffledComment

                expectViolation
                    "shuffled comment inside #if SYM under shebang"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "ShebangSym.cs",
                        shebangSymSrc,
                        shebangSymShuffled,
                        witness = symWitness
                    ))

                let deadSrc =
                    lines [ "#if false"; "Foo(a, b); int z = x - y;"; "#endif"; "class C { }" ]

                let deadCorrupted =
                    lines [ "#if false"; "Foo(ab); int z = y - x;"; "#endif"; "class C { }" ]

                expectUnprovable
                    "#if false dropped comma and reordered expression"
                    (verifier.Decide(PrinterOptions.Default, "DeadFalse.cs", deadSrc, deadCorrupted))

                let deadExpected = tokens.Normalize(PrinterOptions.Default, deadSrc, deadCorrupted)

                Expect.isFalse
                    (tokens.FastEquivalent(deadExpected, deadCorrupted))
                    "TokenPreservation.FastEquivalent rejects dropped commas and reordered disabled text."

                let dirCommentSrc =
                    lines
                        [
                            "#if A"
                            "/* keep"
                            "#endif"
                            "#if B"
                            "class B { int x = 1; }"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let dirCommentCorrupted = dirCommentSrc.Replace("/* keep", "/* drop")

                expectViolation
                    "directive-spanning block comment corrupted before #endif"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "DirComment.cs",
                        dirCommentSrc,
                        dirCommentCorrupted
                    ))

                let nestedFalseInBlockCommentSrc =
                    lines [ "#if A"; "/*"; "#if false"; "keep"; "#endif"; "*/"; "#endif" ]

                let nestedFalseInBlockCommentCorrupted =
                    nestedFalseInBlockCommentSrc.Replace("keep", "deleted")

                expectViolation
                    "#if false inside block comment opened in #if A"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "NestedFalseInComment.cs",
                        nestedFalseInBlockCommentSrc,
                        nestedFalseInBlockCommentCorrupted
                    ))

                let siblingFalseInBlockCommentSrc =
                    lines
                        [
                            "#if A"
                            "/*"
                            "#endif"
                            "#if false"
                            "keep"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let siblingFalseInBlockCommentCorrupted =
                    siblingFalseInBlockCommentSrc.Replace("keep", "deleted")

                expectViolation
                    "#if false after #endif inside block comment opened in #if A"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "SiblingFalseInComment.cs",
                        siblingFalseInBlockCommentSrc,
                        siblingFalseInBlockCommentCorrupted
                    ))

                let nestedBcSrc =
                    lines
                        [
                            "#if A"
                            "/*"
                            "#endif"
                            "#if B"
                            "#if C"
                            "class C{int x=1;}"
                            "#endif"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let nestedBcFmt = nestedBcSrc.Replace("class C{int x=1;}", "class C { int x = 1; }")

                expectProven
                    "nested #if B/#if C inside directive-spanning block comment"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "NestedBC.cs",
                        nestedBcSrc,
                        nestedBcFmt
                    ))

                let unchangedArmPlusBSrc =
                    lines
                        [
                            "#if A"
                            "/*"
                            "#endif"
                            "#if A"
                            "class KeepA { }"
                            "#endif"
                            "#if B"
                            "class FormatB{int x;}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let unchangedArmPlusBFmt =
                    unchangedArmPlusBSrc.Replace(
                        "class FormatB{int x;}",
                        "class FormatB { int x; }"
                    )

                expectProven
                    "unchanged #if A alongside formatted #if B inside directive-spanning block comment"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "UnchangedAPlusB.cs",
                        unchangedArmPlusBSrc,
                        unchangedArmPlusBFmt
                    ))

                let parenDirectiveSrc =
                    lines
                        [
                            "#if A"
                            "/*"
                            "#endif"
                            "#if(B)"
                            "class B{int x;}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let parenDirectiveFmt =
                    parenDirectiveSrc.Replace("class B{int x;}", "class B { int x; }")

                expectProven
                    "parenthesized #if(B) inside directive-spanning block comment"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "ParenDirective.cs",
                        parenDirectiveSrc,
                        parenDirectiveFmt
                    ))

                let combiningSymSrc =
                    lines
                        [
                            "#if A\u0301"
                            "/*"
                            "#endif"
                            "#if B\u0301"
                            "class B{int x;}"
                            "#endif"
                            "#if A\u0301"
                            "*/"
                            "#endif"
                        ]

                let combiningSymFmt =
                    combiningSymSrc.Replace("class B{int x;}", "class B { int x; }")

                expectProven
                    "combining-mark symbol forcing #define prefix with deferred spans"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "CombiningSym.cs",
                        combiningSymSrc,
                        combiningSymFmt
                    ))

                let mixedDeadSrc =
                    lines
                        [
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1,];"
                            "#if false"
                            "    Foo(a, b); int z = x - y;"
                            "#endif"
                            "#endif"
                            "}"
                        ]

                let mixedDeadCorrupted =
                    lines
                        [
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1];"
                            "#if false"
                            "    Foo(ab); int z = y - x;"
                            "#endif"
                            "#endif"
                            "}"
                        ]

                expectUnprovable
                    "#if false nested inside active #if SYM"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "MixedDead.cs",
                        mixedDeadSrc,
                        mixedDeadCorrupted,
                        witness = symWitness
                    ))

                let deadCommentSrc =
                    lines
                        [ "#if false"; "// important note, do not touch"; "#endif"; "class C { }" ]

                let deadCommentCorrupted =
                    lines
                        [ "#if false"; "// ,not ,do note important touch"; "#endif"; "class C { }" ]

                expectUnprovable
                    "#if false shuffled comment"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "DeadComment.cs",
                        deadCommentSrc,
                        deadCommentCorrupted
                    ))

                let validSymSrc =
                    lines
                        [
                            "#if SYM"
                            "using Z;"
                            "using A;"
                            "#endif"
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1,];"
                            "    // important note, do not touch"
                            "#endif"
                            "#if false"
                            "    Foo(a, b); int z = x - y;"
                            "#endif"
                            "}"
                        ]

                let validSymFmt =
                    lines
                        [
                            "#if SYM"
                            "using A;"
                            "using Z;"
                            "#endif"
                            "class C"
                            "{"
                            "#if SYM"
                            "    int[] xs = [1];"
                            "    // important note, do not touch"
                            "#endif"
                            "#if false"
                            "        Foo(a, b); int z = x - y;"
                            "#endif"
                            "}"
                        ]

                let validSymWitness = { symWitness with SortedUsings = true }

                expectProven
                    "valid #if SYM transforms with intact #if false"
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "ValidSym.cs",
                        validSymSrc,
                        validSymFmt,
                        witness = validSymWitness
                    ))

                let elifSpanningSource =
                    lines
                        [
                            "#if A"
                            "/*"
                            "#elif B"
                            "class C{int x;}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let elifSpanningFormatted =
                    lines
                        [
                            "#if A"
                            "/*"
                            "#elif B"
                            "class C"
                            "{"
                            "    int x;"
                            "}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                Expect.equal
                    (stable elifSpanningSource Settings.Default)
                    elifSpanningFormatted
                    "Unmatched #elif arm inside directive-spanning block comment defers formatted active body."

                let docSpanningSource =
                    lines
                        [
                            "#if A"
                            "/**"
                            "#endif"
                            "#if B"
                            "class C{int x;}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let docSpanningFormatted =
                    lines
                        [
                            "#if A"
                            "/**"
                            "#endif"
                            "#if B"
                            "class C"
                            "{"
                            "    int x;"
                            "}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                Expect.equal
                    (stable docSpanningSource Settings.Default)
                    docSpanningFormatted
                    "Directive-spanning documentation block comment /** */ defers formatted active body."

                let elseDocSpanningSource =
                    lines
                        [
                            "#if A"
                            "/**"
                            "#else"
                            "class C{int x;}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                let elseDocSpanningFormatted =
                    lines
                        [
                            "#if A"
                            "/**"
                            "#else"
                            "class C"
                            "{"
                            "    int x;"
                            "}"
                            "#endif"
                            "#if A"
                            "*/"
                            "#endif"
                        ]

                Expect.equal
                    (stable elseDocSpanningSource Settings.Default)
                    elseDocSpanningFormatted
                    "Unmatched #else inside directive-spanning /** */ doc comment defers formatted active body."

                let tamperedDoc = docSpanningFormatted.Replace("int x;", "int y;")

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "TamperedDocSpan.cs",
                        docSpanningSource,
                        tamperedDoc
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Tampered body inside deferred directive-spanning doc comment must be rejected."
                | _ -> ()

                let interpHoleSource =
                    "#if SYM\nclass C { string S = $\"{ /* k */ 1 }\"; }\n#endif\n"

                let interpHoleTampered =
                    "#if SYM\nclass C { string S = $\"{ /* j */ 1 }\"; }\n#endif\n"

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "InterpHoleTampered.cs",
                        interpHoleSource,
                        interpHoleTampered
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest "Changed interpolation hole comment inside #if SYM must not be proven."
                | _ -> ()

                let interpHoleRemoved = "#if SYM\nclass C { string S = $\"{ 1 }\"; }\n#endif\n"

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "InterpHoleRemoved.cs",
                        interpHoleSource,
                        interpHoleRemoved
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest "Deleted interpolation hole comment inside #if SYM must not be proven."
                | _ -> ()

                match
                    verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "InterpHoleRemovedSpan.cs",
                        interpHoleSource,
                        interpHoleRemoved.AsSpan(),
                        Unchecked.defaultof<Csff.Parser.SyntaxTree>,
                        TransformationWitness.Searched
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Deleted interpolation hole comment inside #if SYM must not be proven via DecideDirectSpan."
                | _ -> ()

                let interpHoleWithCommaRemoved =
                    "#if SYM\nclass C { string S = $\"{ /* k */ 1 }\"; int[] xs = [1,]; }\n#endif\n"

                let interpHoleWithCommaRemovedFmt =
                    "#if SYM\nclass C { string S = $\"{ 1 }\"; int[] xs = [1]; }\n#endif\n"

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "InterpHoleWithCommaRemoved.cs",
                        interpHoleWithCommaRemoved,
                        interpHoleWithCommaRemovedFmt
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Deleted interpolation hole comment with trailing-comma edit inside #if SYM must not be proven."
                | _ -> ()

                let rawReindentHoleSource =
                    "#if SYM\nclass C\n{\n    void M()\n    {\n        string s = $\"\"\"\n            a { /* k */ 1 }\n            b\n            \"\"\";\n        int[] x = [1,];\n    }\n}\n#endif\n"

                let rawReindentHoleFormatted =
                    "#if SYM\nclass C\n{\n    void M()\n    {\n        string s = $\"\"\"\n        a { /* k */1}\n        b\n        \"\"\";\n        int[] x = [1];\n    }\n}\n#endif\n"

                Expect.equal
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "RawReindentHole.cs",
                        rawReindentHoleSource,
                        rawReindentHoleFormatted
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Reindented multiline raw interpolation with a hole comment and [1,] edit inside #if SYM verifies as Proven."

                Expect.equal
                    (verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "RawReindentHoleSpan.cs",
                        rawReindentHoleSource,
                        rawReindentHoleFormatted.AsSpan(),
                        Unchecked.defaultof<Csff.Parser.SyntaxTree>,
                        TransformationWitness.Searched
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Reindented multiline raw interpolation with a hole comment inside #if SYM verifies via DecideDirectSpan."

                match
                    verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "RawReindentHoleNone.cs",
                        rawReindentHoleSource,
                        rawReindentHoleFormatted.AsSpan(),
                        Unchecked.defaultof<Csff.Parser.SyntaxTree>,
                        TransformationWitness.None
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Reindented multiline raw interpolation without witness permission must not be proven."
                | _ -> ()

                for label, tampered in
                    [
                        "hole comment", rawReindentHoleFormatted.Replace("/* k */", "/* x */")
                        "raw literal line",
                        rawReindentHoleFormatted.Replace("\n        b\n", "\n        c\n")
                        "hole expression", rawReindentHoleFormatted.Replace("1}", "2}")
                    ] do
                    match
                        verifier.Decide(
                            PrinterOptions.Default,
                            "RawReindentHoleTampered.cs",
                            rawReindentHoleSource,
                            tampered
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest
                            $"Tampered {label} in reindented multiline raw interpolation inside #if SYM must not be proven."
                    | _ -> ()

                let interpHoleCommaSource =
                    "#if SYM\nclass C { string s = $\"{ /* k */ new int[] {1,} }\"; }\n#endif\n"

                let interpHoleCommaFormatted =
                    "#if SYM\nclass C\n{\n    string s = $\"{ /* k */new int[] { 1 }}\";\n}\n#endif\n"

                Expect.equal
                    (stable interpHoleCommaSource Settings.Default)
                    interpHoleCommaFormatted
                    "Interpolated hole with comment and trailing-comma initializer formats cleanly under #if SYM."

                Expect.equal
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "InterpHoleComma.cs",
                        interpHoleCommaSource,
                        interpHoleCommaFormatted
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Deferred interpolation hole comment tolerates proven trailing-comma removal."

                Expect.equal
                    (verifier.DecideDirectSpan(
                        PrinterOptions.Default,
                        "InterpHoleCommaSpan.cs",
                        interpHoleCommaSource,
                        interpHoleCommaFormatted.AsSpan(),
                        Unchecked.defaultof<Csff.Parser.SyntaxTree>,
                        TransformationWitness.Searched
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Deferred interpolation hole comment with comma removal verifies via DecideDirectSpan."

                for label, badFmt in
                    [
                        "changed comment", interpHoleCommaFormatted.Replace("/* k */", "/* j */")
                        "deleted comment", interpHoleCommaFormatted.Replace("/* k */", "")
                        "changed value", interpHoleCommaFormatted.Replace("{ 1 }", "{ 2 }")
                    ] do
                    match
                        verifier.Decide(
                            PrinterOptions.Default,
                            "InterpHoleCommaTampered.cs",
                            interpHoleCommaSource,
                            badFmt
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest
                            $"Tampered ({label}) inside #if SYM interpolation hole with comma removal must not be proven."
                    | _ -> ()

                let q3 = "\"\"\""

                let rawReindentHoleCommaSource =
                    "#if SYM\nclass C\n{\n    void M()\n    {\n        string s = $"
                    + q3
                    + "\n            a { /* k */ new int[] {1,} }\n            b\n            "
                    + q3
                    + ";\n    }\n}\n#endif\n"

                let rawReindentHoleCommaFormatted =
                    "#if SYM\nclass C\n{\n    void M()\n    {\n        string s = $"
                    + q3
                    + "\n        a { /* k */ new int[] {1} }\n        b\n        "
                    + q3
                    + ";\n    }\n}\n#endif\n"

                Expect.equal
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "RawReindentHoleComma.cs",
                        rawReindentHoleCommaSource,
                        rawReindentHoleCommaFormatted
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Reindented multiline raw interpolation with hole comment and hole trailing comma verifies as Proven."

                let nestedInterpHoleCommaSource =
                    "#if SYM\nclass C { string s = $\"{ /* o */ $\"{ /* i */ new int[] {1,} }\" }\"; }\n#endif\n"

                let nestedInterpHoleCommaFormatted =
                    "#if SYM\nclass C\n{\n    string s = $\"{ /* o */ $\"{ /* i */ new int[] {1} }\" }\";\n}\n#endif\n"

                Expect.equal
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "NestedInterpHoleComma.cs",
                        nestedInterpHoleCommaSource,
                        nestedInterpHoleCommaFormatted
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Nested interpolated hole with comment and inner comma removal verifies as Proven."

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "NestedInterpHoleCommaBadComment.cs",
                        nestedInterpHoleCommaSource,
                        nestedInterpHoleCommaFormatted.Replace("/* i */", "/* x */")
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Changed inner hole comment in nested interpolation with comma removal must not be proven."
                | _ -> ()

                let twoHoleCommaSource =
                    "#if SYM\nclass C { string s = $\"{ /* a */ new int[] {1,} } { /* b */ 2 }\"; }\n#endif\n"

                let twoHoleCommaSwapped =
                    "#if SYM\nclass C\n{\n    string s = $\"{ /* b */ new int[] {1} } { /* a */ 2 }\";\n}\n#endif\n"

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "TwoHoleCommaSwapped.cs",
                        twoHoleCommaSource,
                        twoHoleCommaSwapped
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Swapped hole comments across two interpolation holes must not be proven."
                | _ -> ()

                let interpHoleEmptied = "#if SYM\nclass C { string S = \"\"; }\n#endif\n"

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "InterpHoleEmptied.cs",
                        interpHoleSource,
                        interpHoleEmptied
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Replacing interpolation with hole comment by empty literal inside #if SYM must not be proven."
                | _ -> ()

                let slashManyBody =
                    [ 0..999 ]
                    |> List.map (fun n -> $"string S{n} = $\"https://example.com/{{1}}\";")
                    |> String.concat "\n"

                let slashManySource =
                    $"#if SYM\nclass C {{ int[] a = [1,];\n{slashManyBody}\n}}\n#endif\n"

                let slashManyFormatted = slashManySource.Replace("[1,]", "[1]")
                let slashChecker = SyntaxPreservation.Checker()

                try
                    for _ = 1 to 2 do
                        Expect.equal
                            (slashChecker.Decide(
                                PrinterOptions.Default,
                                "SlashMany.cs",
                                slashManySource,
                                slashManyFormatted
                            ))
                            SyntaxPreservation.Verification.Proven
                            "1000 slash interpolations with trailing-comma normalization verify as Proven."

                    let allocStart = System.GC.GetAllocatedBytesForCurrentThread()

                    let slashVerdict =
                        slashChecker.Decide(
                            PrinterOptions.Default,
                            "SlashMany.cs",
                            slashManySource,
                            slashManyFormatted
                        )

                    let allocDelta = System.GC.GetAllocatedBytesForCurrentThread() - allocStart

                    Expect.equal
                        slashVerdict
                        SyntaxPreservation.Verification.Proven
                        "Warmed 1000 slash interpolations verify as Proven."

                    Expect.isLessThan
                        allocDelta
                        500_000L
                        "Reusing pooled hole lexers avoids 24 MB recurring allocation on deferred interpolations with '/'."
                finally
                    slashChecker.ReleasePooledBuffers()

                let nestedInterpSource =
                    "#if SYM\nclass C { string S = $\"{ $\\\"{ /* k */ 1 }\\\" }\"; }\n#endif\n"

                let nestedInterpTampered =
                    "#if SYM\nclass C { string S = $\"{ $\\\"{ /* j */ 1 }\\\" }\"; }\n#endif\n"

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "NestedInterpHoleTampered.cs",
                        nestedInterpSource,
                        nestedInterpTampered
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Changed nested interpolation hole comment inside #if SYM must not be proven."
                | _ -> ()

                let slashLiteralInterpSource =
                    "#if SYM\nclass C{string U=$\"https://example.com/{1}\";}\n#endif\n"

                let slashLiteralInterpExpected =
                    "#if SYM\nclass C\n{\n    string U = $\"https://example.com/{1}\";\n}\n#endif\n"

                Expect.equal
                    (stable slashLiteralInterpSource Settings.Default)
                    slashLiteralInterpExpected
                    "Interpolation containing '/' outside hole comments still defers and formats in #if SYM."

                let rawTailDeadSource =
                    "#if SYM\nclass C\n{\n    string S =\n        \"\"\"\n            a\n            b\n            \"\"\";\n    int[] xs = [1,];\n}\n#endif\n#if false\nclass Dead { int x = /* comment */ 1; }\n#endif\n"

                let rawTailDeadFormatted = stable rawTailDeadSource Settings.Default

                Expect.isTrue
                    (rawTailDeadFormatted.Contains("[1]")
                     && rawTailDeadFormatted.Contains("/* comment */"))
                    "Reindented raw string before trailing comma and #if false dead block normalizes and preserves dead block."

                let commentHoleInterpSource =
                    "#if SYM\nclass C\n{\n    string S = $\"{ /* k */1}\";\n    int[] xs = [1,];\n}\n#endif\n"

                let commentHoleInterpFormatted =
                    "#if SYM\nclass C\n{\n    string S = $\"{ /* k */1}\";\n    int[] xs = [1];\n}\n#endif\n"

                Expect.equal
                    (verifier.Decide(
                        PrinterOptions.Default,
                        "UnchangedHoleComment.cs",
                        commentHoleInterpSource,
                        commentHoleInterpFormatted
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Unchanged commented interpolation inside #if SYM must still verify as Proven alongside normalization."

                let spacedHoleInterpSource =
                    "#if SYM\nclass C{string S=$\"{ /* k */ 1 }\";int[] xs=[1,];}\n#endif\n"

                let spacedHoleInterpFormatted = stable spacedHoleInterpSource Settings.Default

                Expect.isTrue
                    (spacedHoleInterpFormatted.Contains("[1]")
                     && spacedHoleInterpFormatted.Contains("/* k */"))
                    "Commented interpolation with hole spacing reformatted inside #if SYM normalizes [1,] and preserves comment."

                let nestedSpacedHoleSource =
                    "#if SYM\nclass C{string S=$\"{ $\"{ /* k */ 1 }\" }\";int[] xs=[1,];}\n#endif\n"

                let nestedSpacedHoleFormatted = stable nestedSpacedHoleSource Settings.Default

                Expect.isTrue
                    (nestedSpacedHoleFormatted.Contains("[1]")
                     && nestedSpacedHoleFormatted.Contains("/* k */"))
                    "Nested commented interpolation inside #if SYM verifies alongside trailing-comma normalization."

                let repeatedSlashRegions =
                    [|
                        for i in 0..999 ->
                            $"#if SYM{i}\nclass C{i} {{ int[] a = [1,]; string U = \"https://a/b\"; }}\n#endif\n"
                    |]
                    |> String.concat ""

                let repeatedSlashFormatted = repeatedSlashRegions.Replace("[1,]", "[1]")
                let repeatedTimer = Stopwatch.StartNew()

                let repeatedVerdict =
                    verifier.Decide(
                        PrinterOptions.Default,
                        "RepeatedSlashRegions.cs",
                        repeatedSlashRegions,
                        repeatedSlashFormatted
                    )

                repeatedTimer.Stop()

                Expect.equal
                    repeatedVerdict
                    SyntaxPreservation.Verification.Proven
                    "1000 conditional regions sharing one normalized source verify as Proven."

                Expect.isLessThan
                    repeatedTimer.Elapsed.TotalSeconds
                    5.0
                    "Checking each deferred source group once per configuration keeps 1000 conditional regions sublinear."

                let sortedUsingDirectiveComments =
                    "using Z; /*\n#else\nz\n#endif\n*/\nusing A; /*\n#else\na\n#endif\n*/\n#if S\nclass C { int[] a = [1,]; }\n#endif\n"

                let sortedUsingDirectiveFormatted =
                    stable sortedUsingDirectiveComments Settings.Default

                Expect.isTrue
                    (sortedUsingDirectiveFormatted.Contains("using A;")
                     && sortedUsingDirectiveFormatted.Contains("[1]"))
                    "Sorted usings with directive-shaped block comments match whole-comment permutations before body splits."

                let hybridUsingSpanSource =
                    "using Z; /*\n#else\nz\n#endif\n*/\nusing A; /*\n#else\na\n#endif\n*/\n#if S\n/*\n#endif\n#if B\nclass C{int x;}\n#endif\n#if S\n*/\n#endif\n"

                let hybridUsingSpanFormatted = stable hybridUsingSpanSource Settings.Default

                Expect.isTrue
                    (hybridUsingSpanFormatted.Contains("using A;")
                     && hybridUsingSpanFormatted.Contains("int x;"))
                    "Sorted usings with directive-shaped comments alongside a separate directive-spanning block comment stay Proven."

                let hybridUsingDocMergeSource =
                    "/// z\nusing Z; /// tail\nusing A;\n" + docSpanningSource

                let hybridUsingDocMergeFormatted = stable hybridUsingDocMergeSource Settings.Default

                Expect.isTrue
                    (hybridUsingDocMergeFormatted.Contains("/// tail")
                     && hybridUsingDocMergeFormatted.Contains("int x;"))
                    "Sorted usings merging /// runs alongside a directive-spanning /** */ block comment stay Proven."

                for label, docSrc, docFmt in
                    [
                        "1+2->3",
                        "/// z\nusing Z; /// tail1\n/// tail2\nusing A;\n" + docSpanningSource,
                        "/// z\n/// tail1\n/// tail2\nusing A;\nusing Z;\n" + docSpanningFormatted
                        "2+1->3",
                        "/// a\n/// b\nusing Z; /// tail\nusing A;\n" + docSpanningSource,
                        "/// a\n/// b\n/// tail\nusing A;\nusing Z;\n" + docSpanningFormatted
                        "2+2->4",
                        "/// a\n/// b\nusing Z; /// c\n/// d\nusing A;\n" + docSpanningSource,
                        "/// a\n/// b\n/// c\n/// d\nusing A;\nusing Z;\n" + docSpanningFormatted
                    ] do
                    Expect.equal
                        (verifier.Decide(
                            PrinterOptions.Default,
                            $"MultiLineDocMerge-{label}.cs",
                            docSrc,
                            docFmt
                        ))
                        SyntaxPreservation.Verification.Proven
                        $"Merging multi-line /// runs ({label}) alongside formatted directive-spanning /** */ stays Proven."

                let multiLineDocMergeReordered =
                    "/// tail\n/// a\n/// b\nusing A;\nusing Z;\n" + docSpanningFormatted

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "MultiLineDocMergeReordered.cs",
                        "/// a\n/// b\nusing Z; /// tail\nusing A;\n" + docSpanningSource,
                        multiLineDocMergeReordered
                    )
                with
                | SyntaxPreservation.Verification.Proven ->
                    failtest
                        "Reordered multi-line /// runs alongside directive-spanning /** */ must be rejected."
                | _ -> ()

                let repeatedElse1200 =
                    [|
                        for i in 0..1199 ->
                            $"#if S{i}\nclass C{i} {{ int[] a = [1,]; }}\n#else\nclass D{i} {{ }}\n#endif\n"
                    |]
                    |> String.concat ""

                let repeatedElse1200Formatted = repeatedElse1200.Replace("[1,]", "[1]")
                let repeatedChecker = SyntaxPreservation.Checker()

                try
                    ignore (
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "WarmElse.cs",
                            "#if A\nclass W { int[] a = [1,]; }\n#else\nclass V { }\n#endif\n",
                            "#if A\nclass W { int[] a = [1]; }\n#else\nclass V { }\n#endif\n"
                        )
                    )

                    let allocBefore = GC.GetAllocatedBytesForCurrentThread()

                    let repeatedElseVerdict =
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "RepeatedElse1200.cs",
                            repeatedElse1200,
                            repeatedElse1200Formatted
                        )

                    let allocDelta = GC.GetAllocatedBytesForCurrentThread() - allocBefore

                    Expect.equal
                        repeatedElseVerdict
                        SyntaxPreservation.Verification.Proven
                        "1200 conditional #if/#else regions verify as Proven."

                    Expect.isLessThan
                        allocDelta
                        40_000_000L
                        "Deduplicating deferred disabled spans during collection keeps 1200 #if/#else regions low-allocation."

                    let normalizedRaw400 =
                        let q = "\"\"\""

                        [|
                            for i in 0..399 ->
                                $"#if S{i}\nclass C{i} {{ string S = $"
                                + q
                                + "\n        a { /* k */ 1 }\n        "
                                + q
                                + $"; int[] a = [1,]; }}\n#endif\n"
                        |]
                        |> String.concat ""

                    let normalizedRaw400Formatted =
                        let q = "\"\"\""

                        [|
                            for i in 0..399 ->
                                $"#if S{i}\nclass C{i} {{ string S = $"
                                + q
                                + "\n    a { /* k */ 1 }\n    "
                                + q
                                + $"; int[] a = [1]; }}\n#endif\n"
                        |]
                        |> String.concat ""

                    repeatedChecker.ResetParseWork()

                    let normalizedRaw400Verdict =
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "NormalizedRaw400.cs",
                            normalizedRaw400,
                            normalizedRaw400Formatted
                        )

                    let struct (normalizedRaw400Lexes, _) = repeatedChecker.ParseWork

                    Expect.equal
                        normalizedRaw400Verdict
                        SyntaxPreservation.Verification.Proven
                        "400 conditional branches mixing reindented raw interpolations and trailing commas verify as Proven."

                    Expect.isLessThan
                        normalizedRaw400Lexes
                        4_000
                        "Equivalent normalized source variants reuse deferred disabled span coverage without quadratic full-file lexing."

                    let normalizedRawTamperedSource =
                        "#if S0\nclass C0 { string S = $\"\"\"\n        a { /* k */ 1 }\n        \"\"\"; int[] a = [1,]; }\n#endif\n"

                    let normalizedRawTamperedFormatted =
                        "#if S0\nclass C0 { string S = $\"\"\"\n    a { /* x */ 1 }\n    \"\"\"; int[] a = [1]; }\n#endif\n"

                    match
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "NormalizedRawTampered.cs",
                            normalizedRawTamperedSource,
                            normalizedRawTamperedFormatted
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest
                            "Tampered comment inside deferred raw interpolation hole must still be rejected."
                    | _ -> ()

                    let prefixUncondRaw =
                        let q = "\"\"\""
                        "class Pre { string P = " + q + "\n        hello\n        " + q + "; }\n"

                    let prefixUncondRawFmt =
                        let q = "\"\"\""
                        "class Pre { string P = " + q + "\n    hello\n    " + q + "; }\n"

                    repeatedChecker.ResetParseWork()

                    let mixedUncondRaw400Verdict =
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "MixedUncondRaw400.cs",
                            prefixUncondRaw + normalizedRaw400,
                            prefixUncondRawFmt + normalizedRaw400Formatted
                        )

                    let struct (mixedUncondRaw400Lexes, _) = repeatedChecker.ParseWork

                    Expect.equal
                        mixedUncondRaw400Verdict
                        SyntaxPreservation.Verification.Proven
                        "Default normalization rewriting an unconditional raw literal still preserves rewrite provenance for deferred spans."

                    Expect.isLessThan
                        mixedUncondRaw400Lexes
                        4_000
                        "Rewrite provenance preserved across BeginDisabledDeferral avoids quadratic re-lexing."

                    let wsSpanSource =
                        "#if A\n/* open\n#endif\n#if B\n\n#if C\nusing A;\n#endif\n\n#endif\n#if A\nclose */\n#endif\n"

                    let wsSpanPrinted = stable wsSpanSource Settings.Default

                    Expect.isTrue
                        (wsSpanPrinted.Contains("#if B") && wsSpanPrinted.Contains("using A;"))
                        "Worker.PrintChecked preserves formatting when blank lines vanish in nested disabled directive arms."

                    let wsEmptySource =
                        "#if A\n/* open\n#endif\n#if B\n\n#endif\n#if A\nclose */\n#endif\n"

                    let wsEmptyFormatted =
                        "#if A\n/* open\n#endif\n#if B\n#endif\n#if A\nclose */\n#endif\n"

                    Expect.equal
                        (repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "DirectiveSpanningEmptyWsLeaf.cs",
                            wsEmptySource,
                            wsEmptyFormatted
                        ))
                        SyntaxPreservation.Verification.Proven
                        "Removing blank lines inside an empty disabled arm under a directive-spanning comment stays Proven."

                    let csharpWsDirectiveSource =
                        "#if A\n/* open\n#endif\n#\uFEFFif B\nint   x=1;\n#\u001Aelif 0\n\uFEFF\n\uFEFF#\uFEFFelse\nint  y=2;\n\u001A#\uFEFFendif\n#if A\nclose */\n#endif\n"

                    let csharpWsDirectivePrinted = stable csharpWsDirectiveSource Settings.Default

                    Expect.isTrue
                        (csharpWsDirectivePrinted.Contains("int x = 1;")
                         && csharpWsDirectivePrinted.Contains("int y = 2;"))
                        "Worker.PrintChecked preserves formatting for spanning-comment directives using C# whitespace (U+FEFF, U+001A)."

                    match
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "DirectiveSpanningCSharpWsTamper.cs",
                            csharpWsDirectiveSource,
                            csharpWsDirectiveSource.Replace("int   x=1;", "int   x=9;")
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest
                            "Tampered active arm inside spanning comment using C# directive whitespace must still be rejected."
                    | _ -> ()

                    let csharpWsLeafEmptySource =
                        "#if A\n/* open\n#endif\n\uFEFF#\uFEFFif B\n\n  \n\u001A#\u001Aendif\n#if A\nclose */\n#endif\n"

                    let csharpWsLeafPrinted = stable csharpWsLeafEmptySource Settings.Default

                    Expect.isTrue
                        (csharpWsLeafPrinted.Contains("/* open"))
                        "Worker.PrintChecked preserves formatting when blank lines vanish in spanning-comment directive arm with C# directive whitespace."

                    let unclosedParentSpanSource =
                        "#if A\n#if A\n/*\n#endif\n#endif\n#if B\nclass C{int x;}\n#if A\n*/\n#endif\n#endif\n"

                    let unclosedParentSpanPrinted = stable unclosedParentSpanSource Settings.Default

                    Expect.isTrue
                        (unclosedParentSpanPrinted.Contains("int x;"))
                        "Worker.PrintChecked preserves formatting when */ closes before an enclosing arm's #endif."

                    match
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "UnclosedParentSpanTamper.cs",
                            unclosedParentSpanSource,
                            unclosedParentSpanSource.Replace("int x;", "int y;")
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest
                            "Tampered deferred leaf under unclosed parent arm must still be rejected."
                    | _ -> ()

                    match
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "UnclosedTailSpanTamper.cs",
                            unclosedParentSpanSource,
                            unclosedParentSpanSource.Replace("*/", "tamper\n*/")
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest "Tampered unclosed tail before */ must still be rejected."
                    | _ -> ()

                    match
                        repeatedChecker.Decide(
                            PrinterOptions.Default,
                            "DirectiveSpanningActiveWsTamper.cs",
                            "#if A\n/* open\n\nstill */\n#endif\n",
                            "#if A\n/* open\nstill */\n#endif\n"
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest
                            "Removing a blank line inside an active multi-line comment must still be rejected."
                    | _ -> ()
                finally
                    repeatedChecker.ReleasePooledBuffers()

                for eol in [ "\u0085"; "\u2028"; "\u2029" ] do
                    let unicodeSource = docSpanningSource.Replace("\n", eol)

                    match
                        verifier.Decide(
                            PrinterOptions.Default,
                            "UnicodeEolDocSpanPositive.cs",
                            unicodeSource,
                            docSpanningFormatted
                        )
                    with
                    | SyntaxPreservation.Verification.Proven -> ()
                    | other ->
                        failtest
                            $"Directive-spanning comment using U+%04X{int eol[0]} must verify as Proven, got %A{other}."

                    match
                        verifier.Decide(
                            PrinterOptions.Default,
                            "UnicodeEolDocSpan.cs",
                            unicodeSource,
                            tamperedDoc
                        )
                    with
                    | SyntaxPreservation.Verification.Proven ->
                        failtest
                            "Tampered body inside Unicode-EOL directive-spanning doc comment must be rejected."
                    | _ -> ()
            }

            test "enclosing chain or list breaks when an expanded initializer sits inside it" {
                let source =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        b.HasIndex(x => new { x.Name }).IsUnique();"
                            "        var layout = new Grid"
                            "        {"
                            "            Children = { new Grid { (nested = new Grid { InputTransparent = true }) } },"
                            "        };"
                            "        var arr = new[] { nested = new Grid { InputTransparent = true } };"
                            "        F(x = new Grid { InputTransparent = true });"
                            "        Register(Constants.JSImportAttribute, static (context, ct) => new { Syntax = context.TargetNode, Symbol = context.SemanticModel.GetDeclaredSymbol(context.TargetNode, ct) });"
                            "    }"
                            "}"
                        ]

                let expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        b.HasIndex(x => new"
                            "            {"
                            "                x.Name,"
                            "            })"
                            "            .IsUnique();"
                            "        var layout = new Grid"
                            "        {"
                            "            Children ="
                            "            {"
                            "                new Grid"
                            "                {"
                            "                    ("
                            "                        nested = new Grid"
                            "                        {"
                            "                            InputTransparent = true,"
                            "                        }"
                            "                    ),"
                            "                },"
                            "            },"
                            "        };"
                            "        var arr = new[]"
                            "        {"
                            "            nested = new Grid"
                            "            {"
                            "                InputTransparent = true,"
                            "            },"
                            "        };"
                            "        F("
                            "            x = new Grid"
                            "            {"
                            "                InputTransparent = true,"
                            "            }"
                            "        );"
                            "        Register("
                            "            Constants.JSImportAttribute,"
                            "            static (context, ct) =>"
                            "                new"
                            "                {"
                            "                    Syntax = context.TargetNode,"
                            "                    Symbol = context.SemanticModel.GetDeclaredSymbol(context.TargetNode, ct),"
                            "                }"
                            "        );"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable source Settings.Default)
                    expected
                    "Enclosing chains, collections, parens, and argument lists break around expanded initializers."
            }

            test
                "static lambda anonymous object body preserves trivia and stays linear under nesting" {
                let withLineComment =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        F("
                            "            () => 1,"
                            "            static () =>"
                            "                new {"
                            "                    // keep"
                            "                }"
                            "        );"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable withLineComment Settings.Default)
                    withLineComment
                    "Static lambda with line comment in empty anonymous object preserves comment."

                let width40Source =
                    "class C { void M() { Test(x => x, static () => new { Value = /*keep*/ 1 }); } }\n"

                let width40Expected =
                    lines
                        [
                            "class C"
                            "{"
                            "    void M()"
                            "    {"
                            "        Test("
                            "            x => x,"
                            "            static () =>"
                            "                new"
                            "                {"
                            "                    Value = /*keep*/"
                            "                    1,"
                            "                }"
                            "        );"
                            "    }"
                            "}"
                        ]

                Expect.equal
                    (stable
                        width40Source
                        { Settings.Default with
                            Printer =
                                { Settings.Default.Printer with
                                    Width = 40
                                }
                        })
                    width40Expected
                    "Static lambda with block comment in expanded anonymous object keeps comment."

                let mutable nestedExpr = "new { A = 1 }"

                for _ = 1 to 14 do
                    nestedExpr <- $"Run(x => x, static () => {nestedExpr})"

                let nestedSource = $"class C {{ void M() {{ {nestedExpr}; }} }}\n"
                ignore (stable nestedSource Settings.Default)

                let deepChain =
                    System.Text.StringBuilder("class C\n{\n    void M()\n    {\n        F(x => ")

                deepChain.Append("x") |> ignore

                for _ = 1 to 10000 do
                    deepChain.Append(" + x") |> ignore

                deepChain.Append(");\n    }\n}\n") |> ignore

                let mutable deepError: exn = null

                let thread =
                    System.Threading.Thread(
                        System.Threading.ThreadStart(fun () ->
                            try
                                ignore (
                                    stable
                                        (deepChain.ToString())
                                        { Settings.Default with
                                            Printer =
                                                { Settings.Default.Printer with
                                                    IndentSize = 1
                                                }
                                        }
                                )
                            with ex ->
                                deepError <- ex),
                        Worker.StackSize
                    )

                thread.Start()
                thread.Join()

                if not (isNull deepError) then
                    System.Runtime.ExceptionServices.ExceptionDispatchInfo
                        .Capture(deepError)
                        .Throw()

                ignore (
                    stable
                        "class C\n{\n    void M()\n    {\n        var x = new D { F = () => new { A = 1 } };\n    }\n}\n"
                        Settings.Default
                )

                ignore (
                    stable
                        "class C\n{\n    void M()\n    {\n        var x = new D { First = \"some long property value to wrap\", Second = () => new { A = 1, B = 2 } };\n    }\n}\n"
                        Settings.Default
                )
            }

            test
                "editorconfig sections handle trailing comments and missing closing brackets without leakage" {
                withDirectory (fun root ->
                    let ecPath = Path.Combine(root, ".editorconfig")

                    File.WriteAllText(
                        ecPath,
                        "root = true\n[*.cs]\nindent_size = 4\n\n[*.py] # python\nindent_size = 2\n"
                    )

                    let _, s1 = Configuration.readEditor root
                    let csFile = Path.Combine(root, "A.cs")

                    let eff1 =
                        Configuration.editorForFile (Some { Sections = s1; Parent = None }) csFile
                        |> Option.get

                    Expect.equal eff1.Printer.IndentSize 4 "[*.py] # python must close [*.cs]."

                    File.WriteAllText(
                        ecPath,
                        "root = false\n[*.cs] ; csharp [sub]\nindent_size = 3\n\n[*.py\nroot = true\nindent_size = 2\n"
                    )

                    let isRoot2, s2 = Configuration.readEditor root

                    let eff2 =
                        Configuration.editorForFile (Some { Sections = s2; Parent = None }) csFile
                        |> Option.get

                    Expect.isFalse isRoot2 "Malformed section must not revert to preamble root=."

                    Expect.equal
                        eff2.Printer.IndentSize
                        3
                        "[*.cs] ; comment applies and unclosed [*.py stops leakage."

                    File.WriteAllText(
                        ecPath,
                        "root = true\n[A[0].cs] # [comment]\nindent_size = 6\n"
                    )

                    let _, s3 = Configuration.readEditor root
                    let fileA0 = Path.Combine(root, "A0.cs")

                    let eff3 =
                        Configuration.editorForFile (Some { Sections = s3; Parent = None }) fileA0
                        |> Option.get

                    Expect.equal
                        eff3.Printer.IndentSize
                        6
                        "Section header with char class and comment matches."

                    File.WriteAllText(
                        ecPath,
                        "root = true\n[[!]]*.cs] # negated class starting with literal ']'\nindent_size = 7\n\n[File[]a].cs]\nindent_size = 5\n\n[foo]bar.cs] ; literal outer closing bracket\nindent_size = 8\n"
                    )

                    let _, s4 = Configuration.readEditor root
                    let scope4 = Some { Sections = s4; Parent = None }

                    let expectIndent (fileName: string) expectedIndent message =
                        let filePath = Path.Combine(root, fileName)

                        match Configuration.editorForFile scope4 filePath with
                        | Some eff -> Expect.equal eff.Printer.IndentSize expectedIndent message
                        | None -> failtestf "Expected .editorconfig match for %s" fileName

                    expectIndent "A.cs" 7 "[[!]]*.cs] # comment must match A.cs."
                    expectIndent "Filea.cs" 5 "[File[]a].cs] must match Filea.cs."
                    expectIndent "File].cs" 5 "[File[]a].cs] must match File].cs."
                    expectIndent "foo]bar.cs" 8 "[foo]bar.cs] ; comment must match foo]bar.cs."

                    File.WriteAllText(
                        ecPath,
                        "root = true\n[*]#*.cs]\nindent_size = 5\n\n[*];*.cs]\nindent_size = 6\n"
                    )

                    let _, s5 = Configuration.readEditor root
                    let scope5 = Some { Sections = s5; Parent = None }

                    let expectIndent5 (fileName: string) expectedIndent message =
                        let filePath = Path.Combine(root, fileName)

                        match Configuration.editorForFile scope5 filePath with
                        | Some eff -> Expect.equal eff.Printer.IndentSize expectedIndent message
                        | None -> failtestf "Expected .editorconfig match for %s" fileName

                    expectIndent5 "A.cs" 4 "[*]#*.cs] and [*];*.cs] must not match A.cs as '*'."

                    expectIndent5 "Report]#Old.cs" 5 "[*]#*.cs] must match Report]#Old.cs."
                    expectIndent5 "Report];Old.cs" 6 "[*];*.cs] must match Report];Old.cs."

                    File.WriteAllText(
                        ecPath,
                        "root = true\n[Foo.{cs,txt] #backup.cs}]\nindent_size = 5\n\n[Bar.{vb,{a] ;n,cs}}]\nindent_size = 6\n\n[{Baz,[}]}.cs] # trailing\nindent_size = 7\n"
                    )

                    let _, s6 = Configuration.readEditor root
                    let scope6 = Some { Sections = s6; Parent = None }

                    let expectIndent6 (fileName: string) expectedIndent message =
                        let filePath = Path.Combine(root, fileName)

                        match Configuration.editorForFile scope6 filePath with
                        | Some eff -> Expect.equal eff.Printer.IndentSize expectedIndent message
                        | None -> failtestf "Expected .editorconfig match for %s" fileName

                    expectIndent6 "Foo.cs" 5 "[Foo.{cs,txt] #backup.cs}] must apply to Foo.cs."

                    expectIndent6
                        "Foo.txt] #backup.cs"
                        5
                        "[Foo.{cs,txt] #backup.cs}] must match literal backup alt."

                    expectIndent6
                        "Bar.cs"
                        6
                        "[Bar.{vb,{a] ;n,cs}}] must keep nested brace alternatives intact."

                    expectIndent6
                        "}.cs"
                        7
                        "[{Baz,[}]}.cs] # trailing must not treat '}' inside char class as closing brace."

                    File.WriteAllText(
                        ecPath,
                        "root = true\n[*.{cs,txt] #backup}]\nindent_size = 5\n"
                    )

                    let _, s6b = Configuration.readEditor root

                    let eff6b =
                        Configuration.editorForFile
                            (Some { Sections = s6b; Parent = None })
                            (Path.Combine(root, "A.cs"))
                        |> Option.get

                    Expect.equal
                        eff6b.Printer.IndentSize
                        5
                        "[*.{cs,txt] #backup}] applies to A.cs.")
            }

            test "comments remain anchored to tokens and interpolation holes are checked" {
                let verifier = SyntaxPreservation.Checker()

                let expectCommentViolation label src (fmt: string) =
                    let expectViolation kindLabel v =
                        match v with
                        | SyntaxPreservation.Verification.Violation msg ->
                            Expect.stringContains
                                msg
                                "changed a comment"
                                $"Expected comment violation for %s{label} (%s{kindLabel}), got: %s{msg}"
                        | other ->
                            failtest
                                $"Expected Violation for %s{label} (%s{kindLabel}), got %A{other}."

                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse src tree

                    expectViolation
                        "Decide"
                        (verifier.Decide(
                            PrinterOptions.Default,
                            "Test.cs",
                            src,
                            fmt,
                            sourceTree = tree
                        ))

                    expectViolation
                        "DecideDirectSpan"
                        (verifier.DecideDirectSpan(
                            PrinterOptions.Default,
                            "Test.cs",
                            src,
                            fmt.AsSpan(),
                            tree,
                            TransformationWitness.None
                        ))

                    expectViolation
                        "AdjudicateDecision"
                        (verifier.AdjudicateDecision(PrinterOptions.Default, "Test.cs", src, fmt))

                let expectProven label src (fmt: string) =
                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse src tree

                    match
                        verifier.Decide(
                            PrinterOptions.Default,
                            "Test.cs",
                            src,
                            fmt,
                            sourceTree = tree
                        )
                    with
                    | SyntaxPreservation.Verification.Proven -> ()
                    | other -> failtest $"Expected Proven for %s{label}, got %A{other}."

                let swappedMethodDocsSrc =
                    lines
                        [
                            "class C"
                            "{"
                            "    /// <summary>A</summary>"
                            "    void A() { }"
                            "    /// <summary>B</summary>"
                            "    void B() { }"
                            "}"
                        ]

                let swappedMethodDocsFmt =
                    lines
                        [
                            "class C"
                            "{"
                            "    /// <summary>B</summary>"
                            "    void A() { }"
                            "    /// <summary>A</summary>"
                            "    void B() { }"
                            "}"
                        ]

                expectCommentViolation
                    "swapped doc comments between methods"
                    swappedMethodDocsSrc
                    swappedMethodDocsFmt

                let movedSingleDocSrc =
                    lines
                        [
                            "class C"
                            "{"
                            "    /// <summary>A</summary>"
                            "    void A() { }"
                            "    void B() { }"
                            "}"
                        ]

                let movedSingleDocFmt =
                    lines
                        [
                            "class C"
                            "{"
                            "    void A() { }"
                            "    /// <summary>A</summary>"
                            "    void B() { }"
                            "}"
                        ]

                expectCommentViolation
                    "single doc comment moved across methods"
                    movedSingleDocSrc
                    movedSingleDocFmt

                let movedFieldCommentSrc =
                    lines [ "class C"; "{"; "    int x = 1; // x"; "    int y = 2;"; "}" ]

                let movedFieldCommentFmt =
                    lines [ "class C"; "{"; "    int x = 1;"; "    int y = 2; // x"; "}" ]

                expectCommentViolation
                    "single line comment moved across fields"
                    movedFieldCommentSrc
                    movedFieldCommentFmt

                let usingWithMethodSwapSrc =
                    lines
                        [
                            "using B;"
                            "using A;"
                            "class C"
                            "{"
                            "    /// <summary>A</summary>"
                            "    void A() { }"
                            "    /// <summary>B</summary>"
                            "    void B() { }"
                            "}"
                        ]

                let usingWithMethodSwapFmt =
                    lines
                        [
                            "using A;"
                            "using B;"
                            "class C"
                            "{"
                            "    /// <summary>B</summary>"
                            "    void A() { }"
                            "    /// <summary>A</summary>"
                            "    void B() { }"
                            "}"
                        ]

                expectCommentViolation
                    "swapped method docs with sorted usings"
                    usingWithMethodSwapSrc
                    usingWithMethodSwapFmt

                let swappedUsingTrailSrc = lines [ "using Z; // zebra"; "using A; // alpha" ]
                let swappedUsingTrailFmt = lines [ "using A; // zebra"; "using Z; // alpha" ]

                expectCommentViolation
                    "swapped trailing comments on sorted usings"
                    swappedUsingTrailSrc
                    swappedUsingTrailFmt

                let swappedModRunDocsSrc =
                    lines
                        [
                            "/// <summary>A</summary>"
                            "unsafe public class A { }"
                            "/// <summary>B</summary>"
                            "unsafe public class B { }"
                        ]

                let swappedModRunDocsFmt =
                    lines
                        [
                            "/// <summary>B</summary>"
                            "public unsafe class A { }"
                            "/// <summary>A</summary>"
                            "public unsafe class B { }"
                        ]

                expectCommentViolation
                    "swapped doc comments across two permuted modifier runs"
                    swappedModRunDocsSrc
                    swappedModRunDocsFmt

                expectCommentViolation
                    "deleted comment inside interpolation hole"
                    "class C { string S(int x) => $\"{x /* note */}\"; }\n"
                    "class C { string S(int x) => $\"{x}\"; }\n"

                expectCommentViolation
                    "altered comment inside interpolation hole"
                    "class C { string S(int x) => $\"{x /* note */}\"; }\n"
                    "class C { string S(int x) => $\"{x /* forged */}\"; }\n"

                expectCommentViolation
                    "added comment inside interpolation hole"
                    "class C { string S(int x) => $\"{x}\"; }\n"
                    "class C { string S(int x) => $\"{x /* forged */}\"; }\n"

                expectCommentViolation
                    "deleted hole comment combined with sorted usings and trailing comma"
                    "using B;\nusing A;\nclass C { int[] a = { 1, 2 }; string S(int x) => $\"{x /* keep */}\"; }\n"
                    "using A;\nusing B;\nclass C { int[] a = { 1, 2, }; string S(int x) => $\"{x}\"; }\n"

                expectCommentViolation
                    "deleted hole comment before format specifier"
                    "class C { string S(int x) => $\"{x /* keep */:F2}\"; }\n"
                    "class C { string S(int x) => $\"{x:F2}\"; }\n"

                expectCommentViolation
                    "moved comment inside interpolation hole"
                    "class C { string S(int a, int b) => $\"{a /* c */ + b}\"; }\n"
                    "class C { string S(int a, int b) => $\"{a + b /* c */}\"; }\n"

                expectCommentViolation
                    "deleted comment inside nested interpolation hole"
                    "class C { string S(int y) => $\"outer {$\"{y /* inner */}\"}\"; }\n"
                    "class C { string S(int y) => $\"outer {$\"{y}\"}\"; }\n"

                expectCommentViolation
                    "interpolation with hole comment replaced by plain string"
                    "class C { string S(int x) => $\"{x /* lost */}\"; }\n"
                    "class C { string S(int x) => \"plain\"; }\n"

                expectCommentViolation
                    "plain string replaced by interpolation with hole comment"
                    "class C { string S(int x) => \"plain\"; }\n"
                    "class C { string S(int x) => $\"{x /* forged */}\"; }\n"

                let rawInterpSrc =
                    "class C\n{\n    string S(int x) => $$'''\n            {{x /* keep */}}\n            ''';\n}\n"
                        .Replace("'''", "\"\"\"")

                let rawInterpFmt =
                    "class C\n{\n    string S(int x) => $$'''\n        {{x /* keep */}}\n        ''';\n}\n"
                        .Replace("'''", "\"\"\"")

                expectProven
                    "reindented raw interpolation keeping hole comment"
                    rawInterpSrc
                    rawInterpFmt

                expectProven
                    "intact hole comment with formatted spacing"
                    "class C { string S(int x) => $\"{ x /* keep */ }\"; }\n"
                    "class C { string S(int x) => $\"{x /* keep */}\"; }\n"

                expectProven
                    "intact hole comment alongside trailing comma in hole"
                    "class C { string S() => $\"{new[] { 1 /* keep */ }}\"; }\n"
                    "class C { string S() => $\"{new[] { 1 /* keep */, }}\"; }\n"

                expectProven
                    "sorted usings with trailing comments kept on each directive"
                    "using Z; // z\nusing A; // a\n"
                    "using A; // a\nusing Z; // z\n"

                let sortedUsingInteriorDocSrc = "using Z\n/// a\n\n/// b\n;\nusing A;\n"

                let sortedUsingInteriorDocFmt =
                    GeneratedOutput.format PrinterOptions.Default sortedUsingInteriorDocSrc

                expectProven
                    "sorted usings with merged documentation comment inside clause"
                    sortedUsingInteriorDocSrc
                    sortedUsingInteriorDocFmt

                let sortedUsingLeadingDocSrc = "/// a\n\n/// b\nusing Z;\nusing A;\n"

                let sortedUsingLeadingDocFmt =
                    GeneratedOutput.format PrinterOptions.Default sortedUsingLeadingDocSrc

                expectProven
                    "sorted usings with merged leading documentation comment"
                    sortedUsingLeadingDocSrc
                    sortedUsingLeadingDocFmt

                expectCommentViolation
                    "file-leading semicolon followed by changed comment"
                    ";\n// a\nclass C {}\n"
                    ";\n// b\nclass C {}\n"

                let orderedUsingsPrefix =
                    Array.init 300 (fun n -> sprintf "using N%04d;\n" n) |> String.concat ""

                let orderedUsingsModSrc =
                    orderedUsingsPrefix + "// note\nstatic public class C {}\n"

                let orderedUsingsModFmt =
                    GeneratedOutput.format PrinterOptions.Default orderedUsingsModSrc

                expectProven
                    "ordered using run before permuted modifiers with comment"
                    orderedUsingsModSrc
                    orderedUsingsModFmt

                expectCommentViolation
                    "comment deleted inside ordered using run before permuted modifiers"
                    (orderedUsingsPrefix
                     + "using Z0; // a\nusing Z1; // b\nstatic public class C {}\n")
                    (orderedUsingsPrefix + "using Z0;\nusing Z1; // b\npublic static class C { }\n")

                let wrappedGenericUsingSrc =
                    lines
                        [
                            "using Z = System.Collections.Generic.Dictionary<string, System.Collections.Generic.List<System.Collections.Generic.List<int>>>; // z"
                            "using A = int; // a"
                            ""
                            "class C { }"
                        ]

                let wrappedGenericUsingFmt =
                    GeneratedOutput.format PrinterOptions.Default wrappedGenericUsingSrc

                expectProven
                    "sorted using aliases with wrapped split generic closers and comments"
                    wrappedGenericUsingSrc
                    wrappedGenericUsingFmt

                expectCommentViolation
                    "swapped comments on sorted using aliases with split generic closers"
                    wrappedGenericUsingSrc
                    (wrappedGenericUsingFmt
                        .Replace("// a", "// SWAPPED_A")
                        .Replace("// z", "// a")
                        .Replace("// SWAPPED_A", "// z"))

                let rawThenInterpThenModSrc =
                    lines
                        [
                            "class C"
                            "{"
                            "    string R = \"\"\""
                            "            hello"
                            "            \"\"\";"
                            "    string S(int x) => $\"{x /* keep */}\";"
                            "    static public void M() { }"
                            "}"
                        ]

                let rawThenInterpThenModFmt =
                    GeneratedOutput.format PrinterOptions.Default rawThenInterpThenModSrc

                expectProven
                    "unchanged interpolation with hole comment between reindented raw string and permuted modifiers"
                    rawThenInterpThenModSrc
                    rawThenInterpThenModFmt

                expectCommentViolation
                    "deleted hole comment inside interpolation between reindented raw string and permuted modifiers"
                    rawThenInterpThenModSrc
                    (rawThenInterpThenModFmt.Replace("/* keep */", ""))

                match
                    verifier.Decide(
                        PrinterOptions.Default,
                        "Div.cs",
                        "class C { string S(int a, int b) => $\"{a / b}\"; }\n",
                        "class C { string S(int a, int b) => $\"{a * b}\"; }\n"
                    )
                with
                | SyntaxPreservation.Verification.Unprovable msg ->
                    Expect.isFalse
                        (msg.Contains("changed a comment", StringComparison.Ordinal))
                        $"Division change must not claim a comment change: %s{msg}"
                | SyntaxPreservation.Verification.Violation msg ->
                    Expect.isFalse
                        (msg.Contains("changed a comment", StringComparison.Ordinal))
                        $"Division change must not claim a comment change: %s{msg}"
                | SyntaxPreservation.Verification.Proven ->
                    failtest "Changed operator in interpolation must not be Proven."

                let condFooterSrc =
                    lines
                        [
                            "#if true"
                            "using Z;"
                            "#endif"
                            "// tail"
                            "using A;"
                            "class C { int[] a = [1,]; }"
                        ]

                let condFooterFmt = GeneratedOutput.format PrinterOptions.Default condFooterSrc

                expectProven
                    "sorted using across #if frame carrying post-#endif tail comment"
                    condFooterSrc
                    condFooterFmt

                let condFooterWithDocSrc =
                    lines
                        [
                            "#if true"
                            "using Z;"
                            "#endif"
                            "// tail"
                            "using A;"
                            "// class doc"
                            "class C { int[] a = [1,]; }"
                        ]

                let condFooterWithDocFmt =
                    GeneratedOutput.format PrinterOptions.Default condFooterWithDocSrc

                expectProven
                    "sorted using across #if frame carrying post-#endif tail comment before class doc comment"
                    condFooterWithDocSrc
                    condFooterWithDocFmt

                expectCommentViolation
                    "class doc comment moved before #endif in sorted using run"
                    condFooterWithDocSrc
                    (lines
                        [
                            "using A;"
                            "#if true"
                            "// class doc"
                            "using Z;"
                            "#endif"
                            "// tail"
                            ""
                            "class C"
                            "{"
                            "    int[] a = [1];"
                            "}"
                        ])

                let condDupCommentSrc =
                    lines
                        [
                            "#if true"
                            "using Z;"
                            "#endif"
                            "// same"
                            "using A;"
                            "// same"
                            "class C { }"
                        ]

                expectCommentViolation
                    "deleted duplicate comment when #endif tail matches class comment"
                    condDupCommentSrc
                    (lines
                        [
                            "using A;"
                            "#if true"
                            "using Z;"
                            "#endif"
                            "// same"
                            ""
                            "class C { }"
                        ])

                let tailMismatchTime count =
                    let sbIn = System.Text.StringBuilder()
                    let sbOut = System.Text.StringBuilder()

                    for idx = count - 1 downto 1 do
                        let line = $"using U%05d{idx};\n"
                        sbIn.Append line |> ignore
                        sbOut.Append line |> ignore

                    sbIn.Append "using U00000; // tail\nclass C { }\n" |> ignore
                    sbOut.Append "// tail\nclass C { }\n" |> ignore
                    let src = sbIn.ToString()
                    let fmt = sbOut.ToString()
                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse src tree
                    let sw = System.Diagnostics.Stopwatch.StartNew()

                    let v =
                        verifier.Decide(
                            PrinterOptions.Default,
                            "TailMismatch.cs",
                            src,
                            fmt,
                            sourceTree = tree
                        )

                    sw.Stop()
                    v, sw.ElapsedMilliseconds

                let v2k, ms2k = tailMismatchTime 2000
                let v16k, ms16k = tailMismatchTime 16000

                match v2k, v16k with
                | SyntaxPreservation.Verification.Violation _,
                  SyntaxPreservation.Verification.Violation _ -> ()
                | other ->
                    failtest $"Expected violations for dropped trailing using, got %A{other}."

                Expect.isLessThan
                    ms16k
                    (max (ms2k * 30L) 2000L)
                    $"16k-using tail mismatch must avoid quadratic re-pairing (2k={ms2k}ms, 16k={ms16k}ms)."

                let condSwappedUsingComments =
                    "using Z; /* a */\nusing A; /* z */\n#if S\nclass C { int[] a = [1]; }\n#endif\n"

                expectProven
                    "swapped usings with plain trailing comments verify across lex-only conditional passes"
                    condSwappedUsingComments
                    (GeneratedOutput.format PrinterOptions.Default condSwappedUsingComments)

                let inOrderCondFrameSrc =
                    "#if A\nusing Z;\n#endif\n#if B\n// comment\n#endif\nusing X;\nusing Y;\n"

                let inOrderCondFrameFmt =
                    GeneratedOutput.format PrinterOptions.Default inOrderCondFrameSrc

                expectProven
                    "in-order multi-using run accepts conditional comment footer moved after run"
                    inOrderCondFrameSrc
                    inOrderCondFrameFmt

                expectCommentViolation
                    "moved conditional footer comment with changed text still fails"
                    "#if A\nusing Z;\n#endif\n#if B\n// evil\n#endif\nusing X;\n"
                    "using X;\n#if A\nusing Z;\n#endif\n#if B\n// moved\n#endif\n"

                expectCommentViolation
                    "in-order usings without conditional footer still reject swapped trailing comments"
                    "using X; // a\nusing Y; // b\n#if S\nclass C { }\n#endif\n"
                    "using X; // b\nusing Y; // a\n#if S\nclass C { }\n#endif\n"

                let splitHeaderMergedDocSrc =
                    "/// c\n\n/// d\n#if A\nusing Z;\n#endif\n/// t\nusing A;\nclass C {}\n"

                let splitHeaderMergedDocFmt = stable splitHeaderMergedDocSrc Settings.Default

                Expect.isTrue
                    (splitHeaderMergedDocFmt.Contains("/// d\n/// t", StringComparison.Ordinal))
                    "Split doc comment runs around conditional using frame merge cleanly."

                expectProven
                    "split header doc comments merged around conditional using frame verify across Check, Decide, and Adjudicate"
                    splitHeaderMergedDocSrc
                    splitHeaderMergedDocFmt

                let dupConditionalUsingSrc =
                    "#if true\nusing A; // inside\n#endif\nusing A; // outside\n"

                let dupConditionalUsingFmt = stable dupConditionalUsingSrc Settings.Default

                Expect.isTrue
                    (dupConditionalUsingFmt.StartsWith(
                        "using A; // outside",
                        StringComparison.Ordinal
                    ))
                    "Unconditional duplicate using sorts ahead of conditional duplicate."

                expectProven
                    "duplicate conditional and unconditional usings keep distinct comment placement"
                    dupConditionalUsingSrc
                    dupConditionalUsingFmt

                expectCommentViolation
                    "swapped comments across duplicate conditional and unconditional usings still fail"
                    dupConditionalUsingSrc
                    (dupConditionalUsingFmt
                        .Replace("// outside", "// SWAPPED")
                        .Replace("// inside", "// outside")
                        .Replace("// SWAPPED", "// inside"))

                let nestedInterpSb = System.Text.StringBuilder("class C {\n")

                for idx = 0 to 999 do
                    nestedInterpSb.Append(
                        $"    string S{idx}(int x) => $\"{{ $\"{{ x / 2 }}\" }}\";\n"
                    )
                    |> ignore

                nestedInterpSb.Append("}\n") |> ignore
                let nestedInterpSrc = nestedInterpSb.ToString()
                let nestedInterpFmt = nestedInterpSrc.Replace("x / 2", "x/2")
                let nestedInterpTree = Csff.Parser.SyntaxTree()
                Parser.parse nestedInterpSrc nestedInterpTree

                verifier.Decide(
                    PrinterOptions.Default,
                    "NestedInterpAlloc.cs",
                    nestedInterpSrc,
                    nestedInterpFmt,
                    sourceTree = nestedInterpTree
                )
                |> ignore

                let allocStart = GC.GetAllocatedBytesForCurrentThread()

                let nestedInterpVerdict =
                    verifier.Decide(
                        PrinterOptions.Default,
                        "NestedInterpAlloc.cs",
                        nestedInterpSrc,
                        nestedInterpFmt,
                        sourceTree = nestedInterpTree
                    )

                let allocBytes = GC.GetAllocatedBytesForCurrentThread() - allocStart

                Expect.equal
                    nestedInterpVerdict
                    SyntaxPreservation.Verification.Proven
                    "1000 nested interpolations with division spacing verify as Proven."

                Expect.isLessThan
                    allocBytes
                    5_000_000L
                    $"1000 nested interpolations must reuse pooled depth buffers cleanly (allocated {allocBytes} bytes)."

                let dupIgnoreBlockSrc =
                    "// csff-ignore-start\nusing X;\n// csff-ignore-end\nusing X;\nclass C {}\n"

                let dupIgnoreBlockFmt = stable dupIgnoreBlockSrc Settings.Default

                Expect.isTrue
                    (dupIgnoreBlockFmt.StartsWith(
                        "using X;\n// csff-ignore-start",
                        StringComparison.Ordinal
                    ))
                    "Unignored duplicate using sorts ahead of intact ignored block."

                expectProven
                    "duplicate usings across ignore block boundaries verify cleanly"
                    dupIgnoreBlockSrc
                    dupIgnoreBlockFmt

                let dupIgnoreCommentedSrc =
                    "// csff-ignore-start\nusing X; // in\n// csff-ignore-end\nusing X; // out\nclass C {}\n"

                let dupIgnoreCommentedFmt = stable dupIgnoreCommentedSrc Settings.Default

                expectProven
                    "commented duplicate usings across ignore block verify cleanly"
                    dupIgnoreCommentedSrc
                    dupIgnoreCommentedFmt

                expectCommentViolation
                    "swapped comments across ignored and unignored duplicate usings fail"
                    dupIgnoreCommentedSrc
                    (dupIgnoreCommentedFmt
                        .Replace("// out", "// SWAPPED")
                        .Replace("// in", "// out")
                        .Replace("// SWAPPED", "// in"))

                let dupSingleIgnoreSrc =
                    "// csff-ignore\nusing X; // a\nusing X; // b\nclass C {}\n"

                let dupSingleIgnoreFmt = stable dupSingleIgnoreSrc Settings.Default

                expectProven
                    "duplicate usings with single-line csff-ignore verify cleanly"
                    dupSingleIgnoreSrc
                    dupSingleIgnoreFmt

                expectCommentViolation
                    "swapped comments across single-line csff-ignore duplicate usings fail"
                    dupSingleIgnoreSrc
                    (dupSingleIgnoreFmt
                        .Replace("// b", "// SWAPPED")
                        .Replace("// a", "// b")
                        .Replace("// SWAPPED", "// a"))

                let lateDirectiveNsBench (nsCount: int) (withLateDirective: bool) =
                    let sbIn = System.Text.StringBuilder()
                    let sbOut = System.Text.StringBuilder()

                    for idx = 0 to nsCount - 1 do
                        sbIn.Append $"namespace N{idx} {{ using Z; using A; class C {{ }} }}\n"
                        |> ignore

                        sbOut.Append
                            $"namespace N{idx}\n{{\n    using A;\n    using Z;\n    class C {{ }}\n}}\n"
                        |> ignore

                    if withLateDirective then
                        sbIn.Append "// end\n#nullable enable\n" |> ignore
                        sbOut.Append "// end\n#nullable enable\n" |> ignore

                    let src = sbIn.ToString()
                    let fmt = sbOut.ToString()
                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse src tree

                    let sw = System.Diagnostics.Stopwatch.StartNew()

                    let v =
                        verifier.Decide(
                            PrinterOptions.Default,
                            "LateDirectiveNs.cs",
                            src,
                            fmt,
                            sourceTree = tree
                        )

                    sw.Stop()
                    v, sw.ElapsedMilliseconds

                let warmV, _ = lateDirectiveNsBench 10 true

                Expect.equal
                    warmV
                    SyntaxPreservation.Verification.Proven
                    "Namespace-local using runs with late #nullable directive verify as Proven."

                let v2kLate, ms2kLate = lateDirectiveNsBench 2000 true
                let v16kLate, ms16kLate = lateDirectiveNsBench 16000 true

                Expect.equal
                    v2kLate
                    SyntaxPreservation.Verification.Proven
                    "2k late-directive namespaces Proven."

                Expect.equal
                    v16kLate
                    SyntaxPreservation.Verification.Proven
                    "16k late-directive namespaces Proven."

                Expect.isLessThan
                    ms16kLate
                    (max (ms2kLate * 25L) 1500L)
                    $"16k namespace using runs with late #nullable directive must scale linearly (2k={ms2kLate}ms, 16k={ms16kLate}ms)."

                let untermIgnoreNsSrc =
                    "namespace N1 { // csff-ignore-start\nusing Z;\nusing A;\n}\nnamespace N2 {\n// csff-ignore\nusing X; // in\nusing X; // out\n}\n"

                let untermIgnoreNsFmt = stable untermIgnoreNsSrc Settings.Default

                expectProven
                    "unterminated ignore-start inside N1 ends at N1 closing brace"
                    untermIgnoreNsSrc
                    untermIgnoreNsFmt

                let nestedIgnoreEndClassSrc =
                    "namespace N1 {\n// csff-ignore-start\nusing Z;\nusing A;\nclass C {\n// csff-ignore-end\n}\n}\nnamespace N2 {\n// csff-ignore\nusing X; // in\nusing X; // out\n}\n"

                let nestedIgnoreEndClassFmt = stable nestedIgnoreEndClassSrc Settings.Default

                expectProven
                    "nested ignore-end inside class does not prematurely close N1 ignore range before N2"
                    nestedIgnoreEndClassSrc
                    nestedIgnoreEndClassFmt

                let untermTopUsingToNsSrc =
                    "// csff-ignore-start\nusing Z;\nnamespace N2 {\n// csff-ignore\nusing X; // in\nusing X; // out\n}\n"

                let untermTopUsingToNsFmt = stable untermTopUsingToNsSrc Settings.Default

                expectProven
                    "unterminated top-level using ignore-start does not leak into N2"
                    untermTopUsingToNsSrc
                    untermTopUsingToNsFmt

                let untermTopUsingToFileNsSrc =
                    "// csff-ignore-start\nusing Z;\nnamespace N2;\n// csff-ignore\nusing X; // in\nusing X; // out\n"

                let untermTopUsingToFileNsFmt = stable untermTopUsingToFileNsSrc Settings.Default

                expectProven
                    "unterminated top-level using ignore-start does not leak into file-scoped namespace"
                    untermTopUsingToFileNsSrc
                    untermTopUsingToFileNsFmt

                let nonMarkerSuffixSrc = "// csff-ignore nope\nusing Z; // z\nusing A; // a\n"
                let nonMarkerSuffixFmt = stable nonMarkerSuffixSrc Settings.Default

                expectProven
                    "comment starting with // csff-ignore without ' - ' explanation sorts normally"
                    nonMarkerSuffixSrc
                    nonMarkerSuffixFmt

                let explainedSingleIgnoreSrc =
                    "// csff-ignore - keep\nusing X; // in\nusing X; // out\nclass C { }\n"

                let explainedSingleIgnoreFmt = stable explainedSingleIgnoreSrc Settings.Default

                expectProven
                    "comment with valid ' - ' ignore explanation preserves ignore membership"
                    explainedSingleIgnoreSrc
                    explainedSingleIgnoreFmt

                let singleThenStartSrc =
                    "// csff-ignore\n// csff-ignore-start\nusing X; // s\nusing X; // out\n"

                let singleThenStartFmt = stable singleThenStartSrc Settings.Default

                expectProven
                    "leading single ignore marker suppresses subsequent range start on same token"
                    singleThenStartSrc
                    singleThenStartFmt

                let commentedNsBench (nsCount: int) =
                    let sbIn = System.Text.StringBuilder()
                    let sbOut = System.Text.StringBuilder()

                    for idx = 0 to nsCount - 1 do
                        sbIn.Append $"namespace N{idx} {{ using Z; // z\n using A; // a\n }}\n"
                        |> ignore

                        sbOut.Append
                            $"namespace N{idx}\n{{\n    using A; // a\n    using Z; // z\n}}\n"
                        |> ignore

                    let src = sbIn.ToString()
                    let fmt = sbOut.ToString()
                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse src tree
                    let sw = System.Diagnostics.Stopwatch.StartNew()

                    let v =
                        verifier.Decide(
                            PrinterOptions.Default,
                            "CommentedNs.cs",
                            src,
                            fmt,
                            sourceTree = tree
                        )

                    sw.Stop()
                    v, sw.ElapsedMilliseconds

                let warmCommentedV, _ = commentedNsBench 10

                Expect.equal
                    warmCommentedV
                    SyntaxPreservation.Verification.Proven
                    "Commented namespace-local using runs verify cleanly."

                let v2kCommented, ms2kCommented = commentedNsBench 2000
                let v16kCommented, ms16kCommented = commentedNsBench 16000

                Expect.equal
                    v2kCommented
                    SyntaxPreservation.Verification.Proven
                    "2k commented namespaces Proven."

                Expect.equal
                    v16kCommented
                    SyntaxPreservation.Verification.Proven
                    "16k commented namespaces Proven."

                Expect.isLessThan
                    ms16kCommented
                    (max (ms2kCommented * 25L) 1500L)
                    $"16k commented namespace using runs must scale linearly (2k={ms2kCommented}ms, 16k={ms16kCommented}ms)."

                let adjacentIgnoreDupSrc =
                    "// csff-ignore-start\nusing X; // a\n// csff-ignore-end\n// csff-ignore-start\nusing X; // b\n// csff-ignore-end\nclass C{}\n"

                let adjacentIgnoreDupFmt = stable adjacentIgnoreDupSrc Settings.Default

                expectProven
                    "adjacent closed ignore blocks with duplicate using clauses verify cleanly"
                    adjacentIgnoreDupSrc
                    adjacentIgnoreDupFmt

                expectCommentViolation
                    "swapped comments across adjacent closed ignore blocks fail"
                    adjacentIgnoreDupSrc
                    (adjacentIgnoreDupFmt
                        .Replace("// b", "// SWAPPED")
                        .Replace("// a", "// b")
                        .Replace("// SWAPPED", "// a"))

                let threeAdjacentIgnoreDupSrc =
                    "// csff-ignore-start\nusing X; // a\n// csff-ignore-end\n// csff-ignore-start\nusing X; // b\n// csff-ignore-end\n// csff-ignore-start\nusing X; // c\n// csff-ignore-end\nclass C{}\n"

                let threeAdjacentIgnoreDupFmt = stable threeAdjacentIgnoreDupSrc Settings.Default

                expectProven
                    "three adjacent closed ignore blocks with duplicate usings verify cleanly"
                    threeAdjacentIgnoreDupSrc
                    threeAdjacentIgnoreDupFmt

                let splitIgnoreDupSrc =
                    "// csff-ignore-start\nusing X; // a\n// csff-ignore-end\nusing A;\n// csff-ignore-start\nusing X; // b\n// csff-ignore-end\nclass C { }\n"

                let splitIgnoreDupFmt = stable splitIgnoreDupSrc Settings.Default

                expectProven
                    "separated closed ignore blocks with duplicate usings preserve source order"
                    splitIgnoreDupSrc
                    splitIgnoreDupFmt

                let headerStartDupSrc =
                    "// csff-ignore-start\n// csff-ignore-end\n// csff-ignore-start\nusing X; // a\n// csff-ignore-end\nusing X; // b\n"

                let headerStartDupFmt = stable headerStartDupSrc Settings.Default

                expectProven
                    "suppressed ignore-start after empty header ignore block pairs duplicate usings cleanly"
                    headerStartDupSrc
                    headerStartDupFmt

                let mergedDocNsBench (nsCount: int) =
                    let sbIn = System.Text.StringBuilder()
                    let sbOut = System.Text.StringBuilder()

                    for idx = 0 to nsCount - 1 do
                        sbIn.Append $"namespace N{idx} {{\nusing Z;\n/// a\n\n/// b\nusing A;\n}}\n"
                        |> ignore

                        sbOut.Append
                            $"namespace N{idx}\n{{\n    /// a\n    /// b\n    using A;\n    using Z;\n}}\n"
                        |> ignore

                    let src = sbIn.ToString()
                    let fmt = sbOut.ToString()
                    let tree = Csff.Parser.SyntaxTree()
                    Parser.parse src tree
                    let localVerifier = SyntaxPreservation.Checker()
                    let alloc0 = GC.GetAllocatedBytesForCurrentThread()

                    let v =
                        localVerifier.Decide(
                            PrinterOptions.Default,
                            "MergedDocNs.cs",
                            src,
                            fmt,
                            sourceTree = tree
                        )

                    v, GC.GetAllocatedBytesForCurrentThread() - alloc0

                let warmMergedV, _ = mergedDocNsBench 10

                Expect.equal
                    warmMergedV
                    SyntaxPreservation.Verification.Proven
                    "Merged doc namespace using runs verify cleanly."

                let v2kMergedDoc, alloc2kMergedDoc = mergedDocNsBench 2000

                Expect.equal
                    v2kMergedDoc
                    SyntaxPreservation.Verification.Proven
                    "2k merged-doc namespaces verify as Proven."

                Expect.isLessThan
                    alloc2kMergedDoc
                    15_000_000L
                    $"2k merged-doc namespaces must reuse bounded run metadata without quadratic allocation (allocated {alloc2kMergedDoc} bytes)."

                let largePlainReorderedSrc =
                    ([
                        for i = 75 downto 1 do
                            yield $"using U{i:D3};"
                     ]
                     @ [ "class C { }" ]
                     |> String.concat "\n")
                    + "\n"

                let largePlainReorderedFmt = stable largePlainReorderedSrc Settings.Default

                Expect.stringStarts
                    largePlainReorderedFmt
                    "using U001;"
                    "Large plain using run is sorted when formatted with default settings."

                expectProven
                    "large plain reordered using run (>64 clauses without comments or directives) verifies cleanly"
                    largePlainReorderedSrc
                    largePlainReorderedFmt

                let headerSuppressedEndStartSrc =
                    "// csff-ignore-end\n// csff-ignore-start\nusing Z;\nusing X; //first\nusing X; //second\nclass C { }\n"

                let headerSuppressedEndStartFmt =
                    stable headerSuppressedEndStartSrc Settings.Default

                expectProven
                    "suppressed file header ignore markers preserve duplicate using FIFO pairing"
                    headerSuppressedEndStartSrc
                    headerSuppressedEndStartFmt

                expectCommentViolation
                    "swapping duplicate using comments beneath suppressed header ignore markers fails"
                    headerSuppressedEndStartSrc
                    (headerSuppressedEndStartFmt
                        .Replace("//second", "// SWAPPED")
                        .Replace("//first", "//second")
                        .Replace("// SWAPPED", "//first"))

                let headerCloseBeforeBlockSrc =
                    "// csff-ignore-end\n// csff-ignore-start\nusing X; //first\n// csff-ignore-end\n// csff-ignore-start\nusing X; //second\n// csff-ignore-end\nclass C { }\n"

                let headerCloseBeforeBlockFmt = stable headerCloseBeforeBlockSrc Settings.Default

                expectProven
                    "suppressed file header marker before later ignore block pairs duplicates cleanly"
                    headerCloseBeforeBlockSrc
                    headerCloseBeforeBlockFmt

                let fileScopedNsHeaderSrc =
                    "global using G;\nnamespace N;\n// csff-ignore-end\n// csff-ignore-start\nusing Z;\nusing X; //first\nusing X; //second\nclass C { }\n"

                let fileScopedNsHeaderFmt = stable fileScopedNsHeaderSrc Settings.Default

                expectProven
                    "suppressed ignore marker at file-scoped namespace header pairs duplicate usings cleanly"
                    fileScopedNsHeaderSrc
                    fileScopedNsHeaderFmt

                let longSharedPrefix = String.replicate 35 "N."

                let longPrefixUsingSrc =
                    $"using {longSharedPrefix}Z; // z\nusing {longSharedPrefix}A; // a\nclass C {{ }}\n"

                let longPrefixUsingFmt = stable longPrefixUsingSrc Settings.Default

                expectProven
                    "reordered usings sharing >64-token prefix rewind to clause start without witness"
                    longPrefixUsingSrc
                    longPrefixUsingFmt

                expectCommentViolation
                    "swapping comments on >64-token shared-prefix usings fails"
                    longPrefixUsingSrc
                    (longPrefixUsingFmt
                        .Replace("// a", "// SWAPPED")
                        .Replace("// z", "// a")
                        .Replace("// SWAPPED", "// z"))

                let regionSeparatedIgnoreDupSrc =
                    "// csff-ignore-start\nusing System; // a\n// csff-ignore-end\n#region R\n#endregion\n// csff-ignore-start\nusing System; // b\n// csff-ignore-end\nclass C { int[] a = [1,]; }\n"

                let regionSeparatedIgnoreDupFmt =
                    stable regionSeparatedIgnoreDupSrc Settings.Default

                expectProven
                    "region-separated duplicate ignore blocks prefer exact ignore-state pairing"
                    regionSeparatedIgnoreDupSrc
                    regionSeparatedIgnoreDupFmt

                expectCommentViolation
                    "swapping comments across region-separated duplicate ignore blocks fails"
                    regionSeparatedIgnoreDupSrc
                    (regionSeparatedIgnoreDupFmt
                        .Replace("// b", "// SWAPPED")
                        .Replace("// a", "// b")
                        .Replace("// SWAPPED", "// a"))

                let ifSeparatedIgnoreDupSrc =
                    "// csff-ignore-start\nusing System; // a\n// csff-ignore-end\n#if A\n#endif\n// csff-ignore-start\nusing System; // b\n// csff-ignore-end\nclass C { int[] a = [1,]; }\n"

                let ifSeparatedIgnoreDupFmt = stable ifSeparatedIgnoreDupSrc Settings.Default

                expectProven
                    "conditional-separated duplicate ignore blocks prefer exact ignore-state pairing"
                    ifSeparatedIgnoreDupSrc
                    ifSeparatedIgnoreDupFmt

                let conditionalSameDocMergeSrc =
                    "using System;\n/// doc\n#if S\n/// doc\nusing System.IO;\n#endif\n/// doc\n/* note */\nusing System.Text;\nclass C { }\n"

                let conditionalSameDocMergeFmt = stable conditionalSameDocMergeSrc Settings.Default

                expectProven
                    "merged documentation resolves before common identical doc keys are consumed"
                    conditionalSameDocMergeSrc
                    conditionalSameDocMergeFmt

                expectCommentViolation
                    "dropping the trailing unchanged doc comment in merged conditional doc fails"
                    conditionalSameDocMergeSrc
                    (conditionalSameDocMergeFmt.Replace("#if S\n/// doc\n", "#if S\n"))

                let fnPtrAliasCondSrc =
                    "#if S\nusing B = long;\n#endif\nnamespace N\n{\n    using unsafe Z = delegate*<in int, out byte, void>; // z\n    using A = int; // a\n    class C { }\n}\n"

                let fnPtrAliasCondFmt = stable fnPtrAliasCondSrc Settings.Default

                expectProven
                    "token-only using scanner handles function-pointer parameter modifiers in conditional files"
                    fnPtrAliasCondSrc
                    fnPtrAliasCondFmt

                expectCommentViolation
                    "swapping trailing comments on sorted function-pointer using aliases fails"
                    fnPtrAliasCondSrc
                    (fnPtrAliasCondFmt
                        .Replace("// a", "// SWAPPED")
                        .Replace("// z", "// a")
                        .Replace("// SWAPPED", "// z"))

                let condFooterDocIgnoreEndSrc =
                    "using Z;\n#if true\nusing Y;\n#endif\nusing A;\n/// t\n// csff-ignore-end\nclass C { }\n"

                let condFooterDocIgnoreEndFmt = stable condFooterDocIgnoreEndSrc Settings.Default

                expectProven
                    "declaration doc comment followed by ignore-end is preserved after conditional using footer"
                    condFooterDocIgnoreEndSrc
                    condFooterDocIgnoreEndFmt

                expectCommentViolation
                    "dropping declaration doc comment before ignore-end after conditional using footer fails"
                    condFooterDocIgnoreEndSrc
                    (condFooterDocIgnoreEndFmt.Replace("/// t\n", ""))

                let condDisabledFooterDocEndSrc =
                    "using Z;\n#if S\nusing Y;\n#endif\nusing A;\n/// t\n// csff-ignore-end\nclass C { }\n"

                let condDisabledFooterDocEndFmt =
                    stable condDisabledFooterDocEndSrc Settings.Default

                expectProven
                    "declaration doc comment followed by ignore-end is preserved across disabled conditional footer"
                    condDisabledFooterDocEndSrc
                    condDisabledFooterDocEndFmt

                let footerIgnoreEndModRunSrc =
                    "using Z;\n// csff-ignore-start\nusing X;\n// csff-ignore-end\nusing A;\nstatic public class C { }\n"

                let footerIgnoreEndModRunFmt =
                    stableUnprovable footerIgnoreEndModRunSrc Settings.Default

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        footerIgnoreEndModRunSrc,
                        footerIgnoreEndModRunFmt
                    ))
                    SyntaxPreservation.Verification.Proven
                    "modifier run following consumed ignore-end using footer adjudicates as Proven"

                expectCommentViolation
                    "duplicating ignore-end marker across modifier run fails comment preservation"
                    footerIgnoreEndModRunSrc
                    (footerIgnoreEndModRunFmt.Replace(
                        "// csff-ignore-end\n",
                        "// csff-ignore-end\n// extra\n"
                    ))

                let condFooterModRunSrc =
                    "using Z;\n#if true\nusing Y;\n#endif\nusing A;\n/// t\n// csff-ignore-end\nstatic public class C { }\n"

                let condFooterModRunFmt = stable condFooterModRunSrc Settings.Default

                expectProven
                    "modifier run following conditional using footer preserves trailing declaration comment suffix"
                    condFooterModRunSrc
                    condFooterModRunFmt

                let afterEndifNoteSrc =
                    "using Z;\n#if true\nusing Y;\n#endif\n// after endif\nusing A;\n/// class document\n// csff-ignore-end\nclass C { }\n"

                let afterEndifNoteFmt = stable afterEndifNoteSrc Settings.Default

                expectProven
                    "post-endif note followed by declaration doc and ignore-end is preserved across sorted usings"
                    afterEndifNoteSrc
                    afterEndifNoteFmt

                expectCommentViolation
                    "moving post-endif using note inside #if frame fails comment preservation"
                    afterEndifNoteSrc
                    "using A;\nusing Z;\n#if true\n// after endif\nusing Y;\n#endif\n\n/// class document\n// csff-ignore-end\nclass C { }\n"

                expectCommentViolation
                    "moving post-endif note into leading #if frame fails comment preservation"
                    "#if true\nusing Y;\n#endif\n// after endif\nusing A;\n/// class document\n// csff-ignore-end\nclass C { }\n"
                    "using A;\n#if true\n// after endif\nusing Y;\n#endif\n\n/// class document\n// csff-ignore-end\nclass C { }\n"

                let fnPtrTopLeadingSrc =
                    "#if S\nusing B = long;\n#endif\nusing unsafe Z = delegate*<in int, out byte, void>;\n// ReSharper disable All\n// ReSharper restore All\nusing A = int;\n"

                let fnPtrTopLeadingFmt =
                    "// ReSharper disable All\n// ReSharper restore All\nusing A = int;\nusing unsafe Z = delegate* <in int, out byte, void>;\n#if S\nusing B = long;\n#endif\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        fnPtrTopLeadingSrc,
                        fnPtrTopLeadingFmt
                    ))
                    SyntaxPreservation.Verification.Proven
                    "top-level sorted function-pointer using aliases preserving consecutive leading comments adjudicate as Proven"

                expectCommentViolation
                    "reversing consecutive leading comments on top-level sorted function-pointer using aliases fails"
                    fnPtrTopLeadingSrc
                    (fnPtrTopLeadingFmt.Replace(
                        "// ReSharper disable All\n// ReSharper restore All",
                        "// ReSharper restore All\n// ReSharper disable All"
                    ))

                let fnPtrLeadingSrc =
                    "#if S\nusing B = long;\n#endif\nnamespace N\n{\n    using unsafe Z = delegate*<in int, out byte, void>;\n    // ReSharper disable All\n    // ReSharper restore All\n    using A = int;\n    class C { }\n}\n"

                let fnPtrLeadingFmt = stable fnPtrLeadingSrc Settings.Default

                expectProven
                    "sorting function-pointer using aliases preserves consecutive leading comment order"
                    fnPtrLeadingSrc
                    fnPtrLeadingFmt

                expectCommentViolation
                    "reversing consecutive leading comments on sorted function-pointer using aliases fails"
                    fnPtrLeadingSrc
                    (fnPtrLeadingFmt.Replace(
                        "    // ReSharper disable All\n    // ReSharper restore All",
                        "    // ReSharper restore All\n    // ReSharper disable All"
                    ))

                let fnPtrSwapLeadingSrc =
                    "#if S\nusing B = long;\n#endif\nnamespace N\n{\n    // z\n    using unsafe Z = delegate*<in int, out byte, void>;\n    // a\n    using A = int;\n    class C { }\n}\n"

                let fnPtrSwapLeadingFmt = stable fnPtrSwapLeadingSrc Settings.Default

                expectProven
                    "sorting function-pointer using aliases preserves each alias's own leading comment"
                    fnPtrSwapLeadingSrc
                    fnPtrSwapLeadingFmt

                expectCommentViolation
                    "swapping leading comments across sorted function-pointer using aliases fails"
                    fnPtrSwapLeadingSrc
                    (fnPtrSwapLeadingFmt
                        .Replace("// a", "// SWAPPED")
                        .Replace("// z", "// a")
                        .Replace("// SWAPPED", "// z"))

                let footerDocModRunSrc =
                    "using A;\n#if true\nusing B;\n#endif\n/// class document\nstatic public class C { }\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        footerDocModRunSrc,
                        "using A;\n#if true\nusing B;\n#endif\n/// class document\npublic static class C { }\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "declaration doc kept after #endif ahead of sorted modifier run adjudicates as Proven"

                expectCommentViolation
                    "moving declaration doc before #endif ahead of sorted modifier run fails comment preservation"
                    footerDocModRunSrc
                    "using A;\n#if true\n/// class document\nusing B;\n#endif\npublic static class C { }\n"

                expectCommentViolation
                    "moving declaration doc before #endif ahead of unpermuted modifier run fails comment preservation"
                    footerDocModRunSrc
                    "using A;\n#if true\n/// class document\nusing B;\n#endif\nstatic public class C { }\n"

                let headerBeforeConditionalSrc =
                    "// License\n#if FEATURE\nusing B;\n#endif\nusing C;\nusing A;\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        headerBeforeConditionalSrc,
                        "// License\nusing A;\nusing C;\n#if FEATURE\nusing B;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "file header before leading conditional block stays on first sorted using"

                expectCommentViolation
                    "moving file header onto second sorted using fails comment preservation"
                    headerBeforeConditionalSrc
                    "using A;\n// License\nusing C;\n#if FEATURE\nusing B;\n#endif\n"

                expectCommentViolation
                    "pulling file header inside conditional block fails comment preservation"
                    headerBeforeConditionalSrc
                    "using A;\nusing C;\n#if FEATURE\n// License\nusing B;\n#endif\n"

                let headerAndInnerSrc =
                    "// License\n#if FEATURE\n// inner B\nusing B;\n#endif\nusing C;\nusing A;\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        headerAndInnerSrc,
                        "// License\nusing A;\nusing C;\n#if FEATURE\n// inner B\nusing B;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "file header stays on first sorted using while inner comment stays inside conditional block"

                expectCommentViolation
                    "lifting inner conditional comment alongside file header onto first sorted using fails"
                    headerAndInnerSrc
                    "// License\n// inner B\nusing A;\nusing C;\n#if FEATURE\nusing B;\n#endif\n"

                let intermediateBoundarySrc =
                    "#if true\nusing B;\n#endif\n// note\nusing A;\n#if true\nusing C;\n#endif\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        intermediateBoundarySrc,
                        "using A;\n#if true\nusing B;\n#endif\n// note\n#if true\nusing C;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "post-endif comment preserved at intermediate conditional boundary adjudicates as Proven"

                expectCommentViolation
                    "pulling intermediate post-endif comment inside following conditional block fails"
                    intermediateBoundarySrc
                    "using A;\n#if true\nusing B;\n#endif\n#if true\n// note\nusing C;\n#endif\n"

                expectCommentViolation
                    "moving intermediate post-endif comment after final #endif fails"
                    intermediateBoundarySrc
                    "using A;\n#if true\nusing B;\n#endif\n#if true\nusing C;\n#endif\n// note\n"

                let twoBoundaryNotesSrc =
                    "#if true\nusing B;\n#endif\n// note 1\n// note 2\nusing A;\n#if true\nusing C;\n#endif\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        twoBoundaryNotesSrc,
                        "using A;\n#if true\nusing B;\n#endif\n// note 1\n// note 2\n#if true\nusing C;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "multiple post-endif comments stay ordered at intermediate conditional boundary"

                expectCommentViolation
                    "swapping post-endif comments at intermediate conditional boundary fails"
                    twoBoundaryNotesSrc
                    "using A;\n#if true\nusing B;\n#endif\n// note 2\n// note 1\n#if true\nusing C;\n#endif\n"

                let innerBeforeEndifSrc =
                    "#if true\nusing B;\n// inside B\n#endif\nusing A;\n#if true\nusing C;\n#endif\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        innerBeforeEndifSrc,
                        "using A;\n#if true\nusing B;\n// inside B\n#endif\n#if true\nusing C;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "trailing inside-if comment stays ahead of closing #endif when next using hoists"

                let combinedHeaderAndMidBoundarySrc =
                    "// License\n#if F1\nusing Z;\n#endif\n// mid\n#if F2\nusing Y;\n#endif\nusing A;\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        combinedHeaderAndMidBoundarySrc,
                        "// License\nusing A;\n#if F1\nusing Z;\n#endif\n// mid\n#if F2\nusing Y;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "file header and intermediate post-endif boundary comment both preserve across displaced conditional usings"

                let repeatedSb = System.Text.StringBuilder()

                for _ = 1 to 2000 do
                    repeatedSb.Append("// same\n") |> ignore

                let repeatedBlock = repeatedSb.ToString()

                let repeatedClauseWithFooterSrc =
                    "using Z;\n#if true\nusing B;\n#endif\n"
                    + repeatedBlock
                    + "using A;\n// same\nclass C { }\n"

                let repeatedClauseWithFooterOut =
                    repeatedBlock
                    + "using A;\nusing Z;\n#if true\nusing B;\n#endif\n// same\nclass C { }\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        repeatedClauseWithFooterSrc,
                        repeatedClauseWithFooterOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "large repeated comment block alongside matching footer adjudicates cleanly"

                expectCommentViolation
                    "moving footer comment up onto hoisted using in repeated block fails"
                    repeatedClauseWithFooterSrc
                    (repeatedBlock
                     + "// same\nusing A;\nusing Z;\n#if true\nusing B;\n#endif\nclass C { }\n")

                let footerLinesSb = System.Text.StringBuilder()

                for i = 1 to 16000 do
                    footerLinesSb.Append("// documentation line ").Append(i).Append('\n') |> ignore

                let footerLines = footerLinesSb.ToString()

                let largeFooterSrc =
                    "using Z;\n#if true\nusing B;\n#endif\n"
                    + footerLines
                    + "using A;\nclass C { }\n"

                let largeFooterOut =
                    "using A;\nusing Z;\n#if true\nusing B;\n#endif\n"
                    + footerLines
                    + "class C { }\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        largeFooterSrc,
                        largeFooterOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "large distinct using-run footer adjudicates cleanly"

                let swappedFooterSb = System.Text.StringBuilder()

                swappedFooterSb.Append("// documentation line 2\n// documentation line 1\n")
                |> ignore

                for i = 3 to 16000 do
                    swappedFooterSb.Append("// documentation line ").Append(i).Append('\n')
                    |> ignore

                expectCommentViolation
                    "reordering large using-run footer fails comment preservation"
                    largeFooterSrc
                    ("using A;\nusing Z;\n#if true\nusing B;\n#endif\n"
                     + swappedFooterSb.ToString()
                     + "class C { }\n")

                let deepClauseSb = System.Text.StringBuilder()

                for _ = 1 to 20000 do
                    deepClauseSb.Append("// note\n") |> ignore

                let deepNotes = deepClauseSb.ToString()

                let deepClauseWithFooterMarkerSrc =
                    "using Z;\n" + deepNotes + "// csff-ignore-end\nusing A;\nclass D {}\n"

                let deepClauseWithFooterMarkerOut =
                    deepNotes + "using A;\nusing Z;\n// csff-ignore-end\nclass D { }\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        deepClauseWithFooterMarkerSrc,
                        deepClauseWithFooterMarkerOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "deep leading comment run with trailing footer marker runs iteratively without stack overflow"

                let deepSameDiagonalSrc =
                    "using Z;\n" + deepNotes + "// csff-ignore-end\nusing A;\n// note\nclass D {}\n"

                let deepSameDiagonalOut =
                    deepNotes + "using A;\nusing Z;\n// csff-ignore-end\n// note\nclass D { }\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        deepSameDiagonalSrc,
                        deepSameDiagonalOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "deep leading comment run sharing text with footer reuses no-skip failure memo linearly"

                let regionHoistSrc =
                    "#region R\nusing Y;\n#endregion\n// note\nusing Z;\n#if S\nusing A;\n#endif\n"

                let regionHoistFmt = stable regionHoistSrc Settings.Default

                expectProven
                    "hoisting using with attached comment into #region ahead of disabled #if verifies cleanly"
                    regionHoistSrc
                    regionHoistFmt

                expectCommentViolation
                    "splitting attached comment out of #region while using enters #region fails"
                    regionHoistSrc
                    "// note\n#region R\nusing Y;\nusing Z;\n#endregion\n#if S\nusing A;\n#endif\n"

                let regionFooterSrc =
                    "#region R\nusing Z;\n#endregion\n#if S\nusing B;\n#endif\nusing A;\n// footer\n"

                expectCommentViolation
                    "moving detached using footer inside #region fails"
                    regionFooterSrc
                    "#region R\nusing A;\nusing Z;\n// footer\n#endregion\n#if S\nusing B;\n#endif\n"

                let fileHeaderBeforeRegionSrc =
                    "// License\n#region R\nusing Z;\n#endregion\n#if S\nusing B;\n#endif\nusing A;\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        fileHeaderBeforeRegionSrc,
                        "// License\nusing A;\n#region R\nusing Z;\n#endregion\n#if S\nusing B;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "file header outside #region stays at depth 0 on first hoisted using"

                let ignoreEndBeforeCondSrc =
                    "// csff-ignore-start\nusing Z;\n// csff-ignore-end\nusing A;\n#if S\nusing B;\n#endif\n"

                let ignoreEndBeforeCondFmt = stable ignoreEndBeforeCondSrc Settings.Default

                expectProven
                    "ignore-end marker outside first conditional survives sorting ordinary using ahead"
                    ignoreEndBeforeCondSrc
                    ignoreEndBeforeCondFmt

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        ignoreEndBeforeCondSrc,
                        "using A;\n// csff-ignore-start\nusing Z;\n// csff-ignore-end\n#if S\nusing B;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "explicit ignore-end marker before first #if adjudicates as Proven"

                expectCommentViolation
                    "moving ignore-end marker inside first conditional fails"
                    ignoreEndBeforeCondSrc
                    "using A;\n// csff-ignore-start\nusing Z;\n#if S\n// csff-ignore-end\nusing B;\n#endif\n"

                expectCommentViolation
                    "moving ordinary comment before first conditional alongside ignore-end fails"
                    "// csff-ignore-start\nusing Z;\n// csff-ignore-end\n// extra\nusing A;\n#if S\nusing B;\n#endif\n"
                    "using A;\n// csff-ignore-start\nusing Z;\n// csff-ignore-end\n// extra\n#if S\nusing B;\n#endif\n"

                let mergedDocAcrossFooterSrc =
                    "/// alpha\n#if S\nusing Z;\n/// alpha\n#endif\n/// beta\nusing A;\n"

                let mergedDocAcrossFooterFmt = stable mergedDocAcrossFooterSrc Settings.Default

                expectProven
                    "merged outer doc comments across inner conditional footer doc verify cleanly"
                    mergedDocAcrossFooterSrc
                    mergedDocAcrossFooterFmt

                expectCommentViolation
                    "dropping inner conditional footer doc comment from merged outer doc fails"
                    mergedDocAcrossFooterSrc
                    (mergedDocAcrossFooterFmt.Replace(
                        "#if S\nusing Z;\n/// alpha\n",
                        "#if S\nusing Z;\n"
                    ))

                expectCommentViolation
                    "merging inner conditional footer doc comment into outer using doc fails"
                    mergedDocAcrossFooterSrc
                    "/// alpha\n/// alpha\n/// beta\nusing A;\n#if S\nusing Z;\n#endif\n"

                let same3200Sb = System.Text.StringBuilder()
                let same1600Sb = System.Text.StringBuilder()

                for _ = 1 to 3200 do
                    same3200Sb.Append("// same\n") |> ignore

                for _ = 1 to 1600 do
                    same1600Sb.Append("// same\n") |> ignore

                let same3200 = same3200Sb.ToString()
                let same1600 = same1600Sb.ToString()

                let lateMismatchSameSrc =
                    "using Z;\n#if true\nusing B;\n#endif\n"
                    + same3200
                    + "using A;\n"
                    + same1600
                    + "class C { }\n"

                let lateMismatchSameOut =
                    same1600
                    + "// changed\nusing A;\nusing Z;\n#if true\nusing B;\n#endif\n"
                    + same1600
                    + "class C { }\n"

                let swSameMismatch = Stopwatch.StartNew()

                expectCommentViolation
                    "late mismatch in 3200 repeated comments fails quickly without O(N^2) grid or hash collisions"
                    lateMismatchSameSrc
                    lateMismatchSameOut

                swSameMismatch.Stop()

                Expect.isLessThan
                    swSameMismatch.ElapsedMilliseconds
                    1500L
                    $"3200 repeated comment late-mismatch check must stay linear (took {swSameMismatch.ElapsedMilliseconds}ms)."

                let anchorSplitSameSrc =
                    "using Z;\n#if true\nusing B;\n#endif\n"
                    + same1600
                    + "// anchor\n"
                    + same1600
                    + "using A;\n"
                    + same1600
                    + "class C { }\n"

                let anchorSplitSameOut =
                    same1600
                    + "// anchor\nusing A;\nusing Z;\n#if true\nusing B;\n#endif\n"
                    + same3200
                    + "class C { }\n"

                let swAnchorSplit = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        anchorSplitSameSrc,
                        anchorSplitSameOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "split repeated comments around mandatory anchor adjudicate cleanly"

                swAnchorSplit.Stop()

                Expect.isLessThan
                    swAnchorSplit.ElapsedMilliseconds
                    1500L
                    $"Anchored repeated-comment split must stay linear (took {swAnchorSplit.ElapsedMilliseconds}ms)."

                expectCommentViolation
                    "exceeding mandatory-anchor prefix count in repeated comments fails"
                    anchorSplitSameSrc
                    (same1600
                     + "// same\n// anchor\nusing A;\nusing Z;\n#if true\nusing B;\n#endif\n"
                     + same1600
                     + same1600.Substring("// same\n".Length)
                     + "class C { }\n")

                let inner64kSb = System.Text.StringBuilder()

                for i = 1 to 32000 do
                    inner64kSb.Append("// inner ").Append(i).Append('\n') |> ignore

                let inner32k = inner64kSb.ToString()

                let largeInnerHeaderSrc =
                    "// License\n#if FEATURE\n"
                    + inner32k
                    + "using Z;\n#endif\nusing A;\n// footer\nclass C { }\n"

                let largeInnerHeaderOut =
                    "// License\nusing A;\n#if FEATURE\n"
                    + inner32k
                    + "using Z;\n#endif\n// footer\nclass C { }\n"

                let swLargeInner = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        largeInnerHeaderSrc,
                        largeInnerHeaderOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "single movable header ahead of 32k inner guarded comments adjudicates cleanly"

                swLargeInner.Stop()

                Expect.isLessThan
                    swLargeInner.ElapsedMilliseconds
                    2000L
                    $"Header split bounded to movable prefix must run linearly (took {swLargeInner.ElapsedMilliseconds}ms)."

                let hashBlocksA = System.Text.StringBuilder()
                let hashBlocksB = System.Text.StringBuilder()

                for i = 1 to 2000 do
                    hashBlocksA.Append("/* C# example ").Append(i).Append(" */\n") |> ignore
                    hashBlocksB.Append("/* C# footer ").Append(i).Append(" */\n") |> ignore

                let hashBlocksAStr = hashBlocksA.ToString()
                let hashBlocksBStr = hashBlocksB.ToString()

                let ordinaryHashBlocksSrc =
                    "using Z;\n#if true\nusing B;\n#endif\n"
                    + hashBlocksBStr
                    + hashBlocksAStr
                    + "using A;\nclass C { }\n"

                let ordinaryHashBlocksOut =
                    hashBlocksAStr
                    + "using A;\nusing Z;\n#if true\nusing B;\n#endif\n"
                    + hashBlocksBStr
                    + "class C { }\n"

                let swHashBlocks = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        ordinaryHashBlocksSrc,
                        ordinaryHashBlocksOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "thousands of ordinary #-containing block comments verify cleanly"

                expectCommentViolation
                    "tampered ordinary #-containing block comment fails quickly without quadratic spanning scan"
                    ordinaryHashBlocksSrc
                    ("/* C# tampered */\n"
                     + hashBlocksAStr.Substring("/* C# example 1 */\n".Length)
                     + "using A;\nusing Z;\n#if true\nusing B;\n#endif\n"
                     + hashBlocksBStr
                     + "class C { }\n")

                swHashBlocks.Stop()

                Expect.isLessThan
                    swHashBlocks.ElapsedMilliseconds
                    1500L
                    $"Ordinary #-containing block comments must skip directive-spanning fallback (took {swHashBlocks.ElapsedMilliseconds}ms)."

                let dirSpanningUsingSrc =
                    "using Z;\n#if S\n/* head\n#if false\ndead\n#else\nlive\n#endif\ntail */\nusing B;\n#endif\nusing A;\n"

                let dirSpanningUsingOut =
                    "using A;\nusing Z;\n#if S\n/* head\n#if false\ndead\n#else\nlive\n#endif\ntail */\nusing B;\n#endif\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        dirSpanningUsingSrc,
                        dirSpanningUsingOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "indexed directive-spanning multiline footer comment verifies cleanly"

                let boundary8kSb = System.Text.StringBuilder()
                let guarded2kSrcSb = System.Text.StringBuilder()
                let guarded2kOutSb = System.Text.StringBuilder()

                for i = 1 to 8000 do
                    boundary8kSb.Append("// outer ").Append(i).Append('\n') |> ignore

                for i = 2000 downto 1 do
                    guarded2kSrcSb.Append("using U").Append(i.ToString("D4")).Append(";\n")
                    |> ignore

                for i = 1 to 2000 do
                    guarded2kOutSb.Append("using U").Append(i.ToString("D4")).Append(";\n")
                    |> ignore

                let boundary8k = boundary8kSb.ToString()

                let largeBoundaryGuardedSrc =
                    "#if F1\nusing Z;\n#endif\n"
                    + boundary8k
                    + "#if F2\n"
                    + guarded2kSrcSb.ToString()
                    + "#endif\n"

                let largeBoundaryGuardedOut =
                    "#if F1\nusing Z;\n#endif\n"
                    + boundary8k
                    + "#if F2\n"
                    + guarded2kOutSb.ToString()
                    + "#endif\n"

                let swBoundaryLookup = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        largeBoundaryGuardedSrc,
                        largeBoundaryGuardedOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "8k boundary comments ahead of 2k guarded clauses adjudicate without O(B*C) scan"

                swBoundaryLookup.Stop()

                Expect.isLessThan
                    swBoundaryLookup.ElapsedMilliseconds
                    1500L
                    $"Cached next-clause frame lookup must stay linear (took {swBoundaryLookup.ElapsedMilliseconds}ms)."

                let stationaryRegionSrc =
                    "using Z;\n#region R\n// note\n#if X\nusing Y;\n#endif\n#endregion\nusing A;\nclass D {}\n"

                let stationaryRegionFmt = stable stationaryRegionSrc Settings.Default

                expectProven
                    "stationary #region comment stays Proven when outer using is hoisted inside"
                    stationaryRegionSrc
                    stationaryRegionFmt

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        stationaryRegionSrc,
                        "using Z;\n#region R\n// note\nusing A;\n#if X\nusing Y;\n#endif\n#endregion\nclass D {}\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "stationary #region comment at unchanged depth adjudicates cleanly across #endregion hoist"

                expectCommentViolation
                    "moving stationary #region comment out of #region fails"
                    stationaryRegionSrc
                    "using Z;\n// note\n#region R\nusing A;\n#if X\nusing Y;\n#endif\n#endregion\nclass D {}\n"

                let mergedDocBoundarySrc =
                    "/// head\n#if X\nusing Z;\n#endif\n/// doc\n#if X\nusing Y;\n#endif\n/// doc\nusing B;\nclass D {}\n"

                let mergedDocBoundaryFmt = stable mergedDocBoundarySrc Settings.Default

                expectProven
                    "merged /// doc comments across matching boundary doc survive formatting"
                    mergedDocBoundarySrc
                    mergedDocBoundaryFmt

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        mergedDocBoundarySrc,
                        "/// head\n/// doc\nusing B;\n#if X\nusing Z;\n#endif\n/// doc\n#if X\nusing Y;\n#endif\nclass D {}\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "merged /// doc skips matching boundary doc to preserve boundary comment"

                expectCommentViolation
                    "dropping boundary /// doc absorbed into merged header fails"
                    mergedDocBoundarySrc
                    "/// head\n/// doc\nusing B;\n#if X\nusing Z;\nusing Y;\n#endif\nclass D {}\n"

                let alt2kInSb = System.Text.StringBuilder()
                let alt1kOutSb = System.Text.StringBuilder()

                for _ = 1 to 2000 do
                    alt2kInSb.Append("// alt a\n// alt b\n") |> ignore

                for _ = 1 to 1000 do
                    alt1kOutSb.Append("// alt a\n// alt b\n") |> ignore

                let altUnmatchedSrc =
                    "using Z;\n#if S\nusing B;\n#endif\n"
                    + alt2kInSb.ToString()
                    + "// mandatory missing\nusing A;\nclass C { }\n"

                let altUnmatchedOut =
                    "using A;\n"
                    + alt1kOutSb.ToString()
                    + "using Z;\n#if S\nusing B;\n#endif\n// alt a\n// alt b\nclass C { }\n"

                let swAltPrune = Stopwatch.StartNew()

                expectCommentViolation
                    "alternating footer-eligible run ending in unmatched mandatory comment fails fast"
                    altUnmatchedSrc
                    altUnmatchedOut

                swAltPrune.Stop()

                Expect.isLessThan
                    swAltPrune.ElapsedMilliseconds
                    1500L
                    $"Mandatory backward/forward pruning must bound alternating-run failure (took {swAltPrune.ElapsedMilliseconds}ms)."

                let h32kSb = System.Text.StringBuilder()

                for _ = 1 to 32000 do
                    h32kSb.Append("// header rep\n") |> ignore

                let h32k = h32kSb.ToString()

                let headerSplit32kSrc =
                    h32k
                    + "using Z;\n#if S\nusing B;\n#endif\n"
                    + h32k
                    + "// footer\nusing A;\nclass C { }\n"

                let headerSplit32kOut =
                    h32k
                    + "using A;\n"
                    + h32k
                    + "using Z;\n#if S\nusing B;\n#endif\n// footer\nclass C { }\n"

                let swHeaderSplit32k = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        headerSplit32kSrc,
                        headerSplit32kOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "32k repeated headers with reordered footer adjudicate linearly"

                swHeaderSplit32k.Stop()

                Expect.isLessThan
                    swHeaderSplit32k.ElapsedMilliseconds
                    1500L
                    $"Header split verification with footer must stay linear (took {swHeaderSplit32k.ElapsedMilliseconds}ms)."

                let h16kSb = System.Text.StringBuilder()

                for _ = 1 to 16000 do
                    h16kSb.Append("// header rep\n") |> ignore

                let h16k = h16kSb.ToString()

                let headerSplitNegSrc =
                    h16k
                    + "using Z;\n#if S\nusing B;\n#endif\n"
                    + h16k
                    + "// footer\nusing A;\nclass C { }\n"

                let headerSplitNegOut =
                    h16k
                    + "using A;\n// missing\nusing Z;\n#if S\nusing B;\n#endif\n// footer\nclass C { }\n"

                let swHeaderSplitNeg = Stopwatch.StartNew()

                expectCommentViolation
                    "16k repeated headers failing unmatched j0 with footer-eligible prefix fail fast"
                    headerSplitNegSrc
                    headerSplitNegOut

                swHeaderSplitNeg.Stop()

                Expect.isLessThan
                    swHeaderSplitNeg.ElapsedMilliseconds
                    1500L
                    $"Negative repeated header split across footer-eligible run must stay linear (took {swHeaderSplitNeg.ElapsedMilliseconds}ms)."

                let stationaryFirstCondSrc =
                    "using Z;\n// note\n#if X\n#else\nusing B;\n#endif\nusing A;\n#if Y\nusing M;\n#endif\n"

                let stationaryFirstCondFmt = stable stationaryFirstCondSrc Settings.Default

                expectProven
                    "stationary comment before first conditional survives hoisting later using"
                    stationaryFirstCondSrc
                    stationaryFirstCondFmt

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        stationaryFirstCondSrc,
                        "using A;\nusing Z;\n// note\n#if X\n#else\nusing B;\n#endif\n#if Y\nusing M;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "stationary comment before first #if with inactive branch matches across hoisted using"

                expectCommentViolation
                    "file header on first using cannot move before first conditional closed block"
                    "// header\nusing Z;\n#if X\n#else\nusing B;\n#endif\nusing A;\n#if Y\nusing M;\n#endif\n"
                    "using A;\nusing Z;\n// header\n#if X\n#else\nusing B;\n#endif\n#if Y\nusing M;\n#endif\n"

                let regionMergedFooterDocSrc =
                    "#region R\n#if true\nusing A;\n#endif\n/// doc1\n\n/// doc2\n#endregion\nclass C {}\n"

                let regionMergedFooterDocFmt = stable regionMergedFooterDocSrc Settings.Default

                expectProven
                    "merged /// doc comments between #endif and #endregion verify in footer suffix"
                    regionMergedFooterDocSrc
                    regionMergedFooterDocFmt

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        regionMergedFooterDocSrc,
                        "#region R\n#if true\nusing A;\n#endif\n/// doc1\n/// doc2\n#endregion\nclass C { }\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "footer suffix recognizes merged /// documentation trivia inside #region"

                expectCommentViolation
                    "reordering merged /// docs between #endif and #endregion fails"
                    regionMergedFooterDocSrc
                    "#region R\n#if true\nusing A;\n#endif\n/// doc2\n/// doc1\n#endregion\nclass C { }\n"

                let dupClauseOrderedFooterSrc =
                    "#if X\nusing Z;\n#endif\n// a\n// b\n// a\nusing A;\n#if Y\nusing B;\n#endif\n"

                let dupClauseOrderedFooterOut =
                    "// a\nusing A;\n#if X\nusing Z;\n#endif\n// b\n// a\n#if Y\nusing B;\n#endif\n"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        dupClauseOrderedFooterSrc,
                        dupClauseOrderedFooterOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "duplicate clause comment consumes earliest copy so ordered footer matches"

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        dupClauseOrderedFooterSrc,
                        "// a\nusing A;\n#if X\nusing Z;\n#endif\n// a\n// b\n#if Y\nusing B;\n#endif\n"
                    ))
                    SyntaxPreservation.Verification.Proven
                    "duplicate clause comment consumes last copy when ordered footer needs earlier pair"

                expectCommentViolation
                    "duplicate clause comments that invert ordered footer fail"
                    "#if X\nusing Z;\n#endif\n// a\n// a\n// b\nusing A;\n#if Y\nusing B;\n#endif\n"
                    "// a\nusing A;\n#if X\nusing Z;\n#endif\n// b\n// a\n#if Y\nusing B;\n#endif\n"

                let alt20InSb = System.Text.StringBuilder()
                let altOutSb = System.Text.StringBuilder()
                let altFooterSb = System.Text.StringBuilder()

                for _ = 1 to 20 do
                    alt20InSb.Append("// a\n// b\n") |> ignore

                for _ = 1 to 10 do
                    altOutSb.Append("// a\n") |> ignore

                for _ = 1 to 9 do
                    altOutSb.Append("// b\n") |> ignore

                for _ = 1 to 11 do
                    altFooterSb.Append("// b\n") |> ignore

                for _ = 1 to 10 do
                    altFooterSb.Append("// a\n") |> ignore

                let swAltOrdered = Stopwatch.StartNew()

                expectCommentViolation
                    "alternating duplicate skips pruned incrementally by ordered footer capacity"
                    ("#if X\nusing Z;\n#endif\n" + alt20InSb.ToString() + "using A;\nclass C {}\n")
                    (altOutSb.ToString()
                     + "using A;\n#if X\nusing Z;\n#endif\n"
                     + altFooterSb.ToString()
                     + "class C { }\n")

                swAltOrdered.Stop()

                Expect.isLessThan
                    swAltOrdered.ElapsedMilliseconds
                    1500L
                    $"Ordered footer pruning must avoid exponential backtracking (took {swAltOrdered.ElapsedMilliseconds}ms)."

                let rep8kSb = System.Text.StringBuilder()
                let docs8kSplitSb = System.Text.StringBuilder()
                let docs8kMergedSb = System.Text.StringBuilder()

                for _ = 1 to 8000 do
                    rep8kSb.Append("// same\n") |> ignore
                    docs8kSplitSb.Append("/// doc\n\n") |> ignore
                    docs8kMergedSb.Append("/// doc\n") |> ignore

                let rep8k = rep8kSb.ToString()
                let rep8kPlus1 = rep8k + "// same\n"

                let mergedDocHeaderSplitSrc =
                    rep8k
                    + docs8kSplitSb.ToString()
                    + "using Z;\n#if true\nusing B;\n#endif\n"
                    + rep8kPlus1
                    + "using A;\nclass C {}\n"

                let mergedDocHeaderSplitOut =
                    rep8k
                    + "using A;\n"
                    + rep8k
                    + docs8kMergedSb.ToString()
                    + "using Z;\n#if true\nusing B;\n#endif\n// same\nclass C { }\n"

                let swMergedDocSplit = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        mergedDocHeaderSplitSrc,
                        mergedDocHeaderSplitOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "8k repeated headers with merged /// doc block on displaced using prove linearly"

                swMergedDocSplit.Stop()

                Expect.isLessThan
                    swMergedDocSplit.ElapsedMilliseconds
                    1500L
                    $"Merged doc header split bounds must stay linear (took {swMergedDocSplit.ElapsedMilliseconds}ms)."

                let dupFloatingRetrySrc =
                    "#if true\nusing Z;\n#endif\n// x\nusing M;\n// x\n#if EMPTY\n#endif\n// x\n#if SYM\nusing V;\n#endif\nusing A;\nclass C {}\n"

                let dupFloatingRetryFmt = stable dupFloatingRetrySrc Settings.Default

                expectProven
                    "duplicate comments across floating and conditional clauses retry footer assignments"
                    dupFloatingRetrySrc
                    dupFloatingRetryFmt

                let dupOneRenamed =
                    let firstPos = dupFloatingRetryFmt.IndexOf("// x", StringComparison.Ordinal)

                    dupFloatingRetryFmt.Substring(0, firstPos)
                    + "// y"
                    + dupFloatingRetryFmt.Substring(firstPos + 4)

                expectCommentViolation
                    "altering one duplicate comment after floating/conditional retry fails"
                    dupFloatingRetrySrc
                    dupOneRenamed

                let dupSameOrderSrc =
                    "using A;\n// x\nusing Z;\n// x\n#if EMPTY\n#endif\n// x\n#if SYM\nusing V;\n#endif\nusing M;\nclass C {}\n"

                expectProven
                    "duplicate comments in non-displaced first run also retry footer assignments"
                    dupSameOrderSrc
                    (stable dupSameOrderSrc Settings.Default)

                let boundaryDocOrderSrc =
                    "#if true\nusing A;\n#endif\n/// x\nusing V;\n/// y\n#if true\nusing M;\n#endif\nclass C {}\n"

                let boundaryDocOrderFmt = stable boundaryDocOrderSrc Settings.Default

                expectProven
                    "merged boundary docs from earlier displaced outer using prove in source order"
                    boundaryDocOrderSrc
                    boundaryDocOrderFmt

                expectCommentViolation
                    "reordered or altered merged boundary doc text fails verification"
                    boundaryDocOrderSrc
                    (boundaryDocOrderFmt.Replace("/// x", "/// w", StringComparison.Ordinal))

                let boundaryDoc3WaySrc =
                    "/// x\n#if true\nusing Z;\n#endif\n/// y\nusing M;\n/// z\n#if true\nusing B;\n#endif\nusing A;\nclass C {}\n"

                expectProven
                    "three-way merged boundary doc split proves across header split and displaced clauses"
                    boundaryDoc3WaySrc
                    (stable boundaryDoc3WaySrc Settings.Default)

                let doc800BlankSb = System.Text.StringBuilder()
                let doc800MergedSb = System.Text.StringBuilder()

                for _ = 1 to 800 do
                    doc800BlankSb.Append("/// doc\n\n") |> ignore
                    doc800MergedSb.Append("/// doc\n") |> ignore

                let doc800Src =
                    "#if true\nusing Z;\n#endif\n"
                    + doc800BlankSb.ToString()
                    + "using B;\n#if SYM\nusing V;\n#endif\n/// doc\nusing A;\nclass C {}\n"

                let swDoc800Fmt = Stopwatch.StartNew()
                let doc800Fmt = stable doc800Src Settings.Default

                expectProven
                    "800 blank-separated /// doc lines format and prove without cubic backtracking"
                    doc800Src
                    doc800Fmt

                swDoc800Fmt.Stop()

                Expect.isLessThan
                    swDoc800Fmt.ElapsedMilliseconds
                    1500L
                    $"800 blank-separated /// doc formatting must stay fast (took {swDoc800Fmt.ElapsedMilliseconds}ms)."

                let doc800NegSrc =
                    "using Z;\n#if S\nusing B;\n#endif\n/// doc\n"
                    + doc800BlankSb.ToString()
                    + "using A;\nclass C {}\n"

                let doc800NegOut =
                    "using A;\n"
                    + doc800MergedSb.ToString()
                    + "/// nope\nusing Z;\n#if S\nusing B;\n#endif\n/// doc\nclass C { }\n"

                let swDoc800Neg = Stopwatch.StartNew()

                expectCommentViolation
                    "800 blank-separated /// doc mismatch with footer doc fails without cubic backtracking"
                    doc800NegSrc
                    doc800NegOut

                swDoc800Neg.Stop()

                Expect.isLessThan
                    swDoc800Neg.ElapsedMilliseconds
                    1500L
                    $"800 blank-separated /// doc mismatch must fail fast (took {swDoc800Neg.ElapsedMilliseconds}ms)."

                let distinctClauseSb = System.Text.StringBuilder()
                let distinctFooterSb = System.Text.StringBuilder()
                let distinctDocClauseSb = System.Text.StringBuilder()
                let distinctDocFooterSb = System.Text.StringBuilder()

                for i = 0 to 15999 do
                    distinctClauseSb.Append("// c").Append(i).Append('\n') |> ignore
                    distinctFooterSb.Append("// f").Append(i).Append('\n') |> ignore
                    distinctDocClauseSb.Append("/// dc").Append(i).Append("\n\n") |> ignore
                    distinctDocFooterSb.Append("/// df").Append(i).Append("\n\n") |> ignore

                let distinct16kSrc =
                    distinctClauseSb.ToString()
                    + "using Z;\n#if S\nusing B;\n#endif\n"
                    + distinctFooterSb.ToString()
                    + distinctClauseSb.ToString()
                    + "using A;\nclass C {}\n"

                let distinct16kOut =
                    "using A;\n"
                    + distinctClauseSb.ToString()
                    + "using Z;\n#if S\nusing B;\n#endif\n"
                    + distinctFooterSb.ToString()
                    + distinctClauseSb.ToString()
                    + "class C { }\n"

                let swDistinct16k = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        distinct16kSrc,
                        distinct16kOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "16k distinct comments in both clause and footer adjudicate via indexed lookups"

                swDistinct16k.Stop()

                Expect.isLessThan
                    swDistinct16k.ElapsedMilliseconds
                    1500L
                    $"Indexed ordered footer lookup must avoid quadratic scan on 16k comments (took {swDistinct16k.ElapsedMilliseconds}ms)."

                let distinctDoc16kSrc =
                    distinctDocClauseSb.ToString()
                    + "using Z;\n#if S\nusing B;\n#endif\n"
                    + distinctDocFooterSb.ToString()
                    + distinctDocClauseSb.ToString()
                    + "using A;\nclass C {}\n"

                let distinctDoc16kOut =
                    "using A;\n"
                    + distinctDocClauseSb.ToString()
                    + "using Z;\n#if S\nusing B;\n#endif\n"
                    + distinctDocFooterSb.ToString()
                    + distinctDocClauseSb.ToString()
                    + "class C { }\n"

                let swDistinctDoc16k = Stopwatch.StartNew()

                Expect.equal
                    (verifier.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        distinctDoc16kSrc,
                        distinctDoc16kOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "16k distinct /// doc comments in both clause and footer adjudicate via indexed lookups"

                swDistinctDoc16k.Stop()

                Expect.isLessThan
                    swDistinctDoc16k.ElapsedMilliseconds
                    1500L
                    $"Indexed doc footer lookup must avoid quadratic scan on 16k docs (took {swDistinctDoc16k.ElapsedMilliseconds}ms)."

                let buildSharedPrefixDocs (kind: string) split n =
                    let sb = System.Text.StringBuilder()

                    for i = 1 to n do
                        sb.AppendFormat("/// intro\n/// {0}{1}\n", kind, i) |> ignore

                        if split then
                            sb.Append('\n') |> ignore

                        sb.AppendFormat("/// extra\n// sep {0}{1}\n", kind, i) |> ignore

                    sb.ToString()

                let doc65Src =
                    "using System;\n#if true\nusing Z;\n#endif\n"
                    + buildSharedPrefixDocs "C" true 65
                    + "using M;\n"
                    + buildSharedPrefixDocs "F" true 65
                    + "using A;\nclass C {}\n"

                let doc65Fmt = stable doc65Src Settings.Default
                let freshChecker65 = SyntaxPreservation.Checker()

                Expect.equal
                    (freshChecker65.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        doc65Src,
                        doc65Fmt
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Fresh checker proves 65+ multi-line footer doc comments across hash-array growth"

                let doc5kSrc =
                    "using System;\n#if true\nusing Z;\n#endif\n"
                    + buildSharedPrefixDocs "C" true 5000
                    + "using M;\n"
                    + buildSharedPrefixDocs "F" true 5000
                    + "using A;\nclass C {}\n"

                let doc5kOut =
                    "using System;\nusing A;\n"
                    + buildSharedPrefixDocs "C" false 5000
                    + "using M;\n#if true\nusing Z;\n#endif\n"
                    + buildSharedPrefixDocs "F" false 5000
                    + "class C { }\n"

                let doc5kFmt = stable doc5kSrc Settings.Default
                let swDoc5kFmt = Stopwatch.StartNew()
                let freshChecker5kFmt = SyntaxPreservation.Checker()

                Expect.equal
                    (freshChecker5kFmt.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        doc5kSrc,
                        doc5kFmt
                    ))
                    SyntaxPreservation.Verification.Proven
                    "Formatted 5000 shared-prefix multi-line clause/footer docs prove cleanly"

                swDoc5kFmt.Stop()

                Expect.isLessThan
                    swDoc5kFmt.ElapsedMilliseconds
                    1500L
                    $"5000 shared-prefix formatted multi-line docs must scale linearly (took {swDoc5kFmt.ElapsedMilliseconds}ms)."

                let swDoc5kOut = Stopwatch.StartNew()
                let freshChecker5kOut = SyntaxPreservation.Checker()

                Expect.equal
                    (freshChecker5kOut.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        doc5kSrc,
                        doc5kOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "5000 shared-prefix merged clause and footer docs prove without quadratic bucket or suffix scans"

                swDoc5kOut.Stop()

                Expect.isLessThan
                    swDoc5kOut.ElapsedMilliseconds
                    1500L
                    $"5000 shared-prefix merged docs must stay linear (took {swDoc5kOut.ElapsedMilliseconds}ms)."

                let doc1kNegSrc =
                    "using System;\n#if true\nusing Z;\n#endif\n"
                    + buildSharedPrefixDocs "C" true 1000
                    + "using M;\n"
                    + buildSharedPrefixDocs "F" true 1000
                    + "using A;\nclass C {}\n"

                let doc1kNegOut =
                    "using System;\nusing A;\n"
                    + buildSharedPrefixDocs "C" false 999
                    + "/// intro\n/// C1000\n/// altered\n// sep C1000\n"
                    + "using M;\n#if true\nusing Z;\n#endif\n"
                    + buildSharedPrefixDocs "F" false 1000
                    + "class C { }\n"

                Expect.notEqual
                    ((SyntaxPreservation.Checker())
                        .AdjudicateDecision(
                            PrinterOptions.Default,
                            "Review.cs",
                            doc1kNegSrc,
                            doc1kNegOut
                        ))
                    SyntaxPreservation.Verification.Proven
                    "Shared-prefix multi-line doc mutation is rejected as a comment violation"

                let midDupSrc =
                    "#if true\nusing V;\n#endif\n/// X\nusing Z;\n/// X\n\n/// Y\n#if true\nusing E;\n#endif\nclass C {}\n"

                let midDupFmt = stable midDupSrc Settings.Default

                expectProven
                    "Merged boundary doc block with repeated /// X before /// Y formats and proves cleanly"
                    midDupSrc
                    midDupFmt

                expectCommentViolation
                    "Altering /// Y in merged repeated-line boundary doc block is rejected"
                    midDupSrc
                    (midDupFmt.Replace("/// Y", "/// W"))

                let midDupTripleSrc =
                    "#if true\nusing V;\n#endif\n/// X\n\n/// X\nusing Z;\n/// X\n\n/// Y\n#if true\nusing E;\n#endif\nclass C {}\n"

                let midDupTripleFmt = stable midDupTripleSrc Settings.Default

                expectProven
                    "Merged boundary doc block with multiple preceding /// X lines proves cleanly"
                    midDupTripleSrc
                    midDupTripleFmt

                let buildVariedEvictCase count =
                    let sbCIn = System.Text.StringBuilder()
                    let sbCOut = System.Text.StringBuilder()
                    let sbFIn = System.Text.StringBuilder()
                    let sbFOut = System.Text.StringBuilder()

                    for i = 1 to count do
                        let extra = i % 20
                        sbCIn.Append("/// L1\n/// L2\n") |> ignore
                        sbCOut.Append("/// L1\n/// L2\n") |> ignore
                        sbFIn.Append("/// head\n/// L1\n/// L2\n") |> ignore
                        sbFOut.Append("/// head\n/// L1\n/// L2\n") |> ignore

                        for e = 1 to extra do
                            sbCIn.AppendFormat("/// pad{0}\n", e) |> ignore
                            sbCOut.AppendFormat("/// pad{0}\n", e) |> ignore
                            sbFIn.AppendFormat("/// pad{0}\n", e) |> ignore
                            sbFOut.AppendFormat("/// pad{0}\n", e) |> ignore

                        sbCIn.AppendFormat("/// C{0}\n\n/// Cend\n// sepC{0}\n", i) |> ignore
                        sbCOut.AppendFormat("/// C{0}\n/// Cend\n// sepC{0}\n", i) |> ignore
                        sbFIn.AppendFormat("/// F{0}\n\n/// Fend\n// sepF{0}\n", i) |> ignore
                        sbFOut.AppendFormat("/// F{0}\n/// Fend\n// sepF{0}\n", i) |> ignore

                    let src =
                        "#if true\nusing V;\n#endif\n/// H0\nusing A;\n"
                        + sbCIn.ToString()
                        + "using M;\n"
                        + sbFIn.ToString()
                        + "#if true\nusing E;\n#endif\nclass C {}\n"

                    let out =
                        "using A;\n"
                        + sbCOut.ToString()
                        + "using M;\n#if true\nusing V;\n#endif\n/// H0\n"
                        + sbFOut.ToString()
                        + "#if true\nusing E;\n#endif\nclass C { }\n"

                    src, out

                let evict5kSrc, evict5kOut = buildVariedEvictCase 5000
                let swEvict5k = Stopwatch.StartNew()

                Expect.equal
                    ((SyntaxPreservation.Checker())
                        .AdjudicateDecision(
                            PrinterOptions.Default,
                            "Review.cs",
                            evict5kSrc,
                            evict5kOut
                        ))
                    SyntaxPreservation.Verification.Proven
                    "5k shared-prefix varied-length clause/footer docs prove via min-bucket fallback"

                swEvict5k.Stop()

                Expect.isLessThan
                    swEvict5k.ElapsedMilliseconds
                    1500L
                    $"Varied-length doc-block fallback on 5k shared-prefix pairs must avoid quadratic scan (took {swEvict5k.ElapsedMilliseconds}ms)."

                let evictNegSrc, evictNegOut = buildVariedEvictCase 400

                Expect.notEqual
                    ((SyntaxPreservation.Checker())
                        .AdjudicateDecision(
                            PrinterOptions.Default,
                            "Review.cs",
                            evictNegSrc,
                            evictNegOut.Replace("/// C400\n", "/// C400_altered\n")
                        ))
                    SyntaxPreservation.Verification.Proven
                    "Mutating an evicted shared-prefix varied-length doc line is rejected"

                expectCommentViolation
                    "moving a using XML doc down into a declaration XML doc block is rejected"
                    "#if true\n/// <summary>Import note.</summary>\nusing System;\n/// <remarks>Class remarks.</remarks>\n#endif\npublic class C {}\n"
                    "#if true\nusing System;\n/// <summary>Import note.</summary>\n/// <remarks>Class remarks.</remarks>\n#endif\npublic class C {}\n"

                expectCommentViolation
                    "swapped usings cannot merge a using XML doc into the declaration XML doc footer"
                    "#if true\n/// <summary>Import note.</summary>\nusing B;\nusing A;\n/// <remarks>Class remarks.</remarks>\n#endif\npublic class C {}\n"
                    "#if true\nusing A;\nusing B;\n/// <summary>Import note.</summary>\n/// <remarks>Class remarks.</remarks>\n#endif\npublic class C {}\n"

                expectCommentViolation
                    "using XML doc cannot merge into declaration XML doc after an intermediate boundary"
                    "/// <summary>Import note.</summary>\nusing A;\n#if B\nusing Foo;\n#endif\n/// <remarks>Class remarks.</remarks>\npublic class C {}\n"
                    "using A;\n#if B\nusing Foo;\n#endif\n/// <summary>Import note.</summary>\n/// <remarks>Class remarks.</remarks>\npublic class C {}\n"

                let p1DisplacedOut =
                    stable
                        "#if true\n/// <summary>Import note.</summary>\nusing B;\nusing A;\n/// <remarks>Class remarks.</remarks>\n#endif\npublic class C {}\n"
                        Settings.Default

                expectProven
                    "displaced using XML doc remains valid on its own line"
                    "#if true\n/// <summary>Import note.</summary>\nusing B;\nusing A;\n/// <remarks>Class remarks.</remarks>\n#endif\npublic class C {}\n"
                    p1DisplacedOut

                let p2MergedHeaderSrc =
                    "/// header\n#if Y\nusing Z;\n#endif\n/// same\n#if EMPTY\n#endif\n/// same\nusing M;\n/// same\n#if Y\nusing Y;\n#endif\nclass C {}\n"

                let p2MergedHeaderOut = stable p2MergedHeaderSrc Settings.Default

                expectProven
                    "merged header filling output slot retries alternate split cleanly"
                    p2MergedHeaderSrc
                    p2MergedHeaderOut

                expectCommentViolation
                    "mutating retried merged header comment is rejected"
                    p2MergedHeaderSrc
                    (p2MergedHeaderOut.Replace("/// header", "/// other"))

                let p2StationarySrc =
                    "namespace N {\n#if S\nusing Z;\n#endif\n// note\n#if E\n#endif\nusing M;\n// csff-ignore-start\nusing Y;\n// csff-ignore-end\nclass C {}\n}\n"

                let p2StationaryOut = stable p2StationarySrc Settings.Default

                expectProven
                    "stationary comment before same-frame empty conditional and ignore-start proves"
                    p2StationarySrc
                    p2StationaryOut

                expectCommentViolation
                    "adversarial move of stationary comment across unmoved using is rejected"
                    "namespace N {\n#if S\nusing Z;\n#endif\n// note\nusing M;\n#if E\n#endif\nusing Y;\nclass C {}\n}\n"
                    "namespace N {\n#if S\nusing Z;\n#endif\nusing M;\n// note\n#if E\n#endif\nusing Y;\nclass C {}\n}\n"

                let perm100kInSb = StringBuilder()
                let perm100kOutSb = StringBuilder()
                perm100kOutSb.Append("using A;\n") |> ignore

                for i = 99999 downto 1 do
                    perm100kInSb.AppendLine(sprintf "using N%06d;" i) |> ignore

                for i = 1 to 99999 do
                    perm100kOutSb.AppendLine(sprintf "using N%06d;" i) |> ignore

                perm100kInSb.Append("#if true\nusing Z;\n#endif\nusing A;\n// decl\nclass B {}\n")
                |> ignore

                perm100kOutSb.Append("#if true\nusing Z;\n#endif\n// decl\nclass B { }\n")
                |> ignore

                let perm100kSrc = perm100kInSb.ToString()
                let perm100kOut = perm100kOutSb.ToString()
                let retryChecker = SyntaxPreservation.Checker()
                let swPerm100k = Stopwatch.StartNew()

                Expect.equal
                    (retryChecker.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        perm100kSrc,
                        perm100kOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "100k reversed uncommented usings with declaration footer prove cleanly"

                swPerm100k.Stop()

                Expect.isLessThan
                    swPerm100k.ElapsedMilliseconds
                    1500L
                    $"100k reversed uncommented usings must verify fast (took {swPerm100k.ElapsedMilliseconds}ms)."

                let tokField =
                    typeof<SyntaxPreservation.Checker>
                        .GetField(
                            "tokens",
                            System.Reflection.BindingFlags.Instance
                            ||| System.Reflection.BindingFlags.NonPublic
                        )

                let tokChecker = tokField.GetValue retryChecker

                let retryStatesField =
                    tokChecker
                        .GetType()
                        .GetFields(
                            System.Reflection.BindingFlags.Instance
                            ||| System.Reflection.BindingFlags.NonPublic
                        )
                    |> Array.find (fun fi -> fi.Name.StartsWith "runSlotRetryStates")

                let retryStatesArr = retryStatesField.GetValue tokChecker :?> Array

                let nonNullRetryStates =
                    let mutable n = 0

                    if not (isNull retryStatesArr) then
                        for item in retryStatesArr do
                            if not (isNull item) then
                                n <- n + 1

                    n

                Expect.equal
                    nonNullRetryStates
                    0
                    "Unambiguous clauses allocate zero UsingSlotRetryState instances"

                let inertSrcA =
                    "#if A\n#endif\n// csff-ignore-end\n#if B\n#endif\nusing C;\nclass D {}\n"

                let inertOutA = stable inertSrcA Settings.Default

                expectProven
                    "inert csff-ignore-end proves across empty conditionals"
                    inertSrcA
                    inertOutA

                let inertSrcB =
                    "#if A\nusing Z;\n#endif\n// csff-ignore-end\n#if B\n#endif\nusing M;\nclass D {}\n"

                let inertOutB = stable inertSrcB Settings.Default

                expectProven
                    "inert csff-ignore-end proves alongside permuted conditional using"
                    inertSrcB
                    inertOutB

                expectCommentViolation
                    "moving csff-ignore-end across non-empty conditional using is rejected"
                    "// csff-ignore-end\n#if B\nusing X;\n#endif\nusing C;\nclass D {}\n"
                    "#if B\nusing X;\n#endif\n// csff-ignore-end\nusing C;\nclass D {}\n"

                expectCommentViolation
                    "moving csff-ignore-end across non-empty conditional comment is rejected"
                    "// csff-ignore-end\n#if B\n// inner\n#endif\nusing C;\nclass D {}\n"
                    "#if B\n// inner\n#endif\n// csff-ignore-end\nusing C;\nclass D {}\n"

                expectCommentViolation
                    "moving active csff-ignore-end out of conditional arm is rejected"
                    "// csff-ignore-start\nusing Z;\n#if B\n// csff-ignore-end\n#endif\nusing A;\nclass D {}\n"
                    "using A;\n// csff-ignore-start\nusing Z;\n#if B\n#endif\n// csff-ignore-end\nclass D {}\n"

                let r9SameEmptySrc =
                    "using A;\n// note\n#if F\n#endif\nusing Z;\n#if F\n#endif\nusing B;\nclass C {}\n"

                let r9SameEmptyOut = stable r9SameEmptySrc Settings.Default

                expectProven
                    "comment before identical empty conditional stays paired across sorting"
                    r9SameEmptySrc
                    r9SameEmptyOut

                let r9MovedBehindSrc =
                    "using C;\n// note\n#if F\n#endif\nusing Z;\n#if F\n#endif\nusing B;\nclass C {}\n"

                let r9MovedBehindOut = stable r9MovedBehindSrc Settings.Default

                expectProven
                    "comment before identical empty conditional proves when third clause sorts first"
                    r9MovedBehindSrc
                    r9MovedBehindOut

                let r9MergedDocEmptySrc =
                    "using A;\n/// a\n\n/// b\n#if F\n#endif\nusing Z;\n#if F\n#endif\nusing B;\nclass C {}\n"

                let r9MergedDocEmptyOut = stable r9MergedDocEmptySrc Settings.Default

                expectProven
                    "merged doc lines before traveling empty conditional stay paired"
                    r9MergedDocEmptySrc
                    r9MergedDocEmptyOut

                expectCommentViolation
                    "adversarial move of comment before empty conditional within sorted slot is rejected"
                    "using A;\n#if F\n#endif\n// note\nusing Z;\nusing B;\nclass C {}\n"
                    "using A;\nusing B;\n// note\n#if F\n#endif\nusing Z;\nclass C {}\n"

                expectCommentViolation
                    "adversarial cross-clause move before empty conditional is rejected"
                    "using A;\n// note\n#if F\n#endif\nusing B;\n#if G\n#endif\nusing Z;\nclass C {}\n"
                    "using A;\n#if F\n#endif\nusing B;\n// note\n#if G\n#endif\nusing Z;\nclass C {}\n"

                let r9InertRegionSrc =
                    "#if A\n#endif\n// csff-ignore-end\n#region R\n#endregion\nusing B;\nusing A;\nclass C {}\n"

                let r9InertRegionOut = stable r9InertRegionSrc Settings.Default

                expectProven
                    "inert csff-ignore-end proves when moving past empty #region after empty #if"
                    r9InertRegionSrc
                    r9InertRegionOut

                let r9InertRegionEmptyIfSrc =
                    "#if A\n#endif\n// csff-ignore-end\n#region R\n#endregion\n#if B\n#endif\nusing B;\nusing A;\nclass C {}\n"

                let r9InertRegionEmptyIfOut = stable r9InertRegionEmptyIfSrc Settings.Default

                expectProven
                    "inert csff-ignore-end proves across both empty #region and empty #if"
                    r9InertRegionEmptyIfSrc
                    r9InertRegionEmptyIfOut

                expectCommentViolation
                    "moving inert csff-ignore-end into #region body is rejected"
                    r9InertRegionSrc
                    "using A;\n#if A\n#endif\n#region R\n// csff-ignore-end\n#endregion\nusing B;\nclass C {}\n"

                let r9NsInSb = StringBuilder()
                let r9NsOutSb = StringBuilder()

                for i = 1 to 10000 do
                    r9NsInSb.AppendLine(
                        sprintf
                            "namespace N%d {\nusing B;\nusing A;\n// csff-ignore-end\nclass C {}\n}"
                            i
                    )
                    |> ignore

                    r9NsOutSb.AppendLine(
                        sprintf
                            "namespace N%d\n{\n    using A;\n    using B;\n\n    // csff-ignore-end\n\n    class C { }\n}"
                            i
                    )
                    |> ignore

                let r9NsChk = SyntaxPreservation.Checker()
                let swR9Ns = Stopwatch.StartNew()

                Expect.equal
                    (r9NsChk.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        r9NsInSb.ToString(),
                        r9NsOutSb.ToString()
                    ))
                    SyntaxPreservation.Verification.Proven
                    "10k namespaces with inert csff-ignore-end prove in linear time"

                swR9Ns.Stop()

                Expect.isLessThan
                    swR9Ns.ElapsedMilliseconds
                    1500L
                    $"10k namespaces with inert csff-ignore-end must verify fast (took {swR9Ns.ElapsedMilliseconds}ms)."

                let r9DeepInSb = StringBuilder()
                let r9DeepOutSb = StringBuilder()
                r9DeepInSb.AppendLine("using U00000;") |> ignore
                r9DeepOutSb.AppendLine("using U00000;") |> ignore

                for _ = 1 to 10000 do
                    r9DeepInSb.AppendLine("#if true") |> ignore
                    r9DeepOutSb.AppendLine("#if true") |> ignore

                for i = 30000 downto 1 do
                    r9DeepInSb.AppendLine(sprintf "// c%05d\nusing V%05d;" i i) |> ignore

                for i = 1 to 30000 do
                    r9DeepOutSb.AppendLine(sprintf "// c%05d\nusing V%05d;" i i) |> ignore

                for _ = 1 to 10000 do
                    r9DeepInSb.AppendLine("#endif") |> ignore
                    r9DeepOutSb.AppendLine("#endif") |> ignore

                r9DeepInSb.AppendLine("class C {}") |> ignore
                r9DeepOutSb.AppendLine("class C { }") |> ignore
                let r9DeepChk = SyntaxPreservation.Checker()
                let swR9Deep = Stopwatch.StartNew()

                Expect.equal
                    (r9DeepChk.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        r9DeepInSb.ToString(),
                        r9DeepOutSb.ToString()
                    ))
                    SyntaxPreservation.Verification.Proven
                    "30k commented usings under 10k nested #if true frames prove cleanly"

                swR9Deep.Stop()

                Expect.isLessThan
                    swR9Deep.ElapsedMilliseconds
                    1500L
                    $"30k commented usings under 10k nested #if true frames must verify fast (took {swR9Deep.ElapsedMilliseconds}ms)."

                let r10EmptyIfSrc =
                    "#if true\n// note\n#endif\nusing Z;\n#if true\n#endif\nusing A;\nclass C {}\n"

                let r10EmptyIfOut = stable r10EmptyIfSrc Settings.Default

                expectProven
                    "paired closed #if block proves cleanly when another empty #if shifts frame index"
                    r10EmptyIfSrc
                    r10EmptyIfOut

                expectProven
                    "paired closed #if explicit sorted output proves cleanly"
                    r10EmptyIfSrc
                    "#if true\n#endif\nusing A;\n#if true\n// note\n#endif\nusing Z;\nclass C { }\n"

                let r10NestedIfSrc =
                    "#if OUTER\n#if true\n// note\n#endif\nusing Z;\n#if true\n#endif\nusing A;\n#endif\nclass C {}\n"

                expectProven
                    "nested paired closed #if block proves cleanly across empty #if reorder"
                    r10NestedIfSrc
                    (stable r10NestedIfSrc Settings.Default)

                let r10MixedIfSrc =
                    "using Z;\n// outer\n#if F\n// inner\n#endif\nusing B;\n#if F\n#endif\nusing A;\nclass C {}\n"

                expectProven
                    "clause-owned outer comment and closed #if inner comment both prove across empty #if reorder"
                    r10MixedIfSrc
                    (stable r10MixedIfSrc Settings.Default)

                expectProven
                    "merged doc lines inside traveling closed #if block prove cleanly"
                    "#if true\n/// a\n\n/// b\n#endif\nusing Z;\n#if true\n#endif\nusing A;\nclass C {}\n"
                    "#if true\n#endif\nusing A;\n#if true\n/// a\n/// b\n#endif\nusing Z;\nclass C { }\n"

                expectCommentViolation
                    "moving comment between #if and #else arms inside paired slot is rejected"
                    "#if true\n// arm1\n#else\n// arm2\n#endif\nusing Z;\nusing A;\nclass C {}\n"
                    "using A;\n#if true\n#else\n// arm1\n// arm2\n#endif\nusing Z;\nclass C {}\n"

                expectCommentViolation
                    "moving comment out of closed #if onto same clause head is rejected"
                    "#if true\n// note\n#endif\nusing Z;\n#if true\n#endif\nusing A;\nclass C {}\n"
                    "#if true\n#endif\nusing A;\n#if true\n#endif\n// note\nusing Z;\nclass C {}\n"

                let r10RegionSrc =
                    "#if F\nusing Z;\n#endif\n#region R\n/// note\nusing A;\n#endregion\nclass C {}\n"

                expectProven
                    "doc comment on active using crossing #region past inactive conditional using proves cleanly"
                    r10RegionSrc
                    (stable r10RegionSrc Settings.Default)

                let r10RegionDeclDocSrc =
                    "#if F\nusing Z;\n#endif\n#region R\n/// note\nusing A;\n#endregion\n/// decl\nclass C {}\n"

                expectProven
                    "doc comment on active using crossing #region with separate decl doc after #endregion proves cleanly"
                    r10RegionDeclDocSrc
                    (stable r10RegionDeclDocSrc Settings.Default)

                let r10RegionClassInsideSrc =
                    "#if F\nusing Z;\n#endif\n#region R\n/// note\nusing A;\nclass C {}\n#endregion\n"

                expectProven
                    "doc comment on active using crossing #region when class declaration is inside #region proves cleanly"
                    r10RegionClassInsideSrc
                    (stable r10RegionClassInsideSrc Settings.Default)

                expectCommentViolation
                    "doc comment left inside #region merging with declaration doc in same #region is rejected"
                    "#if F\nusing Z;\n#endif\n#region R\n/// note\nusing A;\n/// decl\n#endregion\nclass C {}\n"
                    "using A;\n#if F\nusing Z;\n#endif\n#region R\n/// note\n/// decl\n#endregion\nclass C { }\n"

                expectCommentViolation
                    "dropping doc comment on active using past inactive conditional using without #region is rejected"
                    "#if F\nusing Z;\n#endif\n/// note\nusing A;\nclass C {}\n"
                    "using A;\n#if F\nusing Z;\n#endif\n/// note\nclass C { }\n"

                let r10BudgetFooterSb = StringBuilder(17_000_000)

                for k = 2 to 2350 do
                    r10BudgetFooterSb.Append("// sep\n") |> ignore

                    for _ = 1 to k do
                        r10BudgetFooterSb.Append("/// x\n") |> ignore

                r10BudgetFooterSb.Append("class C {}\n") |> ignore
                let r10BudgetTail = r10BudgetFooterSb.ToString()
                let r10BudgetIn = "using B;\nusing A;\n" + r10BudgetTail
                let r10BudgetOut = "using A;\nusing B;\n" + r10BudgetTail
                let r10BudgetChk = SyntaxPreservation.Checker()

                Expect.equal
                    (r10BudgetChk.AdjudicateDecision(
                        PrinterOptions.Default,
                        "Review.cs",
                        r10BudgetIn,
                        r10BudgetOut
                    ))
                    SyntaxPreservation.Verification.Proven
                    "2..2350 doc blocks with >2^31 total slice cost must respect int64 budget without wrapping"
            }
        ]
