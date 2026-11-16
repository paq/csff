module Csff.Tests.AnonymousMethodTests

open System
open Csff.Cli
open Csff.Conformance
open Csff.Printer
open Expecto
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

let private fixtures =
    [
        "anonymous object argument with a multiline literal",
        "class C\n{\n    void M()\n    {\n        Call(new { Text = @\"line one\nline two\" });\n    }\n}\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            new\n            {\n                Text = @\"line one\nline two\",\n            }\n        );\n    }\n}\n"
        ]
        "anonymous object argument drops the gap before its first member comment",
        "class C\n{\n    void M()\n    {\n        Call(new {\n\n            // first member\n            A = 1, B = 2 });\n    }\n}\n",
        [
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            new\n            {\n                // first member\n                A = 1,\n                B = 2,\n            }\n        );\n    }\n}\n"
        ]
        "empty",
        "class C { void M() { Call(delegate { }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            { }\n        );\n    }\n}\n"
            [ 40; 100 ], "class C\n{\n    void M()\n    {\n        Call(delegate { });\n    }\n}\n"
        ]
        "body",
        "class C { void M() { Call(delegate {  F( 1,  2 );  G( ); }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                F(\n                    1,\n                    2\n                );\n                G();\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                F(1, 2);\n                G();\n            }\n        );\n    }\n}\n"
        ]
        "empty parameters",
        "class C { void M() { Call(delegate () { }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate()\n            { }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(delegate() { });\n    }\n}\n"
        ]
        "parameters",
        "class C { void M() { Call(delegate (int x) {  F( x ); }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate(\n                int x\n            )\n            {\n                F(\n                    x\n                );\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate(int x)\n            {\n                F(x);\n            }\n        );\n    }\n}\n"
        ]
        "async",
        "class C { void M() { Call(async delegate () { await  F( ); }); } }\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            async delegate()\n            {\n                await F();\n            }\n        );\n    }\n}\n"
        ]
        "static",
        "class C { void M() { Call(static delegate (int x) {  F( x ); }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            static delegate(\n                int x\n            )\n            {\n                F(\n                    x\n                );\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            static delegate(int x)\n            {\n                F(x);\n            }\n        );\n    }\n}\n"
        ]
        "async static",
        "class C { void M() { Call(async static delegate { await F(); }); } }\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            async static delegate\n            {\n                await F();\n            }\n        );\n    }\n}\n"
        ]
        "static async",
        "class C { void M() { Call(static async delegate () { await F(); }); } }\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            static async delegate()\n            {\n                await F();\n            }\n        );\n    }\n}\n"
        ]
        "nested",
        "class C { void M() { Call(delegate { Call(delegate(int x) { F( x ); }); }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                Call(\n                    delegate(\n                        int x\n                    )\n                    {\n                        F(\n                            x\n                        );\n                    }\n                );\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                Call(\n                    delegate(int x)\n                    {\n                        F(x);\n                    }\n                );\n            }\n        );\n    }\n}\n"
        ]
        "last",
        "class C { void M() { Call(first, delegate() { F( ); }); } }\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            first,\n            delegate()\n            {\n                F();\n            }\n        );\n    }\n}\n"
        ]
        "middle",
        "class C { void M() { Call(first, delegate() { F( ); }, last); } }\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            first,\n            delegate()\n            {\n                F();\n            },\n            last\n        );\n    }\n}\n"
        ]
        "comments",
        "class C { void M() { Call(delegate () // header\n{ // opening\n\n\n// body\nF( 1, 2 ); /* tail */\n}); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate() // header\n            { // opening\n                // body\n                F(\n                    1,\n                    2\n                ); /* tail */\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate() // header\n            { // opening\n                // body\n                F(1, 2); /* tail */\n            }\n        );\n    }\n}\n"
        ]
        "directives",
        "class C { void M() { Call(delegate {\n#if A\nF( 1,  2);\n#else\nG( 3,  4);\n#endif\n}); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n#if A\n                F(\n                    1,\n                    2\n                );\n#else\n                G(\n                    3,\n                    4\n                );\n#endif\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n#if A\n                F(1, 2);\n#else\n                G(3, 4);\n#endif\n            }\n        );\n    }\n}\n"
        ]
        "lambda line",
        "class C { void M() { Task.Run(() => // comment\n{\n\n\nF( 1, 2 );\n}); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Task.Run(\n            () => // comment\n            {\n                F(\n                    1,\n                    2\n                );\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Task.Run(() => // comment\n        {\n            F(1, 2);\n        });\n    }\n}\n"
        ]
        "lambda empty",
        "class C { void M() { Task.Run(() => // comment\n{ }); } }\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Task.Run(\n            () => // comment\n            { }\n        );\n    }\n}\n"
        ]
        "lambda block",
        "class C { void M() { Task.Run(() => /* comment */ { F( 1, 2 ); }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Task.Run(\n            () => /* comment */\n            {\n                F(\n                    1,\n                    2\n                );\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Task.Run(() => /* comment */\n        {\n            F(1, 2);\n        });\n    }\n}\n"
        ]
        "lambda last",
        "class C { void M() { Call(first, () => // comment\n{ F( 1, 2 ); }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            first,\n            () => // comment\n            {\n                F(\n                    1,\n                    2\n                );\n            }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            first,\n            () => // comment\n            {\n                F(1, 2);\n            }\n        );\n    }\n}\n"
        ]
        "lambda middle",
        "class C { void M() { Call(first, () => // comment\n{ F( 1, 2 ); }, last); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            first,\n            () => // comment\n            {\n                F(\n                    1,\n                    2\n                );\n            },\n            last\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            first,\n            () => // comment\n            {\n                F(1, 2);\n            },\n            last\n        );\n    }\n}\n"
        ]
        "empty typed parameters",
        "class C { void M() { Call(delegate (int x) { }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate(\n                int x\n            ) { }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(delegate(int x) { });\n    }\n}\n"
        ]
        "empty async",
        "class C { void M() { Call(async delegate { }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            async delegate\n            { }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(async delegate { });\n    }\n}\n"
        ]
        "empty static",
        "class C { void M() { Call(static delegate () { }); } }\n",
        [
            [ 20 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            static delegate()\n            { }\n        );\n    }\n}\n"
            [ 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(static delegate() { });\n    }\n}\n"
        ]
        "long parameters",
        "class C { void M() { Call(delegate (int firstParameter, string secondParameter) { F( firstParameter,secondParameter ); }); } }\n",
        [
            [ 20; 40 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate(\n                int firstParameter,\n                string secondParameter\n            )\n            {\n                F(\n                    firstParameter,\n                    secondParameter\n                );\n            }\n        );\n    }\n}\n"
            [ 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate(int firstParameter, string secondParameter)\n            {\n                F(firstParameter, secondParameter);\n            }\n        );\n    }\n}\n"
        ]
        "object argument",
        "class C { void M() { Call(delegate { logger.Write(\"Greeting\", new { msg = \"Hello, world!\" }); }); } }\n",
        [
            [ 20; 40 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                logger.Write(\n                    \"Greeting\",\n                    new\n                    {\n                        msg = \"Hello, world!\",\n                    }\n                );\n            }\n        );\n    }\n}\n"
            [ 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                logger.Write(\"Greeting\", new { msg = \"Hello, world!\" });\n            }\n        );\n    }\n}\n"
        ]
        "object argument comments",
        "class C { void M() { Call(delegate { F(new { /* lead */ Value = 1 /* tail */ }); }); } }\n",
        [
            [ 20; 40; 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                F(\n                    new\n                    { /* lead */\n                        Value = 1, /* tail */\n                    }\n                );\n            }\n        );\n    }\n}\n"
        ]
        "object argument multiple",
        "class C { void M() { Call(delegate { F(new { First = 1, Second = 2, }); }); } }\n",
        [
            [ 20; 40 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                F(\n                    new\n                    {\n                        First = 1,\n                        Second = 2,\n                    }\n                );\n            }\n        );\n    }\n}\n"
            [ 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                F(new { First = 1, Second = 2 });\n            }\n        );\n    }\n}\n"
        ]
        "object argument nested",
        "class C { void M() { Call(delegate { F(new { Inner = new { Value = 1 } }); }); } }\n",
        [
            [ 20; 40 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                F(\n                    new\n                    {\n                        Inner = new\n                        {\n                            Value = 1,\n                        },\n                    }\n                );\n            }\n        );\n    }\n}\n"
            [ 100 ],
            "class C\n{\n    void M()\n    {\n        Call(\n            delegate\n            {\n                F(new { Inner = new { Value = 1 } });\n            }\n        );\n    }\n}\n"
        ]
        "delegate argument with uneven spacing and blank lines",
        "class C\n{\n    void M()\n    {\n        tests.Add(new   SubTest(\"Write/Basic/String\",\n            delegate ()\n          {\n\n\n                logger.Write(\"Greeting\",   new { msg = \"Hello, world!\" });\n            }));\n    }\n}\n",
        [
            [ 20; 40 ],
            "class C\n{\n    void M()\n    {\n        tests.Add(\n            new SubTest(\n                \"Write/Basic/String\",\n                delegate()\n                {\n                    logger.Write(\n                        \"Greeting\",\n                        new\n                        {\n                            msg = \"Hello, world!\",\n                        }\n                    );\n                }\n            )\n        );\n    }\n}\n"
            [ 100 ],
            "class C\n{\n    void M()\n    {\n        tests.Add(\n            new SubTest(\n                \"Write/Basic/String\",\n                delegate()\n                {\n                    logger.Write(\"Greeting\", new { msg = \"Hello, world!\" });\n                }\n            )\n        );\n    }\n}\n"
        ]
    ]

let tests =
    testList
        "anonymous method"
        [
            for name, source, outputs in fixtures do
                for widths, expected in outputs do
                    for width in widths do
                        for endOfLine in [ EndOfLine.Lf; EndOfLine.CrLf ] do
                            testCase $"{name} / width {width} / {endOfLine}" (fun () ->
                                let newline = if endOfLine = EndOfLine.CrLf then "\r\n" else "\n"
                                let source = source.Replace("\n", newline)
                                let expected = expected.Replace("\n", newline)

                                let options =
                                    { PrinterOptions.Default with
                                        Width = width
                                        EndOfLine = endOfLine
                                    }

                                let settings =
                                    { Settings.Default with
                                        AutoEndOfLine = false
                                        Printer = options
                                    }

                                use worker = new Worker()
                                worker.Print(source, settings)
                                let actual = worker.OutputText
                                Expect.equal actual expected "Layout matches CSharpier 1.3.0."
                                worker.Print(actual, settings)

                                Expect.equal
                                    worker.OutputText
                                    actual
                                    "The output is idempotent."

                                TokenPreservation
                                    .Checker()
                                    .Check(options, "anonymous.cs", source, actual)
                                |> function
                                    | Ok() -> ()
                                    | Error error -> failtest error

                                for symbols in [ []; [ "A" ] ] do
                                    let parseOptions =
                                        CSharpParseOptions.Default.WithPreprocessorSymbols(symbols)

                                    let errors =
                                        CSharpSyntaxTree
                                            .ParseText(actual, parseOptions)
                                            .GetDiagnostics()
                                        |> Seq.filter (fun diagnostic ->
                                            diagnostic.Severity = DiagnosticSeverity.Error)
                                        |> Seq.toList

                                    Expect.isEmpty
                                        errors
                                        "Each conditional branch remains valid C#.")
        ]
