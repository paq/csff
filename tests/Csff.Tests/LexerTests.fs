module Csff.Tests.LexerTests

open System
open System.Diagnostics
open Csff.Conformance
open Csff.Lexer
open Expecto
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

let private lex source =
    let buffer = TokenBuffer()
    Lexer.lex source buffer
    buffer

let steadyStateAllocation (batches: int) (iterations: int) (action: unit -> unit) =
    let mutable least = Int64.MaxValue

    for _ in 1 .. max 1 batches do
        let before = GC.GetAllocatedBytesForCurrentThread()
        let mutable iteration = 0

        while iteration < iterations do
            action ()
            iteration <- iteration + 1

        least <- min least (GC.GetAllocatedBytesForCurrentThread() - before)

    least

let private allocatedWhileLexing source buffer =
    steadyStateAllocation 3 100 (fun () -> Lexer.lex source buffer)

let private lexingMilliseconds iterations source buffer =
    let start = Stopwatch.GetTimestamp()
    let mutable iteration = 0

    while iteration < iterations do
        Lexer.lex source buffer
        iteration <- iteration + 1

    Stopwatch.GetElapsedTime(start).TotalMilliseconds

let private expectLinearPrefixScaling label makeSource =
    let small = makeSource 4096
    let large = makeSource (4096 * 8)
    let buffer = lex large
    lexingMilliseconds 32 small buffer |> ignore
    let mutable iterations = 1

    while lexingMilliseconds iterations small buffer < 20.0 do
        iterations <- iterations * 2

    let samples =
        Array.init 5 (fun index ->
            if index % 2 = 0 then
                let smallTime = lexingMilliseconds iterations small buffer
                smallTime, lexingMilliseconds iterations large buffer
            else
                let largeTime = lexingMilliseconds iterations large buffer
                lexingMilliseconds iterations small buffer, largeTime)

    let median values = (Array.sort values)[values.Length / 2]
    let smallTime = samples |> Array.map fst |> median
    let largeTime = samples |> Array.map snd |> median

    printfn
        "failed prefix %s: n %.3f ms; 8n %.3f ms; ratio %.2f"
        label
        smallTime
        largeTime
        (largeTime / smallTime)

    Expect.isLessThan
        largeTime
        (smallTime * 32.0)
        "Eight times the input permits four times the linear cost, not quadratic rescanning."

    Expect.equal
        (allocatedWhileLexing large buffer)
        0L
        "The failure boundary adds no steady-state allocation."

let private expectLossless source (buffer: TokenBuffer) =
    RoundTrip.checkBuffer "fixture.cs" source buffer
    |> fun result -> Expect.equal result (Ok()) "Every character must round-trip."

    let mutable offset = 0

    let checkSpan start length =
        Expect.equal start offset "Spans partition the source without gaps or overlap."
        offset <- offset + length

    for index in 0 .. buffer.TokenCount - 1 do
        let token = buffer.Token index

        for index in token.TriviaStart .. token.TriviaStart + token.LeadingCount - 1 do
            let trivia = buffer.Trivia index
            checkSpan trivia.Start trivia.Length

        checkSpan token.Start token.Length

        for index in
            token.TriviaStart + token.LeadingCount .. token.TriviaStart
                                                      + token.LeadingCount
                                                      + token.TrailingCount
                                                      - 1 do
            let trivia = buffer.Trivia index
            checkSpan trivia.Start trivia.Length

    Expect.equal offset source.Length "The partition reaches EOF."
    let eof = buffer.Token(buffer.TokenCount - 1)
    Expect.equal eof.Kind TokenKind.EndOfFileToken "EOF is always present."
    Expect.equal eof.Length 0 "EOF owns no text."

let private expectTokens source expected =
    let buffer = lex source
    expectLossless source buffer
    Expect.equal buffer.TokenCount (List.length expected + 1) "Include exactly one EOF."

    expected
    |> List.iteri (fun index (kind, text: string) ->
        let token = buffer.Token index
        Expect.equal token.Kind kind "Token kind."
        let mutable span = source.AsSpan(token.Start, token.Length)
        Expect.equal (span.ToString()) text "Token boundaries.")

let private expectLexicalOracle source =
    let buffer = lex source
    expectLossless source buffer

    let options =
        CSharpParseOptions(LanguageVersion.Preview, DocumentationMode.Diagnose)

    let tokens = SyntaxFactory.ParseTokens(source, options = options) |> Seq.toArray
    Expect.equal buffer.TokenCount tokens.Length "Roslyn lexical token count."

    for index in 0 .. tokens.Length - 1 do
        let expected = tokens[index]
        let actual = buffer.Token index
        Expect.equal (int actual.Kind) expected.RawKind "Roslyn lexical kind."
        Expect.equal actual.Start expected.SpanStart "Roslyn token start."
        Expect.equal actual.Length expected.Span.Length "Roslyn token length."
        Expect.equal actual.LeadingCount expected.LeadingTrivia.Count "Leading trivia count."
        Expect.equal actual.TrailingCount expected.TrailingTrivia.Count "Trailing trivia count."

        let trivia =
            Seq.append expected.LeadingTrivia expected.TrailingTrivia |> Seq.toArray

        for index in 0 .. trivia.Length - 1 do
            let actualTrivia = buffer.Trivia(actual.TriviaStart + index)
            Expect.equal (int actualTrivia.Kind) trivia[index].RawKind "Roslyn trivia kind."
            Expect.equal actualTrivia.Start trivia[index].FullSpan.Start "Roslyn trivia start."
            Expect.equal actualTrivia.Length trivia[index].FullSpan.Length "Roslyn trivia length."

let private expectString kind source =
    expectTokens source [ kind, source ]
    expectLexicalOracle (" /* lead */ " + source + "; // tail\r\nnext")

let tests =
    testList
        "lexer"
        [
            test "merge conflict markers and alternate branches match Roslyn trivia" {
                for ending in [ "\n"; "\r\n"; "\r"; "\u2028" ] do
                    for source in
                        [
                            "<<<<<<< HEAD\nint a;\n=======\nint b;\n>>>>>>> B\n"
                            "<<<<<<< HEAD\nint a;\n||||||| BASE\nint old;\n=======\nint b;\n>>>>>>> B\n"
                            "=======\n\nint b;\n>>>>>>> B\nclass C{}"
                            "||||||| BASE\nint old;\n=======\nint b;\n"
                            "  <<<<<<< HEAD\nint a;\n=======\nint b;\n>>>>>>> B\n"
                            "<<<<<<<x\nint a;\n========\nint b;\n>>>>>>>> B\n"
                            ">>>>>>> orphan\nclass C{}\n"
                        ] do
                        let source = source.Replace("\n", ending)
                        let buffer = lex source
                        expectLossless source buffer

                        Expect.equal
                            (RoslynOracle.checkBuffer "conflict.cs" source buffer)
                            (Ok())
                            "Marker headers, combined line endings, and inactive sides have exact boundaries."
            }
            test "seven closing brackets remain ordinary tokens outside a conflict branch" {
                let source = "class G<T>{}\nclass C{\nG<G<G<G<G<G<G<int\n>>>>>>> field;\n}\n"
                let buffer = lex source
                expectLossless source buffer

                Expect.equal
                    (RoslynOracle.checkBuffer "generic.cs" source buffer)
                    (Ok())
                    "Type closers remain ordinary tokens, matching the parsed oracle."
            }
            test "bounded conflict lexing matches a standalone substring" {
                for prefix in [ "x"; "outside text\n" ] do
                    let text = "<<<<<<< HEAD\nclass A{}\n=======\nclass B{}\n>>>>>>> other\n"
                    let source = prefix + text + "outside suffix"
                    let buffer = TokenBuffer()
                    Lexer.lexRange source prefix.Length (prefix.Length + text.Length) buffer
                    let expected = lex text
                    Expect.equal buffer.TokenCount expected.TokenCount "Range token count."
                    Expect.equal buffer.TriviaCount expected.TriviaCount "Range trivia count."

                    for i = 0 to buffer.TokenCount - 1 do
                        let actual = buffer.Token i
                        let token = expected.Token i
                        Expect.equal actual.Kind token.Kind "Range token kind."
                        Expect.equal (actual.Start - prefix.Length) token.Start "Range token start."
                        Expect.equal actual.Length token.Length "Range token length."
                        Expect.equal actual.LeadingCount token.LeadingCount "Range leading trivia."

                        Expect.equal
                            actual.TrailingCount
                            token.TrailingCount
                            "Range trailing trivia."

                    for i = 0 to buffer.TriviaCount - 1 do
                        let actual = buffer.Trivia i
                        let trivia = expected.Trivia i
                        Expect.equal actual.Kind trivia.Kind "Range trivia kind."

                        Expect.equal
                            (actual.Start - prefix.Length)
                            trivia.Start
                            "Range trivia start."

                        Expect.equal actual.Length trivia.Length "Range trivia length."
            }
            test "interpolation ranges preserve bounded tokens and trivia at every truncation" {
                let prefix = "outside {"
                let start = prefix.Length - 1
                let actual = TokenBuffer()
                let expected = TokenBuffer()

                for expression, delimiter in
                    [
                        "x /* } : */ ", "}"
                        "\n /* lead */ F(x) // }\n ", "}"
                        "F(\"}:\", @\"a\"\"}:\", '\\'')", "}"
                        "F(\"\"\"}:\"\"\", $\"nested {x:X}\")", "}"
                        "new C { P = F(a[0], (x ? y : z)) }", "}"
                        "global::N.F(), -10 /* align */ ", ":"
                        "(global::N.F()), -10 /* align */ ", ":"
                        "x\n/** doc */ ", ":"
                        "/*c*//**d*/x", "}"
                        " /*c*/ /**d*/ x", ":"
                        "/*c*/ ///d\nx", "}"
                    ] do
                    let source = prefix + expression + delimiter + " /* tail \" {x}"

                    for finish in prefix.Length .. source.Length do
                        Lexer.lex (source.Substring(prefix.Length, finish - prefix.Length)) expected
                        let mutable boundary = finish
                        let mutable expectedFormat = false
                        let mutable parens, brackets, braces = 0, 0, 0
                        let mutable index = 0
                        let mutable found = false

                        while index < expected.TokenCount && not found do
                            let token = expected.Token index

                            if
                                parens = 0
                                && brackets = 0
                                && braces = 0
                                && (token.Kind = TokenKind.CloseBraceToken
                                    || token.Kind = TokenKind.ColonToken
                                    || token.Kind = TokenKind.ColonColonToken)
                            then
                                boundary <- prefix.Length + token.Start
                                expectedFormat <- token.Kind <> TokenKind.CloseBraceToken
                                found <- true
                            else
                                match token.Kind with
                                | TokenKind.OpenParenToken -> parens <- parens + 1
                                | TokenKind.CloseParenToken -> parens <- max 0 (parens - 1)
                                | TokenKind.OpenBracketToken -> brackets <- brackets + 1
                                | TokenKind.CloseBracketToken -> brackets <- max 0 (brackets - 1)
                                | TokenKind.OpenBraceToken -> braces <- braces + 1
                                | TokenKind.CloseBraceToken -> braces <- max 0 (braces - 1)
                                | _ -> ()

                                index <- index + 1

                        let struct (stop, format) =
                            Lexer.lexInterpolation source start finish actual

                        Expect.equal
                            stop
                            boundary
                            $"Stop at the hole boundary: {expression}, {finish}."

                        Expect.equal
                            format
                            expectedFormat
                            "The first top-level colon starts format text, even in ::."

                        let boundedEnd = min finish (boundary + 1)
                        Lexer.lex (source.Substring(start, boundedEnd - start)) expected

                        Expect.equal actual.TokenCount expected.TokenCount "Same bounded tokens."
                        Expect.equal actual.TriviaCount expected.TriviaCount "Same bounded trivia."

                        for index in 0 .. expected.TokenCount - 1 do
                            let token = expected.Token index

                            Expect.equal
                                (actual.Token index)
                                { token with
                                    Start = start + token.Start
                                }
                                "Tokens retain absolute offsets and trivia ownership."

                        for index in 0 .. expected.TriviaCount - 1 do
                            let trivia = expected.Trivia index

                            Expect.equal
                                (actual.Trivia index)
                                { trivia with
                                    Start = start + trivia.Start
                                }
                                "Trivia retains absolute offsets."
            }
            test "flat interpolation ranges consume only each hole and allocate no text" {
                let buffer = TokenBuffer()

                for width in [ 1; 2; 3 ] do
                    let opening = String('{', width)
                    let closing = String('}', width)

                    for count in [ 128; 256; 512; 1024 ] do
                        let source = String.concat "" (Array.create count (opening + "x" + closing))
                        let stride = width * 2 + 1

                        let consume () =
                            let mutable consumed = 0
                            let mutable tokens = 0

                            for index in 0 .. count - 1 do
                                let start = index * stride + width - 1

                                let struct (boundary, _) =
                                    Lexer.lexInterpolation source start source.Length buffer

                                consumed <- consumed + boundary + 1 - start
                                tokens <- tokens + buffer.TokenCount

                            struct (consumed, tokens)

                        let struct (consumed, tokens) = consume ()
                        let allocated = steadyStateAllocation 3 1 (fun () -> consume () |> ignore)
                        Expect.equal consumed (3 * count) "Each call consumes one {x} range."
                        Expect.equal tokens (4 * count) "Each hole emits three tokens and EOF."
                        Expect.equal allocated 0L "Neither suffixes nor bounded holes are copied."
            }
            test "directive booleans precede symbol lookup regardless of case" {
                for prefix, expression, name in
                    [ "", "TRUE", "A"; "", "True", "A"; "#define FALSE\n", "FALSE", "B" ] do
                    let source =
                        prefix + $"#if {expression}\nclass A {{}}\n#else\nclass B {{}}\n#endif"

                    expectLexicalOracle source
                    let buffer = lex source
                    let identifier = buffer.Token 1

                    Expect.equal
                        (source.Substring(identifier.Start, identifier.Length))
                        name
                        "Roslyn's active class survives."
            }
            test "raw interpolation format text can cross a newline" {
                let source = "var s = $\"\"\"{42:\n000}\"\"\"; int n = 1;"
                expectLexicalOracle source
                let buffer = lex source
                let literal = buffer.Token 3
                Expect.equal literal.Kind TokenKind.InterpolatedStringToken "One complete literal."
                Expect.equal (literal.Start, literal.Length) (8, 16) "Roslyn's literal span."

                Csff.Conformance.NodeOracle.check "regression.cs" source (Csff.Parser.SyntaxTree())
                |> fun result ->
                    Expect.equal result (Ok()) "Raw format text also parses faithfully."
            }
            test "empty and trivia-only sources retain EOF" {
                for source in [ ""; " \t\r\n\n // tail"; "/* unfinished"; "// no newline" ] do
                    expectLexicalOracle source
            }
            test "trailing trivia stops after the first EOL" {
                let source = " \t/* lead */x /* tail */ // hi\r\n\n  // lead\n y \n // eof"
                expectLexicalOracle source
                let buffer = lex source
                let first = buffer.Token 0
                Expect.equal first.LeadingCount 2 "Whitespace and the leading comment."
                Expect.equal first.TrailingCount 5 "The CRLF belongs to x."

                let lastTrailing =
                    buffer.Trivia(first.TriviaStart + first.LeadingCount + first.TrailingCount - 1)

                Expect.equal
                    lastTrailing.Kind
                    TriviaKind.EndOfLineTrivia
                    "Trailing trivia ends at EOL."

                Expect.equal lastTrailing.Length 2 "CRLF is indivisible."
                let next = buffer.Token 1

                Expect.equal
                    (buffer.Trivia next.TriviaStart).Kind
                    TriviaKind.EndOfLineTrivia
                    "The blank line leads y."
            }
            test "multiline comments remain indivisible in trailing trivia" {
                expectLexicalOracle "x /* a\r\nb */ y\n z/**/"
            }
            test "Unicode whitespace and line separators agree with Roslyn" {
                expectLexicalOracle "\ufeff\u001a\t\v\f\u00a0x\u0085\u2000y\u2028z\u2029"
            }
            test "documentation lines share a full span including their final newline" {
                let source = "  /// a\n    /// b\r\n  x"
                expectLexicalOracle source
                let buffer = lex source
                let trivia = buffer.Trivia 1

                Expect.equal
                    trivia.Kind
                    TriviaKind.SingleLineDocumentationCommentTrivia
                    "Structured documentation."

                Expect.equal trivia.Start 2 "First-line indentation is separate."

                Expect.equal
                    trivia.Length
                    17
                    "Subsequent indentation and the final CRLF are owned by documentation."

                Expect.equal
                    (buffer.Trivia 2).Kind
                    TriviaKind.WhitespaceTrivia
                    "Following indentation is separate."
            }
            test "documentation breaks on blank lines and ordinary comments" {
                for source in
                    [
                        "///"
                        "/// a\n\t/// b\n  "
                        "/// a\n \n/// b\nx"
                        "//// ordinary\n/// doc\n//// ordinary\nx"
                        "/// a\n\v/// b\u0085\ufeff/// c\u2028x"
                        "/// <a x=\"\n/// v\">\nx"
                        "/** a */ x /***/ y /****/ z /**/"
                        "/**"
                        "/***"
                    ] do
                    expectLexicalOracle source
            }
            test "documentation after a token leads the next token even without an EOL" {
                for source in
                    [ "x /// a\n  /// b\n y"; "x/**a*/y"; "x /** a\nb */ y\nx"; "x /// eof" ] do
                    expectLexicalOracle source
                    let buffer = lex source
                    let next = buffer.Token 1
                    Expect.isGreaterThan next.LeadingCount 0 "Documentation is leading trivia."
                    let previous = buffer.Token 0

                    for index in
                        previous.TriviaStart .. previous.TriviaStart + previous.TrailingCount - 1 do
                        let kind = (buffer.Trivia index).Kind

                        Expect.isFalse
                            (kind = TriviaKind.SingleLineDocumentationCommentTrivia
                             || kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                            "Documentation never trails a token."
            }
            test "directives own their full line and retain individual kinds" {
                let source =
                    "  #define X\r\n#undef X\n#if true\n#elif false\n#else\n#endif\n#region A\n#endregion\n#pragma warning disable CS1\n#pragma checksum \"f\" \"g\" \"h\"\n#nullable enable\n#line 10 \"f\"\n#line (1,2)-(3,4) 5 \"f\"\n#warning hi\n#error hi\n"

                expectLexicalOracle source
                let buffer = lex source

                let kinds =
                    [
                        for index in 0 .. buffer.TriviaCount - 1 do
                            let kind = (buffer.Trivia index).Kind

                            if kind <> TriviaKind.WhitespaceTrivia then
                                yield kind
                    ]

                Expect.equal
                    kinds
                    [
                        TriviaKind.DefineDirectiveTrivia
                        TriviaKind.UndefDirectiveTrivia
                        TriviaKind.IfDirectiveTrivia
                        TriviaKind.ElifDirectiveTrivia
                        TriviaKind.ElseDirectiveTrivia
                        TriviaKind.EndIfDirectiveTrivia
                        TriviaKind.RegionDirectiveTrivia
                        TriviaKind.EndRegionDirectiveTrivia
                        TriviaKind.PragmaWarningDirectiveTrivia
                        TriviaKind.PragmaChecksumDirectiveTrivia
                        TriviaKind.NullableDirectiveTrivia
                        TriviaKind.LineDirectiveTrivia
                        TriviaKind.LineSpanDirectiveTrivia
                        TriviaKind.WarningDirectiveTrivia
                        TriviaKind.ErrorDirectiveTrivia
                    ]
                    "Every directive has its own Roslyn kind."

                Expect.equal (buffer.Trivia 1).Start 2 "Directive indentation is separate."
                Expect.equal (buffer.Trivia 1).Length 11 "Directive includes CRLF."
            }
            test "conditional expressions use Roslyn precedence and initially undefined symbols" {
                for expression, value in
                    [
                        "true", true
                        "false", false
                        "DEBUG", false
                        "!DEBUG", true
                        "true || false && false", true
                        "(true || false) && false", false
                        "false == false != false", true
                        "true != !false", false
                        "!(true && (false || true))", false
                        "MISSING == false", true
                        "1", false
                        "(true", true
                        "!", true
                        "true junk", true
                        "/**/true", false
                    ] do
                    let source = $"#if {expression}\nlive\n#else\ndead\n#endif\n"
                    expectLexicalOracle source
                    let buffer = lex source
                    let token = buffer.Token 0

                    Expect.equal
                        (source.Substring(token.Start, token.Length))
                        (if value then "live" else "dead")
                        "Selected branch."
            }
            test "disabled text is opaque and separates directive indentation" {
                for source in
                    [
                        "#if false\n  dead\n  #else\n live\n  #endif\nx"
                        "#if false\n// comment\n\n  #endif\n"
                        "#if false\n/*\n#endif\nx"
                        "#if false\n\"unfinished\n/// doc\na #endif\n#if true\nnested\n#else\nother\n#endif\n#else\nlive\n#endif"
                        "#if false\n  \n "
                        "#if false\n #what\nx\n#endif"
                        "#if true\nx\n#elif true\ny\n#else\nz\n#endif\nv"
                    ] do
                    expectLexicalOracle source
            }
            test "define and undef affect only active branches and reset for each source" {
                for source in
                    [
                        "#define X\n#if X && !Y\nx\n#else\ny\n#endif\n"
                        "#define X\n#undef X\n#if X\nx\n#else\ny\n#endif"
                        "#if false\n#define X\n#endif\n#if X\ny\n#endif"
                        "#define \\u0058\n#if X\nx\n#endif"
                        "#define X\n#if \\u0058\nx\n#endif"
                        "#define @X\n#if X\nx\n#endif"
                        "#define class\n#if class\nx\n#endif"
                        "#define if\n#if if\nx\n#endif"
                        "#define a\u200Cb\n#if ab\nx\n#endif"
                        "#define X junk\n#if X\nx\n#endif"
                        "x\n#define X\n#if X\ny\n#endif"
                    ] do
                    expectLexicalOracle source

                let buffer = lex "#define X\n"
                let source = "#if X\ndisabled\n#endif"
                Lexer.lex source buffer
                expectLossless source buffer
                Expect.equal buffer.TokenCount 1 "Defined symbols never leak between files."
            }
            test "malformed directives and region nesting follow Roslyn recovery" {
                for source in
                    [
                        "#"
                        "#what\n#if true junk\nx\n#else\ny\n#endif\n"
                        "x #if false\ny\n#endif\nz"
                        "x /*\n*/ #if false\ny\n#endif\nz"
                        "/* c */ #if false\nx\n#endif\ny"
                        "x/**a*/ #if false\nx\n#endif\ny"
                        "/*c*/ /**d*/ #if false\nx\n#endif\ny"
                        "/*c*/ ///doc\n#if false\nx\n#endif\ny"
                        "#if true\u0085x\u2028#else\u2029y\r#endif"
                        "#\\u0069f true\nx\n#endif"
                        "# if true\nx\n#endif"
                        "#elif true\nx\n#else\ny\n#endif\nz"
                        "#if true\nx\n#else\ny\n#else\nz\n#endif\na"
                        "#if true\nx\n#else\ny\n#elif true\nz\n#endif\na"
                        "#if true\n#region A\n#else\ny\n#endif\nx"
                        "#region A\n#endif\nx\n#endregion\n"
                        "#if true\nx\n#endregion\ny\n#endif\nz"
                        "#if false\n #region ignored\n// blah\n#warning hi\n #if true\nnested\n #endif\n#endif\nx"
                        "#if true /* comment\nend */\nx\n#endif"
                    ] do
                    expectLexicalOracle source
            }
            test "file based program directives and hashes inside tokens agree with Roslyn" {
                for source in
                    [
                        "#!/usr/bin/env dotnet\n#:include f.cs\nx\n# !foo\ny\n#r \"r\"\n#load \"f\"\n"
                        "x; // #if false\n\"#if false\"; /* #endif */ y"
                    ] do
                    let buffer = lex source
                    expectLossless source buffer

                    Expect.equal
                        (RoslynOracle.checkBuffer "fixture.cs" source buffer)
                        (Ok())
                        "Roslyn full-span oracle."
            }
            test "all reserved keywords and their prefixes" {
                for kind in Enum.GetValues<SyntaxKind>() do
                    if SyntaxFacts.IsReservedKeyword kind then
                        let text = SyntaxFacts.GetText kind
                        expectTokens text [ enum<TokenKind>(int kind), text ]
                        expectTokens (text + "x") [ TokenKind.IdentifierToken, text + "x" ]
                        expectTokens ("@" + text) [ TokenKind.IdentifierToken, "@" + text ]
            }
            test "every contextual keyword stays an identifier" {
                for kind in Enum.GetValues<SyntaxKind>() do
                    if SyntaxFacts.IsContextualKeyword kind then
                        let text = SyntaxFacts.GetText kind
                        expectTokens text [ TokenKind.IdentifierToken, text ]

                expectTokens
                    "var _"
                    [ TokenKind.IdentifierToken, "var"; TokenKind.IdentifierToken, "_" ]
            }
            test "a supplementary-plane letter in an identifier lexes as Roslyn lexes it" {
                for source in
                    [
                        "x\\U0001D49Cy"
                        "\\U0001D49Cx"
                        "x\\U00010000y"
                        "x\\U000101FDy"
                        "x\\U0001F600y"
                        "\\U0001F600x"
                        "x\uD835\uDC9Cy"
                        "\uD835\uDC9Cx"
                        "x\uD800\uDC00y"
                        "x\uD83D\uDE00y"
                    ] do
                    expectLexicalOracle source

                expectTokens "x\\u00E9y" [ TokenKind.IdentifierToken, "x\\u00E9y" ]
                expectTokens "x\u00E9y" [ TokenKind.IdentifierToken, "x\u00E9y" ]
            }
            test "Unicode and escaped identifiers retain their source spelling" {
                expectLexicalOracle
                    "café 日本語 a\u0301 a\u200Cb a١ @class @\\u0061 \\u0069f a\\u200Cb \\U00000061bc"
            }
            test "integer bases, separators, and every suffix spelling" {
                for number in [ "0"; "123_456"; "0xFf"; "0X_F_F"; "0b1010_01"; "0B_1" ] do
                    for suffix in
                        [ ""; "u"; "U"; "l"; "L"; "ul"; "uL"; "Ul"; "UL"; "lu"; "lU"; "Lu"; "LU" ] do
                        expectTokens
                            (number + suffix)
                            [ TokenKind.NumericLiteralToken, number + suffix ]

                        expectLexicalOracle (number + suffix)
            }
            test "real literals, exponents, and all floating suffixes" {
                for number in [ "1"; "1.25"; ".5"; "1e3"; "1E+3"; "1e-3"; "1_2.3_4e5_6" ] do
                    for suffix in [ "f"; "F"; "d"; "D"; "m"; "M" ] do
                        expectTokens
                            (number + suffix)
                            [ TokenKind.NumericLiteralToken, number + suffix ]

                        expectLexicalOracle (number + suffix)

                expectLexicalOracle "1. 1.f 1.e2 1e+ 1e_2 0x_ 0b2 1uf 1.2UL"
            }
            test "ranges do not absorb a preceding integer" {
                expectTokens
                    "1..2 .5 1.ToString"
                    [
                        TokenKind.NumericLiteralToken, "1"
                        TokenKind.DotDotToken, ".."
                        TokenKind.NumericLiteralToken, "2"
                        TokenKind.NumericLiteralToken, ".5"
                        TokenKind.NumericLiteralToken, "1"
                        TokenKind.DotToken, "."
                        TokenKind.IdentifierToken, "ToString"
                    ]
            }
            test "characters and ordinary, verbatim, and UTF8 strings" {
                expectLexicalOracle
                    "'a' '\\'' '\\\\' '\\x41' '\\u0041' '\\U00000041' \"日本語😀\" \"a\\\"b\" @\"a\"\"b\r\nc\" \"x\"u8 \"x\"U8 @\"x\"u8"

                expectLexicalOracle "\"unterminated\nx 'unterminated\nx '\\\nx \"a\\\nb\""
            }
            test "ordinary interpolated strings are one token including escaped braces" {
                for source in
                    [
                        "$\"a{b}c\""
                        "$\"\""
                        "$\"{{a}} {{{b}}} \\\" \\\\ {c}\""
                        "$\"{new { X = \"y\", Y = new[] { 1, 2 } }}\""
                    ] do
                    expectString TokenKind.InterpolatedStringToken source
            }
            test "dollar-at interpolated strings retain verbatim escapes and newlines" {
                for source in [ "$@\"a{b}\\nc\""; "$@\"a\"\"b{{c}}\r\n{x}\"" ] do
                    expectString TokenKind.InterpolatedStringToken source
            }
            test "at-dollar interpolated strings retain verbatim escapes and newlines" {
                for source in [ "@$\"x{y}\""; "@$\"a\"\"b{{c}}\r\n{x}\"" ] do
                    expectString TokenKind.InterpolatedStringToken source
            }
            test "failed string prefixes preserve tokens, spans, and trivia" {
                let source = " /*lead*/ $$@@ //tail\r\n@name @$@;"
                let buffer = lex source
                expectLossless source buffer

                let expected =
                    [|
                        TokenKind.DollarToken, 10, 1, 0, 3, 0
                        TokenKind.DollarToken, 11, 1, 3, 0, 0
                        TokenKind.BadToken, 12, 1, 3, 0, 0
                        TokenKind.BadToken, 13, 1, 3, 0, 3
                        TokenKind.IdentifierToken, 23, 5, 6, 0, 1
                        TokenKind.BadToken, 29, 1, 7, 0, 0
                        TokenKind.DollarToken, 30, 1, 7, 0, 0
                        TokenKind.BadToken, 31, 1, 7, 0, 0
                        TokenKind.SemicolonToken, 32, 1, 7, 0, 0
                        TokenKind.EndOfFileToken, 33, 0, 7, 0, 0
                    |]
                    |> Array.map (fun (kind, start, length, triviaStart, leading, trailing) ->
                        {
                            Kind = kind
                            Start = start
                            Length = length
                            TriviaStart = triviaStart
                            LeadingCount = leading
                            TrailingCount = trailing
                        })

                let trivia =
                    [|
                        TriviaKind.WhitespaceTrivia, 0, 1
                        TriviaKind.MultiLineCommentTrivia, 1, 8
                        TriviaKind.WhitespaceTrivia, 9, 1
                        TriviaKind.WhitespaceTrivia, 14, 1
                        TriviaKind.SingleLineCommentTrivia, 15, 6
                        TriviaKind.EndOfLineTrivia, 21, 2
                        TriviaKind.WhitespaceTrivia, 28, 1
                    |]
                    |> Array.map (fun (kind, start, length) ->
                        {
                            Kind = kind
                            Start = start
                            Length = length
                        })

                Expect.equal (buffer.TokenSpan().ToArray()) expected "Exact pre-change tokens."
                Expect.equal (buffer.TriviaSpan().ToArray()) trivia "Exact pre-change trivia."

                for prefix in [ "$$@@"; "@@$$"; "$@$@"; "@@@" ] do
                    expectTokens
                        prefix
                        [
                            for ch in prefix do
                                (if ch = '$' then
                                     TokenKind.DollarToken
                                 else
                                     TokenKind.BadToken),
                                string ch
                        ]

                expectTokens
                    "$$@@name"
                    [
                        TokenKind.DollarToken, "$"
                        TokenKind.DollarToken, "$"
                        TokenKind.BadToken, "@"
                        TokenKind.IdentifierToken, "@name"
                    ]
            }
            test "failed string prefixes leave valid suffixes and later strings recognizable" {
                let ats = String('@', 1024)

                expectTokens
                    (ats + "\"x\"")
                    [
                        for _ in 1..1023 do
                            TokenKind.BadToken, "@"

                        TokenKind.StringLiteralToken, "@\"x\""
                    ]

                for literal in
                    [
                        "$@\"{x}\""
                        "@$\"{x}\""
                        "$$$\"\"\"{{{x}}}\"\"\""
                        "$\"{$@\"{x}\"} {$$\"\"\"{{y}}\"\"\"}\""
                        "$\"{$$@@ + $@\"{x}\"}\""
                    ] do
                    expectTokens
                        ("$$@@; /* gap */ " + literal)
                        [
                            TokenKind.DollarToken, "$"
                            TokenKind.DollarToken, "$"
                            TokenKind.BadToken, "@"
                            TokenKind.BadToken, "@"
                            TokenKind.SemicolonToken, ";"
                            TokenKind.InterpolatedStringToken, literal
                        ]

                expectTokens
                    (ats + "$@\"{x}\"")
                    [ TokenKind.InterpolatedStringToken, ats + "$@\"{x}\"" ]

                let buffer = lex "$$@@"
                Lexer.lex "$@\"{x}\"" buffer
                Expect.equal buffer.TokenCount 2 "Failure state is local to one lex call."

                Expect.equal
                    (buffer.Token 0).Kind
                    TokenKind.InterpolatedStringToken
                    "A reused buffer recognizes a string at the same offset."
            }
            test "a surplus prefix sigil scans the literal Roslyn's recovery scans" {
                for source in
                    [
                        "$$\"abc\""
                        "$$\"a\"\"b\""
                        "$$\"\"a\"\""
                        "$$\"\nabc\n\""
                        "$$\"{x}\""
                        "$$$\"a\"\"\"b\""
                        "x = $$\"abc\";"
                        "@@$\"x\""
                        "@@$\"a\r\nb\""
                        "$@@\"a\"\"b\""
                        "@$@\"a\"\"b\""
                        "$@@\"{\"a\"}\""
                        "$@@\"{$\"{x}\"}\""
                        "$@@\"\"\"{\"\"\"a\"\"\"}\"\"\""
                        "$$@\"a\"\"b\""
                        "$$@@\"\"\"{{x}}\"\"\""
                        "@@$$\"\"a\"\""
                        " /* lead */ $$\"abc\"; // tail\r\nnext"
                        " /* lead */ $@@\"{\"a\"}\"; // tail\r\nnext"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$$\"{{x}\nnext"
                        "$$\"\"\"{{x}\nnext"
                        "$$\"\"\"\"{{x}\nnext"
                        "$$\"\"\"{{x}y}}\"\"\""
                        "$@@\"{)\n\"; next"
                        "$@@\"{]\n\"; next"
                        "$@@\"{x)}\""
                        "$@@\"{x\nnext"
                        "$@@\"\"\"{x:a\"b}\"\"\""
                        "$$\"{{x:a\nb}}\""
                        "$$\"\"\"{{x:a\nb}}\"\"\""
                        "$@@\"\"\"\n{x:a\nb}\n\"\"\""
                        "$$\"{{x:a}\nnext"
                        "$$\"\"\"{{x:a}\nnext"
                        "$$\"\"\"{{x:a}b}}\"\"\""
                        "$$\"\"\"{{x}\"\"\"; next"
                        "$$\"\"\"{{F(}\n\"x\")}}\"\"\"; next"
                        "$$\"\"\"{{F(}x)}}\"\"\""
                        "$\"\"\"{F(}x)}\"\"\""
                        "$@@\"{(x}\nnext"
                        "$@@\"{F(}\nnext"
                        "$@@\"{(x}y\""
                        "$@@\"{F(}y\""
                        "$@@\"{x]}y\""
                        "$$\"{{x)}}\""
                        "$@@\"\"\"{\"\")@\"\"\"; next"
                        "$@@\"\"\"{\"\")\"\"\"; next"
                        "$@@\"{'a}\nnext"
                        "$$\"{{x)}}\nint y = 1;"
                        "$$@\"\"\"{{\"\" + $\"\"\"abc\"\"\"}}\"\"\"; next"
                        "$@@\"{$\"{x}\"}\""
                        "$@@\"\"\"{$\"\"\"abc\"\"\"}\"\"\""
                        "$@@\"\"\"{)}\nnext"
                        "$@@\"\"\"{)\n\"; next"
                        "$@@\"\"\"{\"\"}\nnext"
                        "$$\"{{)}}\n\"next\";"
                        "$@@\"{)\nnext"
                        "$@@\"\"\"{]\"\nnext"
                        "$@@\"\"\"{\"a\"}\nnext"
                        "$@@\"\"\"{\"a\"}{b\nnext"
                        "$@@\"\"\"{a}{b\"\nnext"
                        "$@@\"\"\"{@\"a\"\nnext"
                        "$@@\"\"\"{$\"a\"\nnext"
                        "$@@\"\"\"{a/*\"*/\nnext"
                        "$@@\"{x'a'\nnext"
                        "$@@\"\"\"{x:a\"\nint y = 1;"
                        "$@@\"\"\"{x:a\"\nb}\"\"\"; next"
                        "$@@\"\"\"{x:a\"b\"c\nnext"
                        "$@@\"\"\"{x:a\"b}\"\"\""
                        "$@@\"\"\"{x:a\nb}\"\"\""
                        "$@@\"\"\"\n{x:a\"\nb\nnext"
                        "$@@\"\"\"{\"\"{x}\"\"\"; next"
                        "$$@\"\"\"{{\"\"/*\"\"\"; next"
                        "$$@\"\"\"{{\"\"'a'\"\"\"; next"
                        "$$@\"\"\"{{\"\"}}\"\"\"; next"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$$\"\"\"{{x:a}{{\"\"\"; next"
                        "$$\"\"\"{{x:a}{{\"\"\"y\"\"\"}}\"\"\"; next"
                        "$$\"\"\"{{x}{{\"\"\"y\"\"\"}}\"\"\"; next"
                        "$$\"\"\"{{x:a}{{z}}\"\"\"; next"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$\"\"\"{x:a\"\nb}\"\"\""
                        "$\"\"\"{x:\"\nnext"
                        "$\"\"\"{x:a\"b\"c\nnext"
                        "$\"{x:a\nnext"
                        "$\"{x:a\"b\nnext"
                        "$\"\"\"{x\"\nnext"
                        "$\"{x\"\nnext"
                        "$@\"{x\"\nnext"
                        "$\"\"\"{x:a\"/*\"\"\"; next"
                        "$\"\"\"{x:a\"}\"\"\"; next"
                        "$\"\"\"{\"\"\"a\"\"\"}\"\"\""
                        "$\"\"\"{\"\"\"; next"
                        "$\"\"\"{\"\"\"a\"\"\"; next"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$\"{)\"; next"
                        "$\"{)x\"; next"
                        "$\"{]\"; next"
                        "$\"{x\"; next"
                        "$\"{)\n\"; next"
                        "$\"\"\"{)\n\"; next"
                        "$\"\"\"{)\"\"\"; next"
                        "$\"\"\"{)\"a\"}\"\"\"; next"
                        "$\"{)/*\"; next"
                        "$\"{)'a'\"; next"
                        "$\"{)}\"; next"
                        "$@\"{)\"; next"
                        "$\"{(}\"; next"
                        "$\"{)\"\"; next"
                        "$@\"{)\"\"; next"
                        "$@@\"{)\"\"; next"
                        "$\"{)}{x\"\"\"y\"\"\"}\"; next"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$$\"\"\"{{x:a}{{y\n}}\"\"\"; next"
                        "$\"\"\"{x:a\"{\"\"\"; next"
                        "$\"\"\"{x:a\"{z}\"\"\"; next"
                        "$\"\"\"{x:a\"}{b\"\"\"y\"\"\"}\"\"\"; next"
                        "$@@\"\"\"{\"a\"}{b\"\"\"x\"\"\"}\nnext"
                        "$@@\"\"\"{\"\"{x\"\"\"y\"\"\"}\nnext"
                        "$@\"{x:a\"\"{\"}\"; next"
                        "$@\"{x:a\"\"b}\"; next"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$\"\"\"}{\"\"]\nint y = 1;"
                        "$\"\"\"{\"\"]\nint y = 1;"
                        "$\"\"\"a}b{\"\"]\nint y = 1;"
                        "$\"\"\"}}{\"\"]\nint y = 1;"
                        "$$\"\"\"}{{\"\"]\nint y = 1;"
                        "$$\"\"\"}}{{\"\"]\nint y = 1;"
                        "$$\"\"\"}}}{{\"\"]\nint y = 1;"
                        "$\"}{\"\"]\nint y = 1;"
                        "$\"}}{\"\"]\nint y = 1;"
                        "$\"{x}}{\"\"]\nint y = 1;"
                        "$\"{x}}}{\"\"]\nint y = 1;"
                        "$\"\"\"{{x}}{\"\"]\nint y = 1;"
                        "$$\"\"\"{{{x}}}{{\"\"]\nint y = 1;"
                        "$\"\"\"}{x\"\nnext"
                        "$\"\"\"}{x)\"; next"
                        "$\"\"\"}\"\"\"; next"
                        "$\"\"\"a}b\"\"\"; next"
                        "$\"}\"; next"
                        "$\"\"\"{{x}} {\"y\"}\"\"\""
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$\"\"\"{{\"\")\nnext"
                        "$\"\"\"{{\"\"x\nnext"
                        "$\"\"\"{{{\"\")\nnext"
                        "$$\"\"\"{{\"\")\nnext"
                        "$$\"\"\"{{{\"\")\nnext"
                        "$$$\"\"\"{{{\"\")\nnext"
                        "$$$\"\"\"{{{{{{\"\")\nnext"
                        "$\"{{\"\")\nnext"
                        "$\"\"\"{{x}} {y}\"\"\""
                        "$$\"\"\"{{x}} {{y}}\"\"\""
                        "$\"\"\"{{\"a\"}}\"\"\"; next"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$@@\"{@x\"; next"
                        "$@@\"{@@x\"; next"
                        "$@@\"{@1\"; next"
                        "$@@\"{@ \"; next"
                        "$@@\"{@)\"; next"
                        "$@@\"{@+\"; next"
                        "$@@\"{@_x\"; next"
                        "$@@\"{@'\"; next"
                        "$@@\"{@$\"; next"
                        "$@@\"{@@\"; next"
                    ] do
                    expectLexicalOracle source

                for source in
                    [
                        "$\"abc\""
                        "$@\"x\""
                        "@$\"x\""
                        "$@\"a\"\"b\""
                        "$@\"\"\"x\"\"\""
                        "$$\"\"\"abc\"\"\""
                        "$$\"\"\"{{x}} {y}\"\"\""
                        "@\"x\""
                        "\"\"\"x\"\"\""
                        "$\"{$$\"\"\"{{x}}\"\"\"}\""
                        "$\"{F(x)}\""
                        "$\"{(x ? \"y\" : \"z\")}\""
                        "$\"\"\"{x}}\"\"\""
                    ] do
                    expectLexicalOracle source

                expectTokens
                    "$@$\"{x}\""
                    [
                        TokenKind.DollarToken, "$"
                        TokenKind.BadToken, "@"
                        TokenKind.InterpolatedStringToken, "$\"{x}\""
                    ]

                expectTokens
                    "$@@$@\"a\""
                    [
                        TokenKind.DollarToken, "$"
                        TokenKind.BadToken, "@"
                        TokenKind.BadToken, "@"
                        TokenKind.InterpolatedStringToken, "$@\"a\""
                    ]
            }
            test "a one-off allocation is not read as a per-call one" {
                let mutable first = true

                let once () =
                    if first then
                        first <- false
                        Array.zeroCreate<byte> 4096 |> ignore

                Expect.equal
                    (steadyStateAllocation 3 100 once)
                    0L
                    "A cost paid once lands in one batch, so the least is none."

                let always () = Array.zeroCreate<byte> 4096 |> ignore

                Expect.isGreaterThan
                    (steadyStateAllocation 3 100 always)
                    (100L * 4096L)
                    "A cost paid every call is in every batch, so the least still shows it."

                first <- true

                Expect.isGreaterThan
                    (steadyStateAllocation 1 100 once)
                    0L
                    "A single batch counts the one-off against the action."
            }

            test "failed string prefix recognition scales linearly without allocating" {
                expectLinearPrefixScaling "dollars" (fun n -> String('$', n))
                expectLinearPrefixScaling "at signs" (fun n -> String('@', n))

                expectLinearPrefixScaling "mixed" (fun n ->
                    String(Array.init n (fun i -> if i % 2 = 0 then '$' else '@')))

                expectLinearPrefixScaling "nested interpolation" (fun n ->
                    "$\"{" + String('$', n) + "}\"")

                expectLinearPrefixScaling "at signs before a string" (fun n ->
                    String('@', n) + "\"x\"")

                expectLinearPrefixScaling "dollars before a string" (fun n ->
                    String('$', n) + "\"x\"")

                expectLinearPrefixScaling "mixed before a string" (fun n ->
                    String(Array.init n (fun i -> if i % 2 = 0 then '$' else '@')) + "\"x\"")

                for label, sigil in [ "dollars", '$'; "at signs", '@' ] do
                    expectLinearPrefixScaling $"{label} after a recovered hole" (fun n ->
                        "$@@\"\"\"{\"\"" + String(sigil, n) + "x}\"\"\";")

                expectLinearPrefixScaling "mixed sigils after a recovered hole" (fun n ->
                    "$@@\"\"\"{\"\""
                    + String(Array.init n (fun i -> if i % 2 = 0 then '$' else '@'))
                    + "x}\"\"\";")
            }
            test "interpolation holes skip nested literal quotes, characters, and comments" {
                for source in
                    [
                        "$\"{(x ? \"y\" : \"z\")}\""
                        "$\"{@\"a\"\"b\r\nc\"}\""
                        "$\"{\"\"\"a\"b\"\"\"}\""
                        "$\"{\"\"\"\"a\"\"\"b\"\"\"\"}\""
                        "$\"{\"\"\"\nraw\n\"\"\"}\""
                        "$\"{$@\"{x} \"\"y\"\"\"}\""
                        "$\"{$$\"\"\"{{x}}\"\"\"}\""
                        "$\"{'}'} {'\\\''} {'\"'}\""
                        "$\"{x /* }\" */ + y // }\"\r\n}\""
                        "$\"{x[\"a:b\"]}\""
                    ] do
                    expectString TokenKind.InterpolatedStringToken source
            }
            test "single-line raw strings use the opening quote run as delimiter" {
                for source in
                    [
                        "\"\"\"raw\"\"\""
                        "\"\"\"a\"b\"\"c\\d{e}\"\"\""
                        "\"\"\"\"a\"\"\"b\"\"\"\""
                        "\"\"\"\"\"a\"\"\"\"b\"\"\"\"\""
                        "\"\"\"raw\"\"\"\""
                    ] do
                    expectString TokenKind.SingleLineRawStringLiteralToken source
            }
            test "multiline raw strings include opening whitespace, newlines, and indentation" {
                for source in
                    [
                        "\"\"\"\nraw\n\"\"\""
                        "\"\"\" \t\r\n  raw\r\n  \"\"\""
                        "\"\"\"\"\n  a\"\"\"b\n  \"\"\"\""
                        "\"\"\"\u0085raw\u0085\"\"\""
                    ] do
                    expectString TokenKind.MultiLineRawStringLiteralToken source
            }
            test "UTF8 raw strings have distinct single-line and multiline kinds" {
                for suffix in [ "u8"; "U8" ] do
                    expectString
                        TokenKind.Utf8SingleLineRawStringLiteralToken
                        ("\"\"\"raw\"\"\"" + suffix)

                    expectString
                        TokenKind.Utf8MultiLineRawStringLiteralToken
                        ("\"\"\"\nraw\n\"\"\"" + suffix)

                expectLexicalOracle "$\"x\"u8 $$\"\"\"x\"\"\"U8"
            }
            test "interpolated raw strings count dollars for hole braces" {
                for source in
                    [
                        "$$\"\"\"\na{{b}}c\n\"\"\""
                        "$\"\"\"a{\"b\"}c\"\"\""
                        "$$\"\"\"a{b}{{\"c\"}}d\"\"\""
                        "$$$\"\"\"a{{b}} {{{\"c\"}}}d\"\"\""
                        "$$\"\"\"a{{{new { X = \"x\" }}}}c\"\"\""
                        "$$\"\"\"\"a\"\"\"b{{\"\"\"x\"\"\"}}c\"\"\"\""
                        "$$\"\"\"\na{{\"\"\"\nx\n\"\"\"}}c\n\"\"\""
                    ] do
                    expectString TokenKind.InterpolatedStringToken source
            }
            test "format text respects outer quotes and escapes after a top-level colon" {
                for source in
                    [
                        "$\"{x,10:000.00}\""
                        "$\"{(x ? \"y\" : \"z\"):000}\""
                        "$\"{x:\\\"{{}}}\""
                        "$@\"{x:\"\"}\""
                        "$$\"\"\"{{x:\"}}after\"\"\""
                    ] do
                    expectString TokenKind.InterpolatedStringToken source

                expectLexicalOracle "$\"{x:\"a\"}\";"
                expectLexicalOracle "$\"{x ? \"a\" : \"b\"}\";"
            }
            test "unterminated raw and interpolated strings retain Roslyn boundaries" {
                for source in
                    [
                        "\"\"\""
                        "\"\"\"\"\"\";"
                        "\"\"\"raw\nnext\"\"\";"
                        "\"\"\"\nunterminated"
                        "$\"a\nx\";"
                        "$\"a{x\ny}z\";"
                        "$\"{x\";next"
                        "$@\"unterminated\nnext"
                        "$$\"\"\"raw\nnext\"\"\";"
                        "$$\"x\" $$$@\"x\" @$$\"x\""
                    ] do
                    expectLexicalOracle source
            }
            test "all operators and punctuators use longest match" {
                let cases =
                    [
                        "~", TokenKind.TildeToken
                        "!", TokenKind.ExclamationToken
                        "$", TokenKind.DollarToken
                        "%", TokenKind.PercentToken
                        "^", TokenKind.CaretToken
                        "&", TokenKind.AmpersandToken
                        "*", TokenKind.AsteriskToken
                        "(", TokenKind.OpenParenToken
                        ")", TokenKind.CloseParenToken
                        "-", TokenKind.MinusToken
                        "+", TokenKind.PlusToken
                        "=", TokenKind.EqualsToken
                        "{", TokenKind.OpenBraceToken
                        "}", TokenKind.CloseBraceToken
                        "[", TokenKind.OpenBracketToken
                        "]", TokenKind.CloseBracketToken
                        "|", TokenKind.BarToken
                        "\\", TokenKind.BackslashToken
                        ":", TokenKind.ColonToken
                        ";", TokenKind.SemicolonToken
                        "<", TokenKind.LessThanToken
                        ",", TokenKind.CommaToken
                        ">", TokenKind.GreaterThanToken
                        ".", TokenKind.DotToken
                        "?", TokenKind.QuestionToken
                        "/", TokenKind.SlashToken
                        "||", TokenKind.BarBarToken
                        "&&", TokenKind.AmpersandAmpersandToken
                        "--", TokenKind.MinusMinusToken
                        "++", TokenKind.PlusPlusToken
                        "::", TokenKind.ColonColonToken
                        "??", TokenKind.QuestionQuestionToken
                        "->", TokenKind.MinusGreaterThanToken
                        "!=", TokenKind.ExclamationEqualsToken
                        "==", TokenKind.EqualsEqualsToken
                        "=>", TokenKind.EqualsGreaterThanToken
                        "<=", TokenKind.LessThanEqualsToken
                        "<<", TokenKind.LessThanLessThanToken
                        "<<=", TokenKind.LessThanLessThanEqualsToken
                        ">=", TokenKind.GreaterThanEqualsToken
                        "/=", TokenKind.SlashEqualsToken
                        "*=", TokenKind.AsteriskEqualsToken
                        "|=", TokenKind.BarEqualsToken
                        "&=", TokenKind.AmpersandEqualsToken
                        "+=", TokenKind.PlusEqualsToken
                        "-=", TokenKind.MinusEqualsToken
                        "^=", TokenKind.CaretEqualsToken
                        "%=", TokenKind.PercentEqualsToken
                        "??=", TokenKind.QuestionQuestionEqualsToken
                        "..", TokenKind.DotDotToken
                        ">>", TokenKind.GreaterThanGreaterThanToken
                        ">>=", TokenKind.GreaterThanGreaterThanEqualsToken
                        ">>>", TokenKind.GreaterThanGreaterThanGreaterThanToken
                        ">>>=", TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken
                    ]

                for text, kind in cases do
                    expectTokens text [ kind, text ]

                expectTokens
                    "?. ?["
                    [
                        TokenKind.QuestionToken, "?"
                        TokenKind.DotToken, "."
                        TokenKind.QuestionToken, "?"
                        TokenKind.OpenBracketToken, "["
                    ]
            }
            test "combined right shifts also remain combined in type arguments" {
                expectTokens
                    "A<B<C>>"
                    [
                        TokenKind.IdentifierToken, "A"
                        TokenKind.LessThanToken, "<"
                        TokenKind.IdentifierToken, "B"
                        TokenKind.LessThanToken, "<"
                        TokenKind.IdentifierToken, "C"
                        TokenKind.GreaterThanGreaterThanToken, ">>"
                    ]
            }
            test "directives and malformed input remain lossless" {
                for source in
                    [
                        "$\"hi {x}\""
                        "$@\"hi {x}\""
                        "@$\"hi {x}\""
                        "$$\"\"\"hi {{x}}\"\"\""
                        "\"\"\"\r\nraw\r\n\"\"\""
                        "#if false\nunparsed text\n#endif"
                        "/// <summary>doc</summary>\nclass C {}"
                        "@ @1 \\u0020 \000 𐐀"
                        "'"
                        "\""
                        "@\""
                        "/*"
                        "\"\\"
                        "'\\"
                    ] do
                    expectLossless source (lex source)

                let random = Random 806
                let alphabet = "ab_1x09uULe.+-*/\\\"'@$#{}[]():\r\n\t\000\u0085日本\ud800\udc00"

                for _ in 1..200 do
                    let source =
                        String(
                            Array.init (random.Next(0, 400)) (fun _ ->
                                alphabet[random.Next alphabet.Length])
                        )

                    expectLossless source (lex source)
            }
            test "reusing a buffer clears tokens and trivia without allocating" {
                let buffer = lex "class C { string x = \"hi\"; } // comment\n"
                Lexer.lex "" buffer
                Expect.equal buffer.TokenCount 1 "Only the new EOF remains."
                Expect.equal buffer.TriviaCount 0 "No stale trivia."

                let source =
                    "/// <summary>Doc</summary>\n  /// more\n/** doc */ /* lead */ class C { double x = .5e+1d; string s = $\"{(x ? \"y\" : \"z\")}\"; string t = $$\"\"\"\n{{@\"x\"}}\n\"\"\"; string u = \"\"\"raw\"\"\"u8; } // end\n"

                Lexer.lex source buffer
                let allocated = allocatedWhileLexing source buffer
                Expect.equal allocated 0L "Steady-state lexing allocates no per-token objects."
                expectLossless source buffer
            }
            test
                "vectorized whitespace, comment, and string scanners match Roslyn and respect bounds" {
                let pad = String.replicate 64 " \t"

                let source =
                    pad
                    + "\v\f\u00a0class C {\n"
                    + pad
                    + "// "
                    + String.replicate 40 "comment "
                    + "\u2028"
                    + pad
                    + "/* "
                    + String.replicate 40 "block * / "
                    + "***/\r\n"
                    + pad
                    + "string a = \""
                    + String.replicate 32 "abc\\\""
                    + "\";\n"
                    + pad
                    + "string b = @\""
                    + String.replicate 32 "xyz\"\""
                    + "\";\n"
                    + pad
                    + "string c = \"\"\""
                    + String.replicate 32 "raw \"\" text "
                    + "\"\"\";\n"
                    + pad
                    + "string d = $\""
                    + String.replicate 16 "interp {{ "
                    + "{1 /* inner */ + 2:000}"
                    + String.replicate 16 " }} tail"
                    + "\";\n}\n"

                expectLexicalOracle source
                let buffer = lex source

                Expect.equal
                    (RoslynOracle.checkBuffer "vectorized.cs" source buffer)
                    (Ok())
                    "Vectorized scanners match Roslyn token and trivia spans."

                let bounded = "prefix /* open *" + "/ suffix"
                let rangeBuffer = TokenBuffer()
                Lexer.lexRange bounded 7 16 rangeBuffer
                let standalone = lex "/* open *"

                Expect.equal
                    (rangeBuffer.Trivia 0).Length
                    (standalone.Trivia 0).Length
                    "Bounded block comment must not match closing slash past finish."
            }
            test "vectorized identifier scan stops where the scalar scan stopped" {
                let long = String.replicate 40 "Name"

                let source =
                    "class C {\n"
                    + "    int a"
                    + long
                    + " = 1; int bé́x = 2; int c‍y = 3;\n"
                    + "    int éé = 4; int 一二 = 5; int d٠ = 6; int e‿f = 7;\n"
                    + "    int \\u0067\\u0068 = 8; int h\\u00e9 = 9; int i\\U00000041 = 10;\n"
                    + "    int \\u0041"
                    + long
                    + " = 11; int j_"
                    + long
                    + "é = 12;\n"
                    + "    int k = 13; var क्ष = a"
                    + long
                    + ";\n"
                    + "}\n"

                expectLexicalOracle source
                let buffer = lex source

                Expect.equal
                    (RoslynOracle.checkBuffer "identifiers.cs" source buffer)
                    (Ok())
                    "Vectorized identifier scan matches Roslyn token spans."

                let bounded = "class C { int ab" + "cd = 1; }"
                let rangeBuffer = TokenBuffer()
                Lexer.lexRange bounded 10 16 rangeBuffer
                let standalone = lex "int ab"

                Expect.equal
                    (rangeBuffer.Token 1).Length
                    (standalone.Token 1).Length
                    "Bounded identifier must not absorb characters past finish."
            }
            test "conditional window seeded lexing matches full lexWith on every buffer field" {
                let cases =
                    [
                        "using System;\nusing System.Text;\n// lead comment\nnamespace N;\npublic record R(int A)\n{\n    public async void Pre() => _ = $\"{A}\";\n#if FOO\n    public int X() => 1;\n#elif BAR\n    public string Y => $\"{A + 2}\";\n#else\n    public int Z = 3;\n#endif\n    public async void Post(int v) => _ = $\"{v}\";\n}\n",
                        [| [| "FOO" |]; [| "BAR" |]; [| "FOO"; "BAR" |]; [| "OTHER" |] |]
                        "class C\n{\n    Func<int> f = ()\n#if FOO\n        => 1;\n#else\n        => 2;\n#endif\n    Func<int> g = ()\n        => 3;\n}\n",
                        [| [| "FOO" |]; [| "NONE" |] |]
                        "#region Outer\nclass C {\n#if FOO\n    int x;\n#endif\n}\n#endregion\nclass D { int y; }\n",
                        [| [| "FOO" |] |]
                        "class C {\n    int a = 1;\n#if OPEN_COMMENT\n    string s = \"/*\";\n#endif\n    int b = 2; /* closed here */\n    int c = 3;\n}\n",
                        [| [| "OPEN_COMMENT" |]; [| "OTHER" |] |]
                    ]

                for source, symbolSets in cases do
                    let defaultBuf = TokenBuffer()
                    Lexer.lex source defaultBuf
                    let win = Lexer.buildConditionalWindow defaultBuf

                    for syms in symbolSets do
                        let expected = TokenBuffer()
                        Lexer.lexWith syms source expected
                        let actual = TokenBuffer()
                        Lexer.lexSeededFromDefault syms source defaultBuf &win actual |> ignore

                        Expect.equal
                            (actual.TokenSpan().ToArray())
                            (expected.TokenSpan().ToArray())
                            "Tokens match full lexWith."

                        Expect.equal
                            (actual.TriviaSpan().ToArray())
                            (expected.TriviaSpan().ToArray())
                            "Trivia match full lexWith."

                        Expect.equal
                            (actual.ParenArrowsList.ToArray())
                            (expected.ParenArrowsList.ToArray())
                            "ParenArrows match full lexWith."

                        Expect.equal
                            (actual.InterpolatedList.ToArray())
                            (expected.InterpolatedList.ToArray())
                            "Interpolated indices match full lexWith."

                        Expect.equal
                            (actual.ContextualOffsets.ToArray())
                            (expected.ContextualOffsets.ToArray())
                            "Contextual offsets match full lexWith."

                        Expect.equal
                            (actual.LastCommentTrivia,
                             actual.LastNonCommentTrivia,
                             actual.LastArrowOffset,
                             actual.LastParenArrowOffset,
                             actual.HasDisabledText,
                             actual.HasIfDirective,
                             actual.HasInterpolated)
                            (expected.LastCommentTrivia,
                             expected.LastNonCommentTrivia,
                             expected.LastArrowOffset,
                             expected.LastParenArrowOffset,
                             expected.HasDisabledText,
                             expected.HasIfDirective,
                             expected.HasInterpolated)
                            "Summary flags and cursors match full lexWith."
            }
            test "short or out-of-range Unicode escapes do not form valid identifiers" {
                expectTokens
                    "a\\u41"
                    [
                        TokenKind.IdentifierToken, "a"
                        TokenKind.BackslashToken, "\\"
                        TokenKind.IdentifierToken, "u41"
                    ]

                expectTokens
                    "\\u41"
                    [ TokenKind.BackslashToken, "\\"; TokenKind.IdentifierToken, "u41" ]

                expectTokens
                    "@\\u41"
                    [
                        TokenKind.BadToken, "@"
                        TokenKind.BackslashToken, "\\"
                        TokenKind.IdentifierToken, "u41"
                    ]

                expectTokens
                    "a\\U0041"
                    [
                        TokenKind.IdentifierToken, "a"
                        TokenKind.BackslashToken, "\\"
                        TokenKind.IdentifierToken, "U0041"
                    ]

                expectTokens
                    "a\\U00110000"
                    [
                        TokenKind.IdentifierToken, "a"
                        TokenKind.BackslashToken, "\\"
                        TokenKind.IdentifierToken, "U00110000"
                    ]

                expectLexicalOracle "x\\U0001D49Cy"
                expectTokens "a\\u0041b" [ TokenKind.IdentifierToken, "a\\u0041b" ]
                expectTokens "a\\U00000041b" [ TokenKind.IdentifierToken, "a\\U00000041b" ]
            }
            test
                "sharp inside an interpolation hole degrades string escapes and never runs directives" {
                for source in
                    [
                        "$\"{ # \" }\";"
                        "$@\"{ # \"\" }\";"
                        "$\"\"\"{ # \"\" }\"\"\";"
                        "$\"{ \"#\" }\";"
                        "$\"{ /* # */ \"a\" }\";"
                        "$\"{x:#}\";"
                        "$@\"{\n#if FOO\n1+1\n#else\n2+2\n#endif\n}\";"
                        "$\"{\n#if false\nignored }\n#endif\n}\";"
                        "#define FOO\nvar s = $\"{\n#if FOO\n1\n#endif\n}\";"
                    ] do
                    expectLexicalOracle source

                let holeSource = "outside {#if false\nignored }\n#endif\nx}"
                let holeBuffer = TokenBuffer()

                let struct (boundary, format) =
                    Lexer.lexInterpolation
                        holeSource
                        ("outside ".Length)
                        holeSource.Length
                        holeBuffer

                Expect.equal
                    boundary
                    (holeSource.IndexOf('}'))
                    "Interpolation hole closes at the first } even after #if false"

                Expect.isFalse format "Hole closes on brace rather than format colon"

                Expect.isTrue
                    holeBuffer.HasBadToken
                    "Directives inside interpolation holes produce BadToken '#'"

                Expect.isFalse
                    holeBuffer.HasMalformedTrivia
                    "Holes do not treat # lines as directive trivia"
            }
            test "malformed preprocessor directives match Roslyn tokens and mark malformed trivia" {
                for source in
                    [
                        "#define @foo\n#if @foo\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define\n#if @a\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define\n#if != false\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define\n#if != true\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define\n#if !!= false\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#if != false\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define\n#undef\n#if @a\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define true\n#if @a\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define \\u0074rue\n#if @a\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define tr\u200cue\n#if @a\nclass A {}\n#else\nclass B {}\n#endif\n"
                        "#define @a\n#if false\nclass A {}\n#elif @a\nclass B {}\n#endif\n"
                        "#define X /* c */\nclass A {}\n"
                        "#if true /* c */\nclass A {}\n#endif\n"
                    ] do
                    expectLexicalOracle source

                for malformedSource in
                    [
                        "#define @foo\n"
                        "#define\n"
                        "#undef\n"
                        "#define true\n"
                        "#undef false\n"
                        "#define X junk\n"
                        "#define X /* c */\n"
                        "#if\n#endif\n"
                        "#if @foo\n#endif\n"
                        "#if (true\n#endif\n"
                        "#if true)\n#endif\n"
                        "#if !\n#endif\n"
                        "#if A &&\n#endif\n"
                        "#if true /* c */\n#endif\n"
                        "#if false\n#elif\n#endif\n"
                        "#if true\n#else junk\n#endif\n"
                        "#if true\n#endif junk\n"
                    ] do
                    let buffer = lex malformedSource

                    Expect.isTrue
                        buffer.HasMalformedTrivia
                        ("Expected malformed trivia for: " + malformedSource)

                for validSource in
                    [
                        "#define FOO // ok\nclass A {}\n"
                        "#define \\u0074rue\nclass A {}\n"
                        "#define class\nclass A {}\n"
                        "#if true // ok\nclass A {}\n#else // ok\nclass B {}\n#endif // ok\n"
                        "#if !false && (true || A)\nclass A {}\n#endif\n"
                    ] do
                    let buffer = lex validSource

                    Expect.isFalse
                        buffer.HasMalformedTrivia
                        ("Expected valid directive trivia for: " + validSource)
            }
        ]
