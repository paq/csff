module Csff.Tests.UnicodeTests

open System
open Csff.Cli
open Csff.Lexer
open Csff.Printer
open Expecto

[<Literal>]
let private Nel = "\u0085"

[<Literal>]
let private LineSeparator = "\u2028"

[<Literal>]
let private ParagraphSeparator = "\u2029"

[<Literal>]
let private Nbsp = "\u00a0"

[<Literal>]
let private IdeographicSpace = "\u3000"

[<Literal>]
let private ZeroWidthNoBreakSpace = "\ufeff"

[<Literal>]
let private Hiragana = "\u3042"

[<Literal>]
let private Hyphen = "\u2010"

[<Literal>]
let private Hexagram = "\u4dc0"

[<Literal>]
let private Watch = "\u231a"

[<Literal>]
let private Grinning = "\U0001F600"

let private text (doc: DocumentBuffer) (source: string) (value: string) =
    let start = source.IndexOf(value, StringComparison.Ordinal)

    if start < 0 then
        invalidArg (nameof value) "Fixture text must be a source slice."

    doc.AddText(source, start, value.Length)

let private printWith source options build =
    use doc = new DocumentBuffer()
    use printer = new Printer()
    build doc
    printer.Print(source, doc, options)
    printer.OutputText

let private printAt width source build =
    printWith
        source
        { PrinterOptions.Default with
            Width = width
        }
        build

let private expectPrint source expected build =
    Expect.equal (printAt 100 source build) expected "Document layout matches the expected output."

let private formatAt width (source: string) =
    use worker = new Worker()

    let settings =
        { Settings.Default with
            AutoEndOfLine = false
            Printer =
                { PrinterOptions.Default with
                    Width = width
                }
        }

    Expect.isNull
        (worker.PrintChecked("test.cs", source, settings))
        "The formatted output passes the conformance check."

    worker.OutputText

let private format source = formatAt 100 source

let private expectFormat source expected =
    Expect.equal (format source) expected "The formatted output matches the expected bytes."
    Expect.equal (format expected) expected "The formatted output is a fixed point."

let private lex source =
    let buffer = TokenBuffer()
    Lexer.lex source buffer
    buffer

let private endOfLineTrivia (source: string) =
    let buffer = lex source

    [
        for i in 0 .. buffer.TriviaCount - 1 do
            let item = buffer.Trivia i

            if item.Kind = TriviaKind.EndOfLineTrivia then
                source.Substring(item.Start, item.Length)
    ]

let private expectedWidth (n: int) =
    if
        n >= 0x1100
        && (n <= 0x115f
            || n = 0x2329
            || n = 0x232a
            || (n >= 0x2e80 && n <= 0xa4cf && n <> 0x303f)
            || (n >= 0xac00 && n <= 0xd7a3)
            || (n >= 0xf900 && n <= 0xfaff)
            || (n >= 0xfe10 && n <= 0xfe19)
            || (n >= 0xfe30 && n <= 0xfe6f)
            || (n >= 0xff00 && n <= 0xff60)
            || (n >= 0xffe0 && n <= 0xffe6))
    then
        2u
    else
        1u

let private widthTable =
    [
        test "every code unit's printed width is the nine-range table" {
            let disagreeing =
                [
                    for n in 0..0xffff do
                        if PrintedWidth.character (char n) <> expectedWidth n then
                            sprintf "U+%04X" n
                ]

            Expect.equal disagreeing [] "No code unit may leave the nine-range table."
        }
        test "the table keeps its own answer where Unicode East_Asian_Width differs" {
            let cells =
                [
                    0x231a, 1u, "W"
                    0x2705, 1u, "W"
                    0x2b50, 1u, "W"
                    0xa960, 1u, "W"
                    0x3248, 2u, "A"
                    0x4dc0, 2u, "N"
                    0x303f, 1u, "N"
                    0x3042, 2u, "W"
                ]

            for codePoint, columns, property in cells do
                Expect.equal
                    (PrintedWidth.character (char codePoint))
                    columns
                    (sprintf
                        "U+%04X (East_Asian_Width %s) keeps csff's column count."
                        codePoint
                        property)
        }
        test "each half of a surrogate pair is one column" {
            for n in [ 0xd800; 0xdbff; 0xdc00; 0xdfff ] do
                Expect.equal
                    (PrintedWidth.character (char n))
                    1u
                    (sprintf "U+%04X is a lone code unit of width one." n)

            Expect.equal
                (PrintedWidth.measure (Grinning.AsSpan()))
                2u
                "An astral scalar costs two columns, one per code unit."
        }
        test "measure and measureLastLine sum the table across their fast paths" {
            let samples =
                [
                    for length in 0..24 do
                        String.replicate length "a"
                        String.replicate length "a" + Hiragana
                        Hiragana + String.replicate length "a"
                        String.replicate length "a" + Grinning
                        String.replicate length "a" + Nbsp
                        String.replicate length "a" + Watch
                        String.replicate length "a" + Hexagram
                ]

            for sample in samples do
                let expected = sample |> Seq.sumBy PrintedWidth.character

                Expect.equal
                    (PrintedWidth.measure (sample.AsSpan()))
                    expected
                    (sprintf "measure sums the table over %d code units." sample.Length)

                let struct (lastLine, multiline) = PrintedWidth.measureLastLine (sample.AsSpan())

                Expect.equal
                    lastLine
                    expected
                    (sprintf "measureLastLine sums the table over %d code units." sample.Length)

                Expect.isFalse multiline "A sample without a line break is not multiline."

            for marker in [ "\r"; "\n"; "\r\n" ] do
                for length in [ 4; 15; 16; 17; 30 ] do
                    let sample =
                        String.replicate length "a"
                        + marker
                        + Hiragana
                        + String.replicate length "b"

                    let struct (lastLine, multiline) =
                        PrintedWidth.measureLastLine (sample.AsSpan())

                    Expect.isTrue multiline "measureLastLine finds the line break."

                    Expect.equal
                        lastLine
                        (uint32 length + 2u)
                        "Only the final line's columns count."
        }
    ]

let private terminators =
    [
        for name, terminator in
            [ "U+0085", Nel; "U+2028", LineSeparator; "U+2029", ParagraphSeparator ] do
            test $"{name} terminates a source line" {
                let source =
                    "class C"
                    + terminator
                    + "{"
                    + terminator
                    + "void M() { }"
                    + terminator
                    + "}"
                    + terminator

                Expect.equal
                    (endOfLineTrivia source)
                    [ terminator; terminator; terminator; terminator ]
                    $"The lexer records {name} as end-of-line trivia."

                expectFormat source "class C\n{\n    void M() { }\n}\n"
            }

        test "U+00A0 and U+2010 are not line terminators" {
            let source = "class C { string s = \"a" + Nbsp + "b" + Hyphen + "c\"; }\n"

            Expect.equal
                (endOfLineTrivia source)
                [ "\n" ]
                "The only end-of-line trivia is the file's own final newline."

            expectFormat
                source
                ("class C\n{\n    string s = \"a" + Nbsp + "b" + Hyphen + "c\";\n}\n")
        }
    ]

let private squash =
    [
        for name, terminator in
            [ "U+0085", Nel; "U+2028", LineSeparator; "U+2029", ParagraphSeparator ] do
            test $"a squashed line counts {name} already in the output" {
                let source = "a" + terminator + "b"

                expectPrint source ("a" + terminator + "b\n") (fun d ->
                    text d source ("a" + terminator)
                    d.AddLine(LineKind.Hard, ElementFlags.Squash)
                    text d source "b")

                expectPrint source "a\nb\n" (fun d ->
                    text d source "a"
                    d.AddLine(LineKind.Hard, ElementFlags.Squash)
                    text d source "b")
            }

            test $"a blank-squashed line counts two of {name}" {
                let two = "a" + terminator + terminator + "b"

                expectPrint two ("a" + terminator + terminator + "b\n") (fun d ->
                    text d two ("a" + terminator + terminator)
                    d.AddLine(LineKind.Hard, ElementFlags.SquashBlank)
                    text d two "b")

                let one = "a" + terminator + "b"

                expectPrint one ("a" + terminator + "\nb\n") (fun d ->
                    text d one ("a" + terminator)
                    d.AddLine(LineKind.Hard, ElementFlags.SquashBlank)
                    text d one "b")
            }

        test "an ASCII newline is the control for both squash fixtures" {
            let one = "a\nb"

            expectPrint one "a\nb\n" (fun d ->
                text d one "a\n"
                d.AddLine(LineKind.Hard, ElementFlags.Squash)
                text d one "b")

            let two = "a\n\nb"

            expectPrint two "a\n\nb\n" (fun d ->
                text d two "a\n\n"
                d.AddLine(LineKind.Hard, ElementFlags.SquashBlank)
                text d two "b")
        }
    ]

let private trims =
    [
        for name, space in
            [
                "U+00A0", Nbsp
                "U+2003", "\u2003"
                "U+202F", "\u202f"
                "U+3000", IdeographicSpace
            ] do
            test $"the final trim removes a trailing {name}" {
                let source = "a" + space
                expectPrint source "a\n" (fun d -> text d source source)
            }

            test $"a comment ending in {name} loses it through the pipeline" {
                expectFormat ("class C { } // tail" + space + "\n") "class C { } // tail\n"

                expectFormat
                    ("class C\n{\n    // note:" + space + "\n    int x;\n}\n")
                    "class C\n{\n    // note:\n    int x;\n}\n"
            }

            test $"whitespace {name} before a comment is normalized and idempotent" {
                let indent = String.replicate 4 space

                expectFormat
                    ("class C\n{\n    int x;"
                     + space
                     + "// t\n    void M()\n    {\n"
                     + indent
                     + "// c\n    }\n}\n")
                    "class C\n{\n    int x; // t\n\n    void M()\n    {\n        // c\n    }\n}\n"
            }

            test
                $"documentation and block comments normalize {name} layout while keeping interior {name}" {
                let indent = String.replicate 4 space

                expectFormat
                    ("class C\n{\n    /// <summary>\n"
                     + indent
                     + "/// text"
                     + space
                     + "\n"
                     + indent
                     + "/// </summary>\n    int x;\n}\n")
                    "class C\n{\n    /// <summary>\n    /// text\n    /// </summary>\n    int x;\n}\n"

                expectFormat
                    ("class C\n{\n"
                     + indent
                     + "/* a"
                     + space
                     + "\n"
                     + indent
                     + "\n     * b\n     */\n    int x;\n}\n")
                    ("class C\n{\n    /* a\n\n"
                     + (if space = IdeographicSpace then
                            " * b\n */"
                        else
                            "     * b\n     */")
                     + "\n    int x;\n}\n")

                expectFormat
                    ("class C\n{\n    // a" + space + "b\n    string s = \"a" + space + "b\";\n}\n")
                    ("class C\n{\n    // a" + space + "b\n    string s = \"a" + space + "b\";\n}\n")

                expectFormat
                    (indent + "#if FLAG\nclass C { }\n" + indent + "#endif\n")
                    "#if FLAG\nclass C { }\n#endif\n"
            }

        test "TrimInitialLines stops after the last newline, not at the U+2028 before it" {
            let source = LineSeparator + "x"

            let build (d: DocumentBuffer) =
                text d source LineSeparator
                d.AddLine(LineKind.Hard)
                text d source "x"

            expectPrint source (LineSeparator + "\nx\n") build

            let actual =
                printWith
                    source
                    { PrinterOptions.Default with
                        TrimInitialLines = true
                    }
                    build

            Expect.equal actual "x\n" "The leading whitespace run is trimmed past U+2028."
        }
    ]

let private lexing =
    [
        test "a BOM in a block comment's source indentation occupies no column" {
            for prefix in
                [
                    ZeroWidthNoBreakSpace + "    "
                    "  " + ZeroWidthNoBreakSpace + "  "
                    "    " + ZeroWidthNoBreakSpace
                    ZeroWidthNoBreakSpace + "\t"
                ] do
                for opening in [ "/*"; "/**" ] do
                    expectFormat
                        ("class C\n{\n"
                         + prefix
                         + opening
                         + "\n     * body\n     */\n    int x;\n}\n")
                        ("class C\n{\n    " + opening + "\n     * body\n     */\n    int x;\n}\n")
        }
        test "a block comment's source indentation measures every lexer whitespace kind" {
            for prefix in [ "\v"; "\f"; "\u001a"; Nbsp; "\u2003"; "\u202f"; IdeographicSpace ] do
                let width = if prefix = IdeographicSpace then 2 else 1
                let indent = String(' ', width + 3)

                expectFormat
                    ("class C\n{\n "
                     + prefix
                     + " /*\n"
                     + indent
                     + "* body\n"
                     + indent
                     + "*/\n    int x;\n}\n")
                    "class C\n{\n    /*\n     * body\n     */\n    int x;\n}\n"
        }
        test "a doc comment's retained vertical-tab or form-feed prefix is not indentation" {
            for prefix in [ "\v"; "\f" ] do
                expectFormat
                    ("class C\n{\n" + prefix + "/**\n * body\n */\n    int x;\n}\n")
                    ("class C\n{\n    " + prefix + "/**\n     * body\n     */\n    int x;\n}\n")

                expectFormat
                    ("class C\n{\n  " + prefix + "  /**\n   * body\n   */\n    int x;\n}\n")
                    ("class C\n{\n    " + prefix + "  /**\n     * body\n     */\n    int x;\n}\n")
        }
        test "U+FEFF between tokens is whitespace" {
            expectFormat ("class C {" + ZeroWidthNoBreakSpace + " }\n") "class C { }\n"

            expectFormat
                ("class C { int " + ZeroWidthNoBreakSpace + " x = 1; }\n")
                "class C\n{\n    int x = 1;\n}\n"
        }
        test "U+FEFF inside an identifier is a part of it" {
            let source = "class" + ZeroWidthNoBreakSpace + "C { }\n"
            let buffer = lex source

            let identifiers =
                [
                    for i in 0 .. buffer.TokenCount - 1 do
                        let token = buffer.Token i

                        if token.Kind = TokenKind.IdentifierToken then
                            source.Substring(token.Start, token.Length)
                ]

            Expect.equal
                identifiers
                [ "class" + ZeroWidthNoBreakSpace + "C" ]
                "The Format character joins the two halves into one identifier."
        }
        test "non-ASCII identifiers round-trip" {
            let source = "class C\u00e9 { int " + Hiragana + " = 1; }\n"
            expectFormat source ("class C\u00e9\n{\n    int " + Hiragana + " = 1;\n}\n")
        }
    ]

let private commentLineColumn (marker: string) =
    let source = "/* head\n" + marker + " tail */"

    let output =
        printAt 100 source (fun d ->
            d.AddTag(Tag.StartIndent)
            d.AddLine(LineKind.Hard)
            d.AddComment(source, 0, source.Length, true, true, conditional = true)
            d.AddTag(Tag.EndIndent))

    let line =
        output.Split('\n')
        |> Array.find (fun line -> line.Contains(marker + " tail", StringComparison.Ordinal))

    line.Length - line.TrimStart().Length

let private commentDirectives =
    [
        test "a comment line reading #ife is not a directive, with any letter" {
            Expect.equal (commentLineColumn "#if") 0 "A directive line keeps its own column."

            Expect.equal
                (commentLineColumn "#ife")
                4
                "An ASCII letter after #if ends the keyword, so the line moves with the comment."

            Expect.equal
                (commentLineColumn "#if\u00e9")
                4
                "A non-ASCII letter after #if reads the same as an ASCII one."

            Expect.equal
                (commentLineColumn "#if\u0662")
                4
                "A non-ASCII digit after #if reads the same as an ASCII one."
        }
    ]

let private boundary
    name
    (source: int -> string -> string)
    (fitting: int -> string -> string)
    (broken: int -> string -> string)
    flip
    tail
    =
    test $"a width boundary in {name} measures the tail" {
        Expect.equal
            (format (source (flip - 1) tail))
            (fitting (flip - 1) tail)
            "The tail's last column lands on the width and the layout stays flat."

        Expect.equal
            (format (source flip tail))
            (broken flip tail)
            "One padding character further the tail overflows and the layout breaks."
    }

let private asciiBoundary name source fitting broken flip =
    test $"a width boundary in {name} measures a one-column tail one place later" {
        Expect.equal
            (format (source flip "z"))
            (fitting flip "z")
            "The ASCII tail still fits where the two-column tail did not."

        Expect.equal
            (format (source (flip + 1) "z"))
            (broken (flip + 1) "z")
            "It overflows one padding character later."
    }

let private pad n = String.replicate n "a"

let private tokenSource n tail =
    "class C\n{\n    int x = M(" + pad n + tail + ");\n}\n"

let private tokenFits n tail =
    "class C\n{\n    int x = M(" + pad n + tail + ");\n}\n"

let private tokenBroken n tail =
    "class C\n{\n    int x = M(\n        " + pad n + tail + "\n    );\n}\n"

let private rawSource n tail =
    "class C\n{\n    string s = \"\"\"" + pad n + tail + "\"\"\";\n}\n"

let private rawFits n tail = rawSource n tail

let private rawBroken n tail =
    "class C\n{\n    string s =\n        \"\"\"" + pad n + tail + "\"\"\";\n}\n"

let private holeSource n tail =
    "class C\n{\n    string s = $\"{M(" + pad n + tail + ")}\";\n}\n"

let private holeFits n tail = holeSource n tail

let private holeBroken n tail =
    "class C\n{\n    string s =\n        $\"{M(" + pad n + tail + ")}\";\n}\n"

let private leadingSource n tail =
    "class C\n{\n    int x =\n        /* c\n" + pad n + tail + " */ 1 + 2 + 3;\n}\n"

let private leadingFits n tail =
    "class C\n{\n    int x =\n        /* c\n" + pad n + tail + " */1 + 2 + 3;\n}\n"

let private leadingBroken n tail =
    "class C\n{\n    int x =\n        /* c\n"
    + pad n
    + tail
    + " */1\n        + 2\n        + 3;\n}\n"

let private trailingComment padding tail =
    let comment = "/* " + String.replicate padding "a" + tail + " */"
    let source = "a" + comment + "bbbbcccc"

    printAt 40 source (fun d ->
        d.AddTag(Tag.StartForceFlat)
        text d source "a"

        d.AddComment(
            source,
            source.IndexOf(comment, StringComparison.Ordinal),
            comment.Length,
            false,
            true
        )

        d.AddTag(Tag.EndForceFlat)
        d.StartGroup() |> ignore
        text d source "bbbb"
        d.AddLine(LineKind.Soft)
        text d source "cccc"
        d.EndGroup())

let private boundaries =
    [
        boundary "a token" tokenSource tokenFits tokenBroken 83 Hiragana
        asciiBoundary "a token" tokenSource tokenFits tokenBroken 83
        boundary "a raw literal" rawSource rawFits rawBroken 77 Hiragana
        asciiBoundary "a raw literal" rawSource rawFits rawBroken 77
        boundary "an interpolation hole" holeSource holeFits holeBroken 75 Hiragana
        asciiBoundary "an interpolation hole" holeSource holeFits holeBroken 75
        boundary "a leading comment's last line" leadingSource leadingFits leadingBroken 86 Hiragana
        asciiBoundary "a leading comment's last line" leadingSource leadingFits leadingBroken 86

        boundary "a raw literal holding an astral scalar" rawSource rawFits rawBroken 77 Grinning

        boundary "a raw literal holding U+4DC0" rawSource rawFits rawBroken 77 Hexagram
        boundary
            "a leading comment holding U+4DC0"
            leadingSource
            leadingFits
            leadingBroken
            86
            Hexagram

        test "U+231A is one column to csff even though Unicode calls it Wide" {
            Expect.equal
                (format (rawSource 77 Watch))
                (rawFits 77 Watch)
                "U+231A fits where a wide character does not."

            Expect.equal
                (format (rawSource 78 Watch))
                (rawBroken 78 Watch)
                "U+231A overflows exactly where an ASCII character does."
        }

        test "a trailing comment's measured width decides the next group's layout" {
            let wide = trailingComment 21 Hiragana
            let wideBroken = trailingComment 22 Hiragana
            let ascii = trailingComment 22 "z"
            let asciiBroken = trailingComment 23 "z"

            Expect.stringContains wide "bbbbcccc" "The group stays flat while the comment fits."
            Expect.stringContains wideBroken "bbbb\ncccc" "One column more and the group breaks."
            Expect.stringContains ascii "bbbbcccc" "A one-column tail still fits at that padding."
            Expect.stringContains asciiBroken "bbbb\ncccc" "It breaks one padding character later."
        }
    ]

let private conditional =
    [
        test "a non-ASCII raw literal inside a conditional region round-trips" {
            let source =
                "#if DEBUG\nclass C { string s = \"\"\""
                + Hiragana
                + "\u3044\"\"\"; }\n#else\nclass C { }\n#endif\n"

            expectFormat
                source
                ("#if DEBUG\nclass C\n{\n    string s = \"\"\""
                 + Hiragana
                 + "\u3044\"\"\";\n}\n#else\nclass C { }\n#endif\n")
        }
        test "a conditional region whose source holds U+2028 tracks literal ownership" {
            let source =
                "#if DEBUG"
                + LineSeparator
                + "class C { string s = \"\"\""
                + Hiragana
                + "\"\"\"; }"
                + LineSeparator
                + "#else"
                + LineSeparator
                + "class C { }"
                + LineSeparator
                + "#endif"
                + LineSeparator

            expectFormat
                source
                ("#if DEBUG\nclass C\n{\n    string s = \"\"\""
                 + Hiragana
                 + "\"\"\";\n}\n#else\nclass C { }\n#endif\n")
        }
    ]

let private codeUnits (values: int list) =
    String(values |> List.map char |> Array.ofList)

let private byteBuffer =
    [
        test "a surrogate pair split across adjacent slices survives" {
            let source = "\U0001F600"

            let printed =
                printWith source PrinterOptions.Default (fun d ->
                    d.AddText(source, 0, 1)
                    d.AddText(source, 1, 1))

            Expect.stringContains printed source "The astral scalar survives the split."
        }
        test "halves that are apart in the source join in the output" {
            let source = codeUnits [ 0xD83D; int 'X'; 0xDE00 ]

            let printed =
                printWith source PrinterOptions.Default (fun d ->
                    d.AddText(source, 0, 1)
                    d.AddText(source, 2, 1))

            Expect.stringContains printed "\U0001F600" "The halves still make one scalar."
        }
        test "an unpaired low surrogate does not reach back into the buffer" {
            let source = "ab\U0001F600"

            let printed =
                printWith source PrinterOptions.Default (fun d ->
                    d.AddText(source, 0, 2)
                    d.AddText(source, 3, 1))

            Expect.stringContains
                printed
                "ab\uFFFD"
                "The half follows the text as a replacement character."
        }
        test "an unpaired half stays a replacement character" {
            let source = codeUnits [ 0xD83D; int 'X'; int 'a'; int 'b' ]

            let printed =
                printWith source PrinterOptions.Default (fun d ->
                    d.AddText(source, 0, 1)
                    d.AddText(source, 2, 2))

            Expect.stringContains
                printed
                "\uFFFDab"
                "The half reads back as a replacement character."
        }
        test "a multi-megabyte output is not refused room it needs" {
            let source = "class C { string S = \"" + String('x', 5 * 1024 * 1024) + "\"; }"
            use worker = new Worker()

            Expect.isNull
                (worker.PrintChecked("big.cs", source, Settings.Default))
                "The multi-megabyte file's formatting is proven."

            let printed = worker.OutputText

            Expect.equal
                (printed.AsSpan().Count('x'))
                (5 * 1024 * 1024)
                "Every character of the literal is in the formatted output."
        }
    ]

let tests =
    TestList(
        [
            testList
                "unicode"
                (widthTable
                 @ terminators
                 @ squash
                 @ trims
                 @ lexing
                 @ commentDirectives
                 @ boundaries
                 @ conditional
                 @ byteBuffer)
        ],
        Normal
    )
