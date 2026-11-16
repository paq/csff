module Csff.Tests.Utf8Tests

open System
open System.Text
open Csff.Lexer
open Csff.Printer
open Expecto

let private encodeUtf8 (scalar: int) (buffer: byte array) =
    if scalar < 0x80 then
        buffer[0] <- byte scalar
        1
    elif scalar < 0x800 then
        buffer[0] <- byte (0xc0 ||| (scalar >>> 6))
        buffer[1] <- byte (0x80 ||| (scalar &&& 0x3f))
        2
    elif scalar < 0x10000 then
        buffer[0] <- byte (0xe0 ||| (scalar >>> 12))
        buffer[1] <- byte (0x80 ||| ((scalar >>> 6) &&& 0x3f))
        buffer[2] <- byte (0x80 ||| (scalar &&& 0x3f))
        3
    else
        buffer[0] <- byte (0xf0 ||| (scalar >>> 18))
        buffer[1] <- byte (0x80 ||| ((scalar >>> 12) &&& 0x3f))
        buffer[2] <- byte (0x80 ||| ((scalar >>> 6) &&& 0x3f))
        buffer[3] <- byte (0x80 ||| (scalar &&& 0x3f))
        4

let private encodeUtf16 (scalar: int) (buffer: char array) =
    if scalar < 0x10000 then
        buffer[0] <- char scalar
        1
    else
        buffer[0] <- char (0xd800 ||| ((scalar - 0x10000) >>> 10))
        buffer[1] <- char (0xdc00 ||| (scalar &&& 0x3ff))
        2

let private note (failures: ResizeArray<string>) (what: string) =
    if failures.Count < 20 then
        failures.Add what

let private report (failures: ResizeArray<string>) =
    if failures.Count > 0 then
        failtestf
            "The byte side disagrees with the character side:%s%s"
            Environment.NewLine
            (String.Join(Environment.NewLine, failures))

type private Coverage =
    {
        Scalars: int
        Astral: int
        WideInBmp: int
        NewLines: int
        Whitespace: int
        IdentifierStarts: int
    }

let private sweepScalars (failures: ResizeArray<string>) =
    let utf8 = Array.zeroCreate<byte> 4
    let reference = Array.zeroCreate<byte> 4
    let utf16 = Array.zeroCreate<char> 2
    let mutable scalars = 0
    let mutable astral = 0
    let mutable wideInBmp = 0
    let mutable newLines = 0
    let mutable whitespace = 0
    let mutable identifierStarts = 0

    for scalar in 0..0x10ffff do
        if scalar < 0xd800 || scalar > 0xdfff then
            scalars <- scalars + 1
            let size = encodeUtf8 scalar utf8
            let units = encodeUtf16 scalar utf16
            let bytes = ReadOnlySpan<byte>(utf8, 0, size)
            let chars = ReadOnlySpan<char>(utf16, 0, units)
            let tag = "U+" + scalar.ToString("X4") + " "

            let referenceSize = Encoding.UTF8.GetBytes(utf16, 0, units, reference, 0)

            if
                referenceSize <> size
                || not (ReadOnlySpan<byte>(reference, 0, referenceSize).SequenceEqual bytes)
            then
                note failures (tag + "the sweep's own UTF-8 encoding is not the BCL's")

            let struct (decoded, decodedSize) = Utf8Text.scalarAt bytes

            if decoded <> scalar || decodedSize <> size then
                note
                    failures
                    (tag
                     + "scalarAt decoded U+"
                     + decoded.ToString("X4")
                     + " over "
                     + string decodedSize
                     + " bytes")

            let mutable expected = 0u

            for i in 0 .. units - 1 do
                expected <- expected + PrintedWidth.character chars[i]

            if Utf8Text.scalarWidth scalar <> expected then
                note failures (tag + "scalarWidth")

            if Utf8Text.character bytes <> expected then
                note failures (tag + "character")

            if Utf8Text.measure bytes <> PrintedWidth.measure chars then
                note failures (tag + "measure")

            if Utf8Text.lastLine bytes <> PrintedWidth.lastLine chars then
                note failures (tag + "lastLine")

            if Utf8Text.firstLine bytes <> PrintedWidth.firstLine chars then
                note failures (tag + "firstLine")

            let struct (byteWidth, byteBreak) = Utf8Text.measureLastLine bytes
            let struct (charWidth, charBreak) = PrintedWidth.measureLastLine chars

            if byteWidth <> charWidth || byteBreak <> charBreak then
                note failures (tag + "measureLastLine")

            let first = chars[0]

            if Utf8Text.isNewLine bytes <> Lexer.Classify.newLine first then
                note failures (tag + "isNewLine")

            if Utf8Text.isWhitespace bytes <> Lexer.Classify.whitespace first then
                note failures (tag + "isWhitespace")

            if Utf8Text.isIdentifierStart bytes <> Lexer.Classify.identifierStart first then
                note failures (tag + "isIdentifierStart")

            if Utf8Text.isIdentifierPart bytes <> Lexer.Classify.identifierPart first then
                note failures (tag + "isIdentifierPart")

            if scalar >= 0x10000 then
                astral <- astral + 1
            elif expected = 2u then
                wideInBmp <- wideInBmp + 1

            if Utf8Text.isNewLine bytes then
                newLines <- newLines + 1

            if Utf8Text.isWhitespace bytes then
                whitespace <- whitespace + 1

            if Utf8Text.isIdentifierStart bytes then
                identifierStarts <- identifierStarts + 1

    {
        Scalars = scalars
        Astral = astral
        WideInBmp = wideInBmp
        NewLines = newLines
        Whitespace = whitespace
        IdentifierStarts = identifierStarts
    }

let private scalarSweep =
    test "every Unicode scalar measures and classifies the same from UTF-8 bytes" {
        let failures = ResizeArray<string>()
        let coverage = sweepScalars failures
        report failures

        Expect.equal
            coverage.Scalars
            (0x110000 - 0x800)
            "Every scalar but the surrogate range was swept."

        Expect.equal coverage.Astral (0x110000 - 0x10000) "Every astral scalar was swept."

        Expect.equal
            coverage.NewLines
            5
            "The five line terminators C# recognises are the only ones."

        Expect.equal coverage.WideInBmp 42247 "The wide ranges inside the BMP were reached."
        Expect.isGreaterThan coverage.Whitespace 15 "Unicode space separators were reached."
        Expect.isGreaterThan coverage.IdentifierStarts 40000 "Unicode letters were reached."
    }

let private surrogateHalves =
    test "a surrogate half is one column wide and classifies as nothing" {
        for unit in 0xd800..0xdfff do
            let ch = char unit
            let tag = "U+" + unit.ToString("X4")
            Expect.equal (PrintedWidth.character ch) 1u (tag + " is one column wide.")
            Expect.isFalse (Lexer.Classify.newLine ch) (tag + " is not a line terminator.")
            Expect.isFalse (Lexer.Classify.whitespace ch) (tag + " is not whitespace.")
            Expect.isFalse (Lexer.Classify.identifierStart ch) (tag + " starts no identifier.")
            Expect.isFalse (Lexer.Classify.identifierPart ch) (tag + " continues no identifier.")
    }

let private widthBoundaries =
    [
        0x10ff, 1u
        0x1100, 2u
        0x115f, 2u
        0x1160, 1u
        0x2328, 1u
        0x2329, 2u
        0x232a, 2u
        0x232b, 1u
        0x2e7f, 1u
        0x2e80, 2u
        0x303e, 2u
        0x303f, 1u
        0x3040, 2u
        0xa4cf, 2u
        0xa4d0, 1u
        0xabff, 1u
        0xac00, 2u
        0xd7a3, 2u
        0xd7a4, 1u
        0xf8ff, 1u
        0xf900, 2u
        0xfaff, 2u
        0xfb00, 1u
        0xfe0f, 1u
        0xfe10, 2u
        0xfe19, 2u
        0xfe1a, 1u
        0xfe2f, 1u
        0xfe30, 2u
        0xfe6f, 2u
        0xfe70, 1u
        0xfeff, 1u
        0xff00, 2u
        0xff60, 2u
        0xff61, 1u
        0xffdf, 1u
        0xffe0, 2u
        0xffe6, 2u
        0xffe7, 1u
        0x10000, 2u
        0x1f600, 2u
        0x10ffff, 2u
    ]

let private boundaryWidths =
    test "the wide ranges keep their boundaries on the byte side" {
        for scalar, width in widthBoundaries do
            let text = Char.ConvertFromUtf32 scalar
            let bytes = Encoding.UTF8.GetBytes text
            let tag = "U+" + scalar.ToString("X4")

            Expect.equal (Utf8Text.scalarWidth scalar) width (tag + " keeps its column count.")

            Expect.equal
                (Utf8Text.character (ReadOnlySpan<byte> bytes))
                width
                (tag + " keeps its column count read from UTF-8.")

            Expect.equal
                (PrintedWidth.measure (text.AsSpan()))
                width
                (tag + " keeps its column count read from UTF-16.")
    }

let private scalarText (scalar: int) = Char.ConvertFromUtf32 scalar

let private atoms =
    [
        "a"
        "_"
        "0"
        " "
        "\t"
        "{"
        "\r"
        "\n"
        "\r\n"
        "\n\r"
        String.replicate 20 "x"
        String.replicate 17 "y" + "一"
        "\u000b"
        "\u000c"
        "\u001a"
        "\u0085"
        "\u00a0"
        "\u2028"
        "\u2029"
        "\u3000"
        "\ufeff"
        "\u0300"
        "\u20e3"
        scalarText 0x1d165
        scalarText 0x10000
        scalarText 0x1f600
        scalarText 0x10ffff
    ]
    @ List.map (fst >> scalarText) widthBoundaries

let private contexts =
    [
        "a"
        " "
        "\r"
        "\n"
        "\r\n"
        String.replicate 20 "x"
        "一"
        scalarText 0x1f600
        "\u0300"
        "\u00a0"
        "\u3000"
        "\ufeff"
    ]

let private generated =
    seq {
        yield! atoms

        for left in atoms do
            for right in atoms do
                yield left + right

        for atom in atoms do
            for first in contexts do
                for second in contexts do
                    yield atom + first + second
                    yield first + atom + second
                    yield first + second + atom
    }

let private show (text: string) =
    let builder = StringBuilder()

    for rune in text.EnumerateRunes() do
        if rune.Value > 0x20 && rune.Value < 0x7f then
            builder.Append(char rune.Value) |> ignore
        else
            builder.Append("\\u{").Append(rune.Value.ToString("X4")).Append('}') |> ignore

    builder.ToString()

let private compareText (failures: ResizeArray<string>) (text: string) =
    let bytes = ReadOnlySpan<byte>(Encoding.UTF8.GetBytes text)
    let chars = text.AsSpan()

    if Utf8Text.measure bytes <> PrintedWidth.measure chars then
        note failures (show text + " measure")

    if Utf8Text.lastLine bytes <> PrintedWidth.lastLine chars then
        note failures (show text + " lastLine")

    if Utf8Text.firstLine bytes <> PrintedWidth.firstLine chars then
        note failures (show text + " firstLine")

    let struct (byteWidth, byteBreak) = Utf8Text.measureLastLine bytes
    let struct (charWidth, charBreak) = PrintedWidth.measureLastLine chars

    if byteWidth <> charWidth || byteBreak <> charBreak then
        note failures (show text + " measureLastLine")

    let mutable runes = text.EnumerateRunes()
    let mutable position = 0
    let mutable walked = true

    while walked && position < bytes.Length do
        let struct (scalar, size) = Utf8Text.scalarAt (bytes.Slice position)
        walked <- size > 0 && runes.MoveNext() && runes.Current.Value = scalar
        position <- position + max size 1

    if not (walked && not (runes.MoveNext())) then
        note failures (show text + " scalarAt walk")

    byteBreak

let private generatedText =
    test "generated strings measure the same from UTF-8 bytes as from UTF-16" {
        let failures = ResizeArray<string>()
        let mutable strings = 0
        let mutable multiline = 0

        for text in generated do
            strings <- strings + 1

            if compareText failures text then
                multiline <- multiline + 1

        report failures
        Expect.equal strings 34638 "The generated set is the size it is meant to be."
        Expect.isGreaterThan multiline 10000 "Strings holding a line break were generated."
    }

let tests =
    testList "utf8" [ scalarSweep; surrogateHalves; boundaryWidths; generatedText ]
