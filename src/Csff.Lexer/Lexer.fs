namespace Csff.Lexer

open System
open System.Buffers
open System.Globalization
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Runtime.Intrinsics
open System.Runtime.Intrinsics.Arm
open System.Text

[<assembly: InternalsVisibleTo("Csff.Printer")>]
[<assembly: InternalsVisibleTo("Csff.Tests")>]
do ()

module Lexer =
    let private newLineChars = SearchValues.Create("\r\n\u0085\u2028\u2029".AsSpan())

    let private doubleQuoteStopChars =
        SearchValues.Create("\"\\\r\n\u0085\u2028\u2029".AsSpan())

    let private singleQuoteStopChars =
        SearchValues.Create("'\\\r\n\u0085\u2028\u2029".AsSpan())

    let private singleLineRawStopChars =
        SearchValues.Create("\"\r\n\u0085\u2028\u2029".AsSpan())

    let private interpMultilineStopChars = SearchValues.Create("\"\\{}".AsSpan())

    let private interpSingleLineStopChars =
        SearchValues.Create("\"\\{}\r\n\u0085\u2028\u2029".AsSpan())

    let inline private isDigit (ch: char) = uint32 ch - uint32 '0' <= 9u

    let inline private isLetter (ch: char) =
        ((uint32 ch ||| 0x20u) - uint32 'a' <= 25u) || ch = '_'

    let inline private isNewLine ch =
        ch = '\r' || ch = '\n' || ch = '\u0085' || ch = '\u2028' || ch = '\u2029'

    let private isUnicodeLetter ch =
        match Char.GetUnicodeCategory ch with
        | UnicodeCategory.UppercaseLetter
        | UnicodeCategory.LowercaseLetter
        | UnicodeCategory.TitlecaseLetter
        | UnicodeCategory.ModifierLetter
        | UnicodeCategory.OtherLetter
        | UnicodeCategory.LetterNumber -> true
        | _ -> false

    let inline private isIdentifierStart ch =
        isLetter ch || (ch > '\u007f' && isUnicodeLetter ch)

    let private isUnicodeIdentifierPart ch =
        match Char.GetUnicodeCategory ch with
        | UnicodeCategory.DecimalDigitNumber
        | UnicodeCategory.ConnectorPunctuation
        | UnicodeCategory.NonSpacingMark
        | UnicodeCategory.SpacingCombiningMark
        | UnicodeCategory.Format -> true
        | _ -> isUnicodeLetter ch

    let inline private isIdentifierPart ch =
        isLetter ch || isDigit ch || (ch > '\u007f' && isUnicodeIdentifierPart ch)

    let inline private isWhitespace ch =
        ch = ' '
        || ch = '\t'
        || ch = '\v'
        || ch = '\f'
        || ch = '\u001a'
        || ch = '\ufeff'
        || (ch > '\u007f' && Char.GetUnicodeCategory ch = UnicodeCategory.SpaceSeparator)

    module private CharClass =
        [<Literal>]
        let IdentifierStart = 0uy

        [<Literal>]
        let Digit = 1uy

        [<Literal>]
        let SingleQuote = 2uy

        [<Literal>]
        let At = 3uy

        [<Literal>]
        let Backslash = 4uy

        [<Literal>]
        let DoubleQuote = 5uy

        [<Literal>]
        let Dollar = 6uy

        [<Literal>]
        let Dot = 7uy

        [<Literal>]
        let Operator = 8uy

        [<Literal>]
        let Whitespace = 9uy

        [<Literal>]
        let NewLine = 10uy

        [<Literal>]
        let Conflict = 11uy

        [<Literal>]
        let Slash = 12uy

        [<Literal>]
        let Hash = 13uy

    let private asciiClass: byte array =
        let table = Array.create 128 CharClass.Operator

        for ch in 'A' .. 'Z' do
            table[int ch] <- CharClass.IdentifierStart

        for ch in 'a' .. 'z' do
            table[int ch] <- CharClass.IdentifierStart

        for ch in '0' .. '9' do
            table[int ch] <- CharClass.Digit

        table[int '_'] <- CharClass.IdentifierStart
        table[int '\''] <- CharClass.SingleQuote
        table[int '@'] <- CharClass.At
        table[int '\\'] <- CharClass.Backslash
        table[int '"'] <- CharClass.DoubleQuote
        table[int '$'] <- CharClass.Dollar
        table[int '.'] <- CharClass.Dot
        table[int ' '] <- CharClass.Whitespace
        table[int '\t'] <- CharClass.Whitespace
        table[int '\v'] <- CharClass.Whitespace
        table[int '\f'] <- CharClass.Whitespace
        table[int '\u001a'] <- CharClass.Whitespace
        table[int '\r'] <- CharClass.NewLine
        table[int '\n'] <- CharClass.NewLine
        table[int '<'] <- CharClass.Conflict
        table[int '|'] <- CharClass.Conflict
        table[int '='] <- CharClass.Conflict
        table[int '/'] <- CharClass.Slash
        table[int '#'] <- CharClass.Hash
        table

    let private keywordLengths = Keywords.lengthsByFirstCharacter

    let inline private isContextualWordSpan
        (source: ReadOnlySpan<char>)
        (start: int)
        (length: int)
        =
        if uint32 start > uint32 source.Length || source.Length - start < length then
            false
        else
            let first = &Unsafe.AsRef(&MemoryMarshal.GetReference source)

            match length with
            | 3 ->
                Unsafe.Add(&first, start) = 'v'
                && Keywords.load2 &first (start + 1) = Keywords.pack2 'a' 'r'
            | 4 -> Keywords.load4 &first start = Keywords.pack4 'f' 'r' 'o' 'm'
            | 5 ->
                match Unsafe.Add(&first, start) with
                | 'a' ->
                    let w = Keywords.load4 &first (start + 1)
                    w = Keywords.pack4 's' 'y' 'n' 'c' || w = Keywords.pack4 'w' 'a' 'i' 't'
                | 'f' -> Keywords.load4 &first (start + 1) = Keywords.pack4 'i' 'e' 'l' 'd'
                | _ -> false
            | _ -> false

    let isContextualWord (source: string) (start: int) (length: int) =
        isContextualWordSpan (source.AsSpan()) start length

    let inline private keywordShaped (first: char) (length: int) =
        uint32 (length - 2) <= 8u
        && first <= '\u007f'
        && (Unsafe.Add(&MemoryMarshal.GetArrayDataReference keywordLengths, int first)
            &&& (1us <<< length))
           <> 0us

    let inline private keywordShapedAscii (first: char) (length: int) =
        uint32 (length - 2) <= 8u
        && (Unsafe.Add(&MemoryMarshal.GetArrayDataReference keywordLengths, int first)
            &&& (1us <<< length))
           <> 0us

    let inline private triviaClass (ch: char) =
        if ch <= '\u007f' then
            Unsafe.Add(&MemoryMarshal.GetArrayDataReference asciiClass, int ch)
        elif isWhitespace ch then
            CharClass.Whitespace
        elif isNewLine ch then
            CharClass.NewLine
        else
            CharClass.Operator

    let inline private tokenClass (ch: char) =
        if ch <= '\u007f' then
            Unsafe.Add(&MemoryMarshal.GetArrayDataReference asciiClass, int ch)
        elif isUnicodeLetter ch then
            CharClass.IdentifierStart
        else
            CharClass.Operator

    module internal Classify =
        let newLine ch = isNewLine ch
        let whitespace ch = isWhitespace ch
        let identifierStart ch = isIdentifierStart ch
        let identifierPart ch = isIdentifierPart ch

    let inline private peek (source: ReadOnlySpan<char>) sourceEnd position offset =
        let index = position + offset
        if index < sourceEnd then source[index] else '\000'

    let inline private hexValue ch =
        if isDigit ch then int ch - int '0'
        elif ch >= 'a' && ch <= 'f' then int ch - int 'a' + 10
        elif ch >= 'A' && ch <= 'F' then int ch - int 'A' + 10
        else -1

    let private unicodeEscape (source: ReadOnlySpan<char>) sourceEnd start (value: byref<char>) =
        let marker = peek source sourceEnd start 1

        if source[start] <> '\\' || (marker <> 'u' && marker <> 'U') then
            start
        else
            let limit = if marker = 'u' then 4 else 8
            let mutable position = start + 2
            let mutable digits = 0
            let mutable number = 0u

            while digits < limit && position < sourceEnd && hexValue source[position] >= 0 do
                number <- (number <<< 4) ||| uint32 (hexValue source[position])
                position <- position + 1
                digits <- digits + 1

            if digits = limit && number <= 0x10ffffu then
                value <-
                    if number <= 0xffffu then
                        char number
                    else
                        char (0xd800u + ((number - 0x10000u) >>> 10))

                position
            else
                start

    let private identifierEndScalar
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        (escaped: byref<bool>)
        =
        let mutable position = start
        let mutable scanning = true

        while scanning && position < sourceEnd do
            let ch = source[position]

            if isIdentifierPart ch then
                position <- position + 1
            elif ch = '\\' then
                let mutable value = '\000'
                let finish = unicodeEscape source sourceEnd position &value

                if finish > position && isIdentifierPart value then
                    escaped <- true
                    position <- finish
                else
                    scanning <- false
            else
                scanning <- false

        position

    [<Struct; NoEquality; NoComparison>]
    type internal MaskWindow =
        val mutable Base: int
        val mutable Ident: uint64
        val mutable Space: uint64

    let inline private maskOf (v: Vector512<uint16>) = v.ExtractMostSignificantBits()

    let private fillMaskWindow
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        sourceEnd
        (position: int)
        =
        window.Base <- position
        let available = min (sourceEnd - position) (source.Length - position)

        if AdvSimd.Arm64.IsSupported && available >= 64 then
            let first =
                &Unsafe.As<char, uint16>(&Unsafe.AsRef(&MemoryMarshal.GetReference source))

            let inline narrow16 (lo: Vector128<uint16>) (hi: Vector128<uint16>) : Vector128<byte> =
                AdvSimd.ExtractNarrowingSaturateUpper(AdvSimd.ExtractNarrowingSaturateLower lo, hi)

            let b0 =
                narrow16
                    (Vector128.LoadUnsafe(&first, unativeint position))
                    (Vector128.LoadUnsafe(&first, unativeint (position + 8)))

            let b1 =
                narrow16
                    (Vector128.LoadUnsafe(&first, unativeint (position + 16)))
                    (Vector128.LoadUnsafe(&first, unativeint (position + 24)))

            let b2 =
                narrow16
                    (Vector128.LoadUnsafe(&first, unativeint (position + 32)))
                    (Vector128.LoadUnsafe(&first, unativeint (position + 40)))

            let b3 =
                narrow16
                    (Vector128.LoadUnsafe(&first, unativeint (position + 48)))
                    (Vector128.LoadUnsafe(&first, unativeint (position + 56)))

            let zeroB = Vector128.Create(byte '0')
            let nineB = Vector128.Create 9uy
            let bit5B = Vector128.Create 0x20uy
            let aB = Vector128.Create(byte 'a')
            let twentyFiveB = Vector128.Create 25uy
            let underscoreB = Vector128.Create(byte '_')
            let spaceB = Vector128.Create(byte ' ')
            let tabB = Vector128.Create(byte '\t')

            let bitWeights =
                Vector128.Create(
                    1uy,
                    2uy,
                    4uy,
                    8uy,
                    16uy,
                    32uy,
                    64uy,
                    128uy,
                    1uy,
                    2uy,
                    4uy,
                    8uy,
                    16uy,
                    32uy,
                    64uy,
                    128uy
                )

            let inline identWeighted (v: Vector128<byte>) =
                let digit = Vector128.LessThanOrEqual(Vector128.Subtract(v, zeroB), nineB)

                let letter =
                    Vector128.LessThanOrEqual(
                        Vector128.Subtract(Vector128.BitwiseOr(v, bit5B), aB),
                        twentyFiveB
                    )

                let m =
                    Vector128.BitwiseOr(
                        Vector128.BitwiseOr(digit, letter),
                        Vector128.Equals(v, underscoreB)
                    )

                Vector128.BitwiseAnd(m, bitWeights)

            let inline blankWeighted (v: Vector128<byte>) =
                let m = Vector128.BitwiseOr(Vector128.Equals(v, spaceB), Vector128.Equals(v, tabB))
                Vector128.BitwiseAnd(m, bitWeights)

            let qId =
                AdvSimd.Arm64.AddPairwise(
                    AdvSimd.Arm64.AddPairwise(identWeighted b0, identWeighted b1),
                    AdvSimd.Arm64.AddPairwise(identWeighted b2, identWeighted b3)
                )

            let qSp =
                AdvSimd.Arm64.AddPairwise(
                    AdvSimd.Arm64.AddPairwise(blankWeighted b0, blankWeighted b1),
                    AdvSimd.Arm64.AddPairwise(blankWeighted b2, blankWeighted b3)
                )

            let packed = AdvSimd.Arm64.AddPairwise(qId, qSp).AsUInt64()
            window.Ident <- packed.GetElement 0
            window.Space <- packed.GetElement 1
        elif Vector512.IsHardwareAccelerated && available >= 64 then
            let first =
                &Unsafe.As<char, uint16>(&Unsafe.AsRef(&MemoryMarshal.GetReference source))

            let lo = Vector512.LoadUnsafe(&first, unativeint position)
            let hi = Vector512.LoadUnsafe(&first, unativeint (position + 32))
            let zero = Vector512.Create(uint16 '0')
            let nine = Vector512.Create 9us
            let bit5 = Vector512.Create 0x20us
            let a = Vector512.Create(uint16 'a')
            let twentyFive = Vector512.Create 25us
            let underscore = Vector512.Create(uint16 '_')
            let space = Vector512.Create(uint16 ' ')
            let tab = Vector512.Create(uint16 '\t')

            let inline ident (v: Vector512<uint16>) =
                let digit = Vector512.LessThanOrEqual(Vector512.Subtract(v, zero), nine)

                let letter =
                    Vector512.LessThanOrEqual(
                        Vector512.Subtract(Vector512.BitwiseOr(v, bit5), a),
                        twentyFive
                    )

                maskOf (
                    Vector512.BitwiseOr(
                        Vector512.BitwiseOr(digit, letter),
                        Vector512.Equals(v, underscore)
                    )
                )

            let inline blank (v: Vector512<uint16>) =
                maskOf (Vector512.BitwiseOr(Vector512.Equals(v, space), Vector512.Equals(v, tab)))

            window.Ident <- ident lo ||| (ident hi <<< 32)
            window.Space <- blank lo ||| (blank hi <<< 32)
        elif Vector256.IsHardwareAccelerated && available >= 64 then
            let first =
                &Unsafe.As<char, uint16>(&Unsafe.AsRef(&MemoryMarshal.GetReference source))

            let v0 = Vector256.LoadUnsafe(&first, unativeint position)
            let v1 = Vector256.LoadUnsafe(&first, unativeint (position + 16))
            let v2 = Vector256.LoadUnsafe(&first, unativeint (position + 32))
            let v3 = Vector256.LoadUnsafe(&first, unativeint (position + 48))
            let zero = Vector256.Create(uint16 '0')
            let nine = Vector256.Create 9us
            let bit5 = Vector256.Create 0x20us
            let a = Vector256.Create(uint16 'a')
            let twentyFive = Vector256.Create 25us
            let underscore = Vector256.Create(uint16 '_')
            let space = Vector256.Create(uint16 ' ')
            let tab = Vector256.Create(uint16 '\t')

            let inline ident256 (v: Vector256<uint16>) =
                let digit = Vector256.LessThanOrEqual(Vector256.Subtract(v, zero), nine)

                let letter =
                    Vector256.LessThanOrEqual(
                        Vector256.Subtract(Vector256.BitwiseOr(v, bit5), a),
                        twentyFive
                    )

                uint64 (
                    Vector256
                        .BitwiseOr(
                            Vector256.BitwiseOr(digit, letter),
                            Vector256.Equals(v, underscore)
                        )
                        .ExtractMostSignificantBits()
                )

            let inline blank256 (v: Vector256<uint16>) =
                uint64 (
                    Vector256
                        .BitwiseOr(Vector256.Equals(v, space), Vector256.Equals(v, tab))
                        .ExtractMostSignificantBits()
                )

            window.Ident <-
                ident256 v0
                ||| (ident256 v1 <<< 16)
                ||| (ident256 v2 <<< 32)
                ||| (ident256 v3 <<< 48)

            window.Space <-
                blank256 v0
                ||| (blank256 v1 <<< 16)
                ||| (blank256 v2 <<< 32)
                ||| (blank256 v3 <<< 48)
        else
            let count = max 0 (min 64 available)
            let mutable identBits = 0UL
            let mutable spaceBits = 0UL

            for i = 0 to count - 1 do
                let c = int source[position + i]

                if uint32 (c - 0x30) <= 9u || uint32 ((c ||| 0x20) - 0x61) <= 25u || c = 0x5f then
                    identBits <- identBits ||| (1UL <<< i)
                elif c = 0x20 || c = 0x09 then
                    spaceBits <- spaceBits ||| (1UL <<< i)

            window.Ident <- identBits
            window.Space <- spaceBits

    let inline private runEndInClass
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        sourceEnd
        (start: int)
        (identifiers: bool)
        =
        let mutable position = start
        let mutable result = -1

        while result < 0 do
            if uint32 (position - window.Base) >= 64u then
                fillMaskWindow &window source sourceEnd position

            let relative = position - window.Base
            let stops = ~~~(if identifiers then window.Ident else window.Space) >>> relative

            if stops = 0UL then
                position <- window.Base + 64

                if position >= sourceEnd then
                    result <- sourceEnd
            else
                result <- position + System.Numerics.BitOperations.TrailingZeroCount stops

        min result sourceEnd

    let private identifierPartChars =
        SearchValues.Create(
            "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz".AsSpan()
        )

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let private identifierEndProbe
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        (escaped: byref<bool>)
        =
        let offset =
            source.Slice(start, sourceEnd - start).IndexOfAnyExcept identifierPartChars

        if offset < 0 then
            sourceEnd
        else
            let stop = start + offset
            let ch = source[stop]

            if ch <= '\u007f' && ch <> '\\' then
                stop
            else
                identifierEndScalar source sourceEnd stop &escaped

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let private identifierEnd
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        (escaped: byref<bool>)
        =
        let stop = runEndInClass &window source sourceEnd start true

        if stop >= sourceEnd then
            sourceEnd
        else
            let ch = source[stop]

            if ch <= '\u007f' && ch <> '\\' then
                stop
            else
                identifierEndScalar source sourceEnd stop &escaped

    let inline private lineEnd (source: ReadOnlySpan<char>) sourceEnd start =
        if start >= sourceEnd then
            sourceEnd
        else
            let offset = source.Slice(start, sourceEnd - start).IndexOfAny(newLineChars)
            if offset < 0 then sourceEnd else start + offset

    let inline private newlineEnd (source: ReadOnlySpan<char>) sourceEnd position =
        if position = sourceEnd then
            position
        elif source[position] = '\r' && peek source sourceEnd position 1 = '\n' then
            position + 2
        else
            position + 1

    let inline private blockCommentEnd (source: ReadOnlySpan<char>) sourceEnd start =
        let bodyStart = start + 2

        if bodyStart >= sourceEnd then
            sourceEnd
        else
            let offset = source.Slice(bodyStart, sourceEnd - bodyStart).IndexOf("*/".AsSpan())

            if offset < 0 then sourceEnd else bodyStart + offset + 2

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let private skipWhitespace (source: ReadOnlySpan<char>) position limit =
        if position >= limit then
            position
        elif uint32 (int source[position] - 0x21) <= 0x5du then
            position
        else
            let offset = source.Slice(position, limit - position).IndexOfAnyExcept(' ', '\t')

            if offset < 0 then
                limit
            else
                let mutable finish = position + offset

                if not (uint32 (int source[finish] - 0x21) <= 0x5du) then
                    while finish < limit && isWhitespace source[finish] do
                        finish <- finish + 1

                finish

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let private skipWhitespaceInWindow
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        position
        limit
        =
        if position >= limit then
            position
        else
            let mutable finish = runEndInClass &window source limit position false

            if finish < limit && not (uint32 (int source[finish] - 0x21) <= 0x5du) then
                while finish < limit && isWhitespace source[finish] do
                    finish <- finish + 1

            finish

    let private directiveAllowed (buffer: TokenBuffer) start trailing =
        let mutable index = buffer.TriviaCount - 1
        let mutable allowed = not trailing
        let mutable scanning = true

        while scanning && index >= 0 && (buffer.Trivia index).Start >= start do
            match (buffer.Trivia index).Kind with
            | TriviaKind.WhitespaceTrivia
            | TriviaKind.SingleLineDocumentationCommentTrivia
            | TriviaKind.MultiLineDocumentationCommentTrivia -> index <- index - 1
            | TriviaKind.EndOfLineTrivia ->
                allowed <- true
                scanning <- false
            | TriviaKind.SingleLineCommentTrivia
            | TriviaKind.MultiLineCommentTrivia ->
                allowed <- false
                scanning <- false
            | _ -> scanning <- false

        allowed

    let private directiveIdentifier (source: ReadOnlySpan<char>) sourceEnd start limit =
        let mutable position = start
        let mutable first = true
        let mutable text: StringBuilder = null
        let mutable scanning = true

        while scanning && position < limit do
            let mutable ch = source[position]

            let finish =
                if ch = '\\' then
                    unicodeEscape source sourceEnd position &ch
                else
                    position + 1

            if
                finish > position
                && (if first then isIdentifierStart ch else isIdentifierPart ch)
            then
                let isEscaped = finish > position + 1
                let isFormat = ch > '\u007f' && Char.GetUnicodeCategory ch = UnicodeCategory.Format

                if isNull text && (isEscaped || isFormat) then
                    text <- StringBuilder(position - start + 8)

                    if position > start then
                        text.Append(source.Slice(start, position - start)) |> ignore

                if not (isNull text) && not isFormat then
                    text.Append ch |> ignore

                position <- finish
                first <- false
            else
                scanning <- false

        let fallback = if isNull text then null else text.ToString()
        struct (fallback, start, position - start, position)

    let inline private directiveSkip (source: ReadOnlySpan<char>) limit (position: byref<int>) =
        position <- skipWhitespace source position limit

    let inline private directiveHasUnexpectedTail (source: ReadOnlySpan<char>) position limit =
        let tail = skipWhitespace source position limit

        tail < limit
        && not (tail + 1 < limit && source[tail] = '/' && source[tail + 1] = '/')

    let inline private directiveAccept
        (source: ReadOnlySpan<char>)
        limit
        (position: byref<int>)
        (ch: char)
        =
        directiveSkip source limit &position

        if position < limit && source[position] = ch then
            position <- position + 1
            true
        else
            false

    let inline private directiveOperator
        (source: ReadOnlySpan<char>)
        limit
        (position: byref<int>)
        (a: char)
        (b: char)
        =
        directiveSkip source limit &position

        if position + 1 < limit && source[position] = a && source[position + 1] = b then
            position <- position + 2
            true
        else
            false

    let rec private directivePrimary
        (source: ReadOnlySpan<char>)
        sourceEnd
        limit
        (state: DirectiveState)
        (position: byref<int>)
        (malformed: byref<bool>)
        =
        RuntimeHelpers.EnsureSufficientExecutionStack()
        directiveSkip source limit &position

        if
            position < limit
            && source[position] = '!'
            && not (position + 1 < limit && source[position + 1] = '=')
        then
            position <- position + 1
            not (directivePrimary source sourceEnd limit state &position &malformed)
        elif directiveAccept source limit &position '(' then
            let value = directiveDisjunction source sourceEnd limit state &position &malformed

            if not (directiveAccept source limit &position ')') then
                malformed <- true

            value
        else
            let struct (fallback, idStart, idLen, finish) =
                directiveIdentifier source sourceEnd position limit

            if finish = position then
                malformed <- true

            position <- finish

            let span =
                if isNull fallback then
                    source.Slice(idStart, idLen)
                else
                    fallback.AsSpan()

            match Boolean.TryParse span with
            | true, value -> value
            | _ ->
                let lookup = state.Symbols.GetAlternateLookup<ReadOnlySpan<char>>()
                lookup.Contains span

    and private directiveEquality
        (source: ReadOnlySpan<char>)
        sourceEnd
        limit
        (state: DirectiveState)
        (position: byref<int>)
        (malformed: byref<bool>)
        =
        let mutable value =
            directivePrimary source sourceEnd limit state &position &malformed

        let mutable scanning = true

        while scanning do
            if directiveOperator source limit &position '=' '=' then
                let right = directivePrimary source sourceEnd limit state &position &malformed
                value <- value = right
            elif directiveOperator source limit &position '!' '=' then
                let right = directivePrimary source sourceEnd limit state &position &malformed
                value <- value <> right
            else
                scanning <- false

        value

    and private directiveConjunction
        (source: ReadOnlySpan<char>)
        sourceEnd
        limit
        (state: DirectiveState)
        (position: byref<int>)
        (malformed: byref<bool>)
        =
        let mutable value =
            directiveEquality source sourceEnd limit state &position &malformed

        while directiveOperator source limit &position '&' '&' do
            let right = directiveEquality source sourceEnd limit state &position &malformed
            value <- value && right

        value

    and private directiveDisjunction
        (source: ReadOnlySpan<char>)
        sourceEnd
        limit
        (state: DirectiveState)
        (position: byref<int>)
        (malformed: byref<bool>)
        =
        let mutable value =
            directiveConjunction source sourceEnd limit state &position &malformed

        while directiveOperator source limit &position '|' '|' do
            let right = directiveConjunction source sourceEnd limit state &position &malformed
            value <- value || right

        value

    let private directiveExpression
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        limit
        (state: DirectiveState)
        (malformed: byref<bool>)
        =
        let mutable position = start
        let value = directiveDisjunction source sourceEnd limit state &position &malformed

        if directiveHasUnexpectedTail source position limit then
            malformed <- true

        value

    let private directiveKind
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        limit
        (state: DirectiveState)
        (malformed: byref<bool>)
        =
        let wordStart = skipWhitespace source (start + 1) limit
        let mutable escaped = false

        let wordEnd =
            if wordStart < limit then
                identifierEndProbe source sourceEnd wordStart &escaped
            else
                wordStart

        let word = source.Slice(wordStart, wordEnd - wordStart)
        let argument = skipWhitespace source wordEnd limit
        let frames = state.Frames
        let top = frames.Count - 1
        let conditional = top >= 0 && not frames[top].Region && not frames[top].ElseSeen

        if word.SequenceEqual("if".AsSpan()) then
            let value = directiveExpression source sourceEnd argument limit state &malformed

            frames.Add
                {
                    Region = false
                    ParentActive = state.Active
                    BranchTaken = value
                    ElseSeen = false
                }

            state.Active <- state.Active && value
            TriviaKind.IfDirectiveTrivia
        elif conditional && word.SequenceEqual("elif".AsSpan()) then
            let frame = frames[top]
            let value = directiveExpression source sourceEnd argument limit state &malformed
            state.Active <- frame.ParentActive && not frame.BranchTaken && value

            frames[top] <-
                { frame with
                    BranchTaken = frame.BranchTaken || value
                }

            TriviaKind.ElifDirectiveTrivia
        elif conditional && word.SequenceEqual("else".AsSpan()) then
            if directiveHasUnexpectedTail source wordEnd limit then
                malformed <- true

            let frame = frames[top]
            state.Active <- frame.ParentActive && not frame.BranchTaken

            frames[top] <-
                { frame with
                    BranchTaken = true
                    ElseSeen = true
                }

            TriviaKind.ElseDirectiveTrivia
        elif top >= 0 && not frames[top].Region && word.SequenceEqual("endif".AsSpan()) then
            if directiveHasUnexpectedTail source wordEnd limit then
                malformed <- true

            state.Active <- frames[top].ParentActive
            frames.RemoveAt top
            TriviaKind.EndIfDirectiveTrivia
        elif word.SequenceEqual("region".AsSpan()) then
            frames.Add
                {
                    Region = true
                    ParentActive = state.Active
                    BranchTaken = false
                    ElseSeen = false
                }

            TriviaKind.RegionDirectiveTrivia
        elif top >= 0 && frames[top].Region && word.SequenceEqual("endregion".AsSpan()) then
            frames.RemoveAt top
            TriviaKind.EndRegionDirectiveTrivia
        elif word.SequenceEqual("define".AsSpan()) || word.SequenceEqual("undef".AsSpan()) then
            let isDefine = word.Length = 6

            let struct (fallback, idStart, idLen, finish) =
                directiveIdentifier source sourceEnd argument limit

            let isBoolean =
                isNull fallback
                && (let ident = source.Slice(idStart, idLen) in
                    ident.SequenceEqual("true".AsSpan()) || ident.SequenceEqual("false".AsSpan()))

            if finish = argument || isBoolean || directiveHasUnexpectedTail source finish limit then
                malformed <- true

            if state.Active then
                if finish = argument || isBoolean then
                    if isDefine then
                        state.Symbols.Add "" |> ignore
                    else
                        state.Symbols.Remove "" |> ignore
                elif isDefine then
                    let name =
                        if isNull fallback then
                            String(source.Slice(idStart, idLen))
                        else
                            fallback

                    state.Symbols.Add name |> ignore
                else
                    let lookup = state.Symbols.GetAlternateLookup<ReadOnlySpan<char>>()

                    let span =
                        if isNull fallback then
                            source.Slice(idStart, idLen)
                        else
                            fallback.AsSpan()

                    lookup.Remove span |> ignore

            if isDefine then
                TriviaKind.DefineDirectiveTrivia
            else
                TriviaKind.UndefDirectiveTrivia
        elif word.SequenceEqual("error".AsSpan()) then
            TriviaKind.ErrorDirectiveTrivia
        elif word.SequenceEqual("warning".AsSpan()) then
            TriviaKind.WarningDirectiveTrivia
        elif word.SequenceEqual("nullable".AsSpan()) then
            TriviaKind.NullableDirectiveTrivia
        elif word.SequenceEqual("line".AsSpan()) then
            if argument < limit && source[argument] = '(' then
                TriviaKind.LineSpanDirectiveTrivia
            else
                TriviaKind.LineDirectiveTrivia
        elif word.SequenceEqual("pragma".AsSpan()) then
            let mutable escaped = false

            let finish =
                if argument < limit then
                    identifierEndProbe source sourceEnd argument &escaped
                else
                    argument

            if source.Slice(argument, finish - argument).SequenceEqual("checksum".AsSpan()) then
                TriviaKind.PragmaChecksumDirectiveTrivia
            else
                TriviaKind.PragmaWarningDirectiveTrivia
        elif word.SequenceEqual("r".AsSpan()) then
            TriviaKind.ReferenceDirectiveTrivia
        elif word.SequenceEqual("load".AsSpan()) then
            TriviaKind.LoadDirectiveTrivia
        elif peek source sourceEnd wordStart 0 = '!' then
            TriviaKind.ShebangDirectiveTrivia
        elif peek source sourceEnd start 1 = ':' then
            TriviaKind.IgnoredDirectiveTrivia
        else
            TriviaKind.BadDirectiveTrivia

    let private disabledEnd (source: ReadOnlySpan<char>) sourceEnd (buffer: TokenBuffer) start =
        let mutable position = start
        let mutable scanning = true

        while scanning && position < sourceEnd do
            let content = skipWhitespace source position sourceEnd

            if content < sourceEnd && source[content] = '#' then
                scanning <- false
            else
                position <- newlineEnd source sourceEnd (lineEnd source sourceEnd content)

        if position > start then
            buffer.AddTrivia(TriviaKind.DisabledTextTrivia, start, position - start)

        position

    let private directiveEnd
        (source: ReadOnlySpan<char>)
        sourceEnd
        (buffer: TokenBuffer)
        start
        scanStart
        trailing
        (state: byref<DirectiveState>)
        =
        let finish = lineEnd source sourceEnd start
        let mutable malformed = false

        let kind =
            if not (directiveAllowed buffer scanStart trailing) then
                TriviaKind.SkippedTokensTrivia
            else
                if isNull state then
                    state <- buffer.AcquireDirectives()

                directiveKind source sourceEnd start finish state &malformed

        if malformed then
            buffer.MarkMalformedTrivia()

        let mutable position = newlineEnd source sourceEnd finish

        if
            not (isNull state)
            && not state.Active
            && kind <> TriviaKind.IfDirectiveTrivia
            && kind <> TriviaKind.ElifDirectiveTrivia
            && kind <> TriviaKind.ElseDirectiveTrivia
            && kind <> TriviaKind.EndIfDirectiveTrivia
            && kind <> TriviaKind.SkippedTokensTrivia
        then
            buffer.MarkInactive buffer.NextTriviaIndex

        buffer.AddTrivia(kind, start, position - start)

        if not trailing && not (isNull state) && not state.Active then
            position <- disabledEnd source sourceEnd buffer position

        position

    let inline private isLineDocumentation (source: ReadOnlySpan<char>) sourceEnd position =
        peek source sourceEnd position 2 = '/'
        && peek source sourceEnd position 3 <> '/'

    let inline private isBlockDocumentation (source: ReadOnlySpan<char>) sourceEnd position =
        peek source sourceEnd position 2 = '*'
        && peek source sourceEnd position 3 <> '*'
        && peek source sourceEnd position 3 <> '/'

    let private documentationLineEnd (source: ReadOnlySpan<char>) sourceEnd start =
        let mutable position = start
        let mutable scanning = true

        while scanning do
            position <- newlineEnd source sourceEnd (lineEnd source sourceEnd position)
            let next = skipWhitespace source position sourceEnd

            if
                peek source sourceEnd next 0 = '/'
                && peek source sourceEnd next 1 = '/'
                && isLineDocumentation source sourceEnd next
            then
                position <- next
            else
                scanning <- false

        position

    let private conflictMarker (source: ReadOnlySpan<char>) sourceStart sourceEnd position =
        if
            position + 7 > sourceEnd
            || (position > sourceStart && not (isNewLine source[position - 1]))
        then
            false
        else
            let ch = source[position]

            if ch <> '<' && ch <> '|' && ch <> '=' && ch <> '>' then
                false
            else
                let mutable offset = 1

                while offset < 7 && source[position + offset] = ch do
                    offset <- offset + 1

                offset = 7
                && (ch = '|' || ch = '=' || (position + 7 < sourceEnd && source[position + 7] = ' '))

    let private conflictEnd
        (source: ReadOnlySpan<char>)
        sourceStart
        sourceEnd
        (buffer: TokenBuffer)
        start
        =
        let mutable position = start
        let mutable scanning = true

        while scanning do
            let ch = source[position]
            let headerStart = position
            position <- lineEnd source sourceEnd position
            buffer.AddTrivia(TriviaKind.ConflictMarkerTrivia, headerStart, position - headerStart)
            let newlineStart = position

            while position < sourceEnd && isNewLine source[position] do
                position <- position + 1

            if position > newlineStart then
                buffer.AddLayoutTrivia(
                    TriviaKind.EndOfLineTrivia,
                    newlineStart,
                    position - newlineStart
                )

            if ch = '|' || ch = '=' then
                let disabledStart = position

                while position < sourceEnd
                      && not (
                          (source[position] = '>' || (ch = '|' && source[position] = '='))
                          && conflictMarker source sourceStart sourceEnd position
                      ) do
                    position <- position + 1

                if position > disabledStart then
                    buffer.AddTrivia(
                        TriviaKind.DisabledTextTrivia,
                        disabledStart,
                        position - disabledStart
                    )

                scanning <- position < sourceEnd
            else
                scanning <- false

        position

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let private triviaEnd
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        sourceStart
        sourceEnd
        (buffer: TokenBuffer)
        trailing
        allowDirectives
        (startPosition: byref<int>)
        (state: byref<DirectiveState>)
        =
        let start = startPosition
        let mutable position = start
        let mutable scanning = true
        let mutable scanLeading = false

        while scanning && position < sourceEnd do
            let triviaStart = position
            let ch = source[position]
            let cls = triviaClass ch

            if cls < CharClass.Whitespace then
                scanning <- false
            elif cls = CharClass.Whitespace then
                let nextPos = position + 1

                if
                    nextPos < sourceEnd
                    && source[nextPos] <= '\u007f'
                    && asciiClass[int source[nextPos]] < CharClass.Whitespace
                then
                    position <- nextPos
                    buffer.AddLayoutTrivia(TriviaKind.WhitespaceTrivia, triviaStart, 1)
                    scanning <- false
                else
                    position <- skipWhitespaceInWindow &window source nextPos sourceEnd

                    buffer.AddLayoutTrivia(
                        TriviaKind.WhitespaceTrivia,
                        triviaStart,
                        position - triviaStart
                    )

                    if
                        position < sourceEnd
                        && source[position] <= '\u007f'
                        && asciiClass[int source[position]] < CharClass.Whitespace
                    then
                        scanning <- false
            elif cls = CharClass.NewLine then
                position <- position + 1

                if ch = '\r' && position < sourceEnd && source[position] = '\n' then
                    position <- position + 1

                buffer.AddLayoutTrivia(
                    TriviaKind.EndOfLineTrivia,
                    triviaStart,
                    position - triviaStart
                )

                if trailing then
                    scanLeading <- true
                    scanning <- false
            elif cls = CharClass.Conflict then
                if not (conflictMarker source sourceStart sourceEnd position) then
                    scanning <- false
                elif trailing then
                    scanLeading <- true
                    scanning <- false
                else
                    position <- conflictEnd source sourceStart sourceEnd buffer position
            elif cls = CharClass.Slash then
                let next = peek source sourceEnd position 1

                if next = '/' then
                    if isLineDocumentation source sourceEnd position then
                        if trailing then
                            scanLeading <- true
                            scanning <- false
                        else
                            position <- documentationLineEnd source sourceEnd position

                            buffer.AddTrivia(
                                TriviaKind.SingleLineDocumentationCommentTrivia,
                                triviaStart,
                                position - triviaStart
                            )
                    else
                        position <- lineEnd source sourceEnd (position + 2)

                        buffer.AddTrivia(
                            TriviaKind.SingleLineCommentTrivia,
                            triviaStart,
                            position - triviaStart
                        )
                elif next = '*' then
                    let documentation = isBlockDocumentation source sourceEnd position

                    if documentation && trailing then
                        scanLeading <- true
                        scanning <- false
                    else
                        position <- blockCommentEnd source sourceEnd position

                        let kind =
                            if documentation then
                                TriviaKind.MultiLineDocumentationCommentTrivia
                            else
                                TriviaKind.MultiLineCommentTrivia

                        buffer.AddTrivia(kind, triviaStart, position - triviaStart)
                else
                    scanning <- false
            elif allowDirectives then
                position <- directiveEnd source sourceEnd buffer position start trailing &state

                if trailing then
                    scanLeading <- true
                    scanning <- false
            else
                scanning <- false

        startPosition <- position
        scanLeading

    let private integerSuffixEnd (source: ReadOnlySpan<char>) sourceEnd position =
        let ch = peek source sourceEnd position 0

        if ch = 'u' || ch = 'U' then
            let next = peek source sourceEnd position 1
            position + (if next = 'l' || next = 'L' then 2 else 1)
        elif ch = 'l' || ch = 'L' then
            let next = peek source sourceEnd position 1
            position + (if next = 'u' || next = 'U' then 2 else 1)
        else
            position

    let private numberEnd (source: ReadOnlySpan<char>) sourceEnd start =
        let mutable position = start
        let prefix = peek source sourceEnd start 1

        if
            source[start] = '0'
            && (prefix = 'x' || prefix = 'X' || prefix = 'b' || prefix = 'B')
        then
            let hex = prefix = 'x' || prefix = 'X'
            position <- position + 2

            while position < sourceEnd
                  && (source[position] = '_'
                      || (if hex then
                              hexValue source[position] >= 0
                          else
                              source[position] = '0' || source[position] = '1')) do
                position <- position + 1

            integerSuffixEnd source sourceEnd position
        else
            while position < sourceEnd && (isDigit source[position] || source[position] = '_') do
                position <- position + 1

            let mutable real = false

            if
                peek source sourceEnd position 0 = '.'
                && isDigit (peek source sourceEnd position 1)
            then
                real <- true
                position <- position + 1

                while position < sourceEnd && (isDigit source[position] || source[position] = '_') do
                    position <- position + 1

            let ch = peek source sourceEnd position 0

            if ch = 'e' || ch = 'E' then
                real <- true
                position <- position + 1
                let sign = peek source sourceEnd position 0

                if sign = '+' || sign = '-' then
                    position <- position + 1

                while position < sourceEnd && (isDigit source[position] || source[position] = '_') do
                    position <- position + 1

            match peek source sourceEnd position 0 with
            | 'f'
            | 'F'
            | 'd'
            | 'D'
            | 'm'
            | 'M' -> position + 1
            | _ ->
                if real then
                    position
                else
                    integerSuffixEnd source sourceEnd position

    let private quotedEnd (source: ReadOnlySpan<char>) sourceEnd start (quote: char) verbatim =
        let mutable position = start + (if verbatim then 2 else 1)
        let mutable scanning = true

        if verbatim then
            while scanning && position < sourceEnd do
                let offset = source.Slice(position, sourceEnd - position).IndexOf(quote)

                if offset < 0 then
                    position <- sourceEnd
                    scanning <- false
                else
                    position <- position + offset + 1

                    if position < sourceEnd && source[position] = quote then
                        position <- position + 1
                    else
                        scanning <- false
        else
            let stopChars =
                if quote = '"' then
                    doubleQuoteStopChars
                else
                    singleQuoteStopChars

            while scanning && position < sourceEnd do
                let offset = source.Slice(position, sourceEnd - position).IndexOfAny(stopChars)

                if offset < 0 then
                    position <- sourceEnd
                    scanning <- false
                else
                    position <- position + offset
                    let ch = source[position]

                    if ch = quote then
                        position <- position + 1
                        scanning <- false
                    elif ch = '\\' then
                        position <- min sourceEnd (position + 2)
                    else
                        scanning <- false

        position

    let inline private runEnd (source: ReadOnlySpan<char>) sourceEnd start (ch: char) =
        if start >= sourceEnd then
            sourceEnd
        else
            let offset = source.Slice(start, sourceEnd - start).IndexOfAnyExcept(ch)
            if offset < 0 then sourceEnd else start + offset

    let private rawIsMultiLine (source: ReadOnlySpan<char>) sourceEnd start =
        let position = skipWhitespace source start sourceEnd
        position < sourceEnd && isNewLine source[position]

    let private rawEnd (source: ReadOnlySpan<char>) sourceEnd start quotes multiline =
        let mutable position = start
        let mutable scanning = true

        while scanning && position < sourceEnd do
            let span = source.Slice(position, sourceEnd - position)

            let offset =
                if multiline then
                    span.IndexOf('"')
                else
                    span.IndexOfAny(singleLineRawStopChars)

            if offset < 0 then
                position <- sourceEnd
                scanning <- false
            else
                position <- position + offset

                if source[position] = '"' then
                    let finish = runEnd source sourceEnd position '"'
                    scanning <- finish - position < quotes
                    position <- finish
                else
                    scanning <- false

        position

    let rec private stringEnd
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        (kind: byref<TokenKind>)
        (failedPrefixEnd: byref<int>)
        =
        let mutable quoteStart = start
        let mutable dollars = 0
        let mutable ats = 0
        let mutable atFollowedDollar = false

        while quoteStart < sourceEnd
              && (source[quoteStart] = '@' || (source[quoteStart] = '$' && not atFollowedDollar)) do
            if source[quoteStart] = '$' then
                dollars <- dollars + 1
            else
                ats <- ats + 1
                atFollowedDollar <- dollars > 0

            quoteStart <- quoteStart + 1

        if peek source sourceEnd quoteStart 0 <> '"' then
            failedPrefixEnd <- quoteStart
            start
        elif dollars = 0 && ats > 1 then
            failedPrefixEnd <- quoteStart - 1
            start
        else
            let quoteRun = runEnd source sourceEnd quoteStart '"' - quoteStart

            let surplus = ats > 1 || (dollars > 1 && (ats > 0 || quoteRun < 3))
            let verbatim = ats > 0 && not surplus

            let quotes =
                if surplus || (not verbatim && quoteRun >= 3) then
                    quoteRun
                else
                    1

            let raw = surplus || quotes >= 3
            let contentStart = quoteStart + quotes
            let multiline = verbatim || (raw && rawIsMultiLine source sourceEnd contentStart)

            if dollars > 0 then
                kind <- TokenKind.InterpolatedStringToken
                let mutable ended = false
                let mutable degraded = surplus

                interpolatedTextEnd
                    source
                    sourceEnd
                    contentStart
                    verbatim
                    surplus
                    quotes
                    multiline
                    (if raw then dollars else 1)
                    false
                    &ended
                    &degraded
                    &failedPrefixEnd
            else
                let mutable position =
                    if raw then
                        rawEnd source sourceEnd contentStart quotes multiline
                    else
                        quotedEnd source sourceEnd start '"' verbatim

                kind <-
                    if raw then
                        if multiline then
                            TokenKind.MultiLineRawStringLiteralToken
                        else
                            TokenKind.SingleLineRawStringLiteralToken
                    else
                        TokenKind.StringLiteralToken

                if
                    (peek source sourceEnd position 0 = 'u'
                     || peek source sourceEnd position 0 = 'U')
                    && peek source sourceEnd position 1 = '8'
                then
                    position <- position + 2

                    kind <-
                        if raw then
                            if multiline then
                                TokenKind.Utf8MultiLineRawStringLiteralToken
                            else
                                TokenKind.Utf8SingleLineRawStringLiteralToken
                        else
                            TokenKind.Utf8StringLiteralToken

                position

    and private interpolatedTextEnd
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        verbatim
        surplus
        quotes
        multiline
        braces
        format
        (ended: byref<bool>)
        (degraded: byref<bool>)
        (failedPrefixEnd: byref<int>)
        =
        RuntimeHelpers.EnsureSufficientExecutionStack()
        let raw = surplus || quotes >= 3
        let mutable position = start
        let mutable scanning = true

        let stopChars =
            if multiline || format then
                interpMultilineStopChars
            else
                interpSingleLineStopChars

        while scanning && position < sourceEnd do
            let offset = source.Slice(position, sourceEnd - position).IndexOfAny(stopChars)

            if offset < 0 then
                position <- sourceEnd
                scanning <- false
            else
                position <- position + offset
                let ch = source[position]

                if ch = '"' then
                    if raw then
                        let finish = runEnd source sourceEnd position '"'

                        if finish - position >= quotes then
                            ended <- true
                        elif format then
                            degraded <- true
                            scanning <- false

                        position <- finish
                    elif verbatim && peek source sourceEnd position 1 = '"' then
                        position <- position + 2
                    else
                        position <- position + 1
                        ended <- true

                    if ended then
                        scanning <- false
                elif not multiline && not format && isNewLine ch then
                    ended <- true
                    scanning <- false
                elif not raw && not verbatim && ch = '\\' then
                    position <- min sourceEnd (position + 2)
                elif format && ch = '}' then
                    let finish = runEnd source sourceEnd position '}'

                    if finish - position >= braces then
                        position <- position + braces
                    else
                        position <- finish
                        degraded <- true

                    scanning <- false
                elif not format && ch = '{' then
                    let finish = runEnd source sourceEnd position '{'
                    let count = finish - position
                    position <- finish

                    if raw && count >= braces * 2 then
                        degraded <- true

                    if (raw && count >= braces) || (not raw && count % 2 = 1) then
                        position <-
                            interpolationEnd
                                source
                                sourceEnd
                                position
                                verbatim
                                surplus
                                quotes
                                multiline
                                braces
                                &ended
                                &degraded
                                &failedPrefixEnd

                        scanning <- not ended
                elif not format && ch = '}' then
                    let finish = runEnd source sourceEnd position '}'
                    let count = finish - position

                    if (raw && count >= braces) || (not raw && count % 2 = 1) then
                        degraded <- true

                    position <- finish
                else
                    position <- position + 1

        if position = sourceEnd then
            ended <- true

        position

    and private interpolationEnd
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        verbatim
        surplus
        quotes
        multiline
        braces
        (ended: byref<bool>)
        (degraded: byref<bool>)
        (failedPrefixEnd: byref<int>)
        =
        let mutable position = start
        let mutable depth = 0
        let mutable parens = 0
        let mutable brackets = 0
        let mutable scanning = true
        let raw = surplus || quotes >= 3

        while scanning && position < sourceEnd do
            let ch = source[position]
            let mutable nestedKind = TokenKind.BadToken

            let quoteRunEnd =
                if not (degraded && ch = '"') then position
                elif raw then runEnd source sourceEnd position '"'
                else position + 1

            let nestedEnd =
                if
                    quoteRunEnd = position
                    && (ch = '"' || ch = '@' || ch = '$')
                    && position >= failedPrefixEnd
                then
                    stringEnd source sourceEnd position &nestedKind &failedPrefixEnd
                else
                    position

            if quoteRunEnd > position then
                ended <- quoteRunEnd - position >= quotes
                scanning <- false
                position <- quoteRunEnd
            elif nestedEnd > position then
                position <- nestedEnd
            elif ch = '\'' then
                position <- quotedEnd source sourceEnd position '\'' false
            elif ch = '/' && peek source sourceEnd position 1 = '/' then
                position <- lineEnd source sourceEnd (position + 2)
            elif ch = '/' && peek source sourceEnd position 1 = '*' then
                position <- blockCommentEnd source sourceEnd position
            elif ch = '{' then
                depth <- depth + 1
                position <- position + 1
            elif ch = '}' then
                if depth > 0 then
                    depth <- depth - 1
                    position <- position + 1
                elif surplus && (parens > 0 || brackets > 0) then
                    position <- position + 1
                else
                    let finish = runEnd source sourceEnd position '}'

                    if finish - position >= braces then
                        position <- position + braces
                        scanning <- false
                    elif parens = 0 && brackets = 0 then
                        position <- finish
                        degraded <- true
                        scanning <- false
                    else
                        position <- finish
            elif ch = ':' && depth = 0 && parens = 0 && brackets = 0 then
                position <-
                    interpolatedTextEnd
                        source
                        sourceEnd
                        (position + 1)
                        verbatim
                        surplus
                        quotes
                        multiline
                        braces
                        true
                        &ended
                        &degraded
                        &failedPrefixEnd

                scanning <- false
            elif ch = '(' || ch = '[' then
                if ch = '(' then
                    parens <- parens + 1
                else
                    brackets <- brackets + 1

                position <- position + 1
            elif ch = ')' || ch = ']' then
                let matched = if ch = ')' then parens > 0 else brackets > 0

                if matched then
                    if ch = ')' then
                        parens <- parens - 1
                    else
                        brackets <- brackets - 1
                else
                    degraded <- true

                position <- position + 1
            elif ch = '#' then
                degraded <- true
                position <- position + 1
            else
                position <- position + 1

        position

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let private tokenKind
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        sourceEnd
        (position: byref<int>)
        (failedPrefixEnd: byref<int>)
        =
        let start = position
        let ch = source[start]
        let mutable kind = TokenKind.BadToken
        position <- start + 1
        let cls = tokenClass ch

        if cls >= CharClass.DoubleQuote then
            let stringFinish =
                if cls <= CharClass.Dollar && start >= failedPrefixEnd then
                    stringEnd source sourceEnd start &kind &failedPrefixEnd
                else
                    start

            if stringFinish > start then
                position <- stringFinish
            elif cls = CharClass.Dot && isDigit (peek source sourceEnd start 1) then
                position <- numberEnd source sourceEnd start
                kind <- TokenKind.NumericLiteralToken
            else
                let next = peek source sourceEnd start 1

                match ch with
                | '~' -> kind <- TokenKind.TildeToken
                | '(' -> kind <- TokenKind.OpenParenToken
                | ')' -> kind <- TokenKind.CloseParenToken
                | '{' -> kind <- TokenKind.OpenBraceToken
                | '}' -> kind <- TokenKind.CloseBraceToken
                | '[' -> kind <- TokenKind.OpenBracketToken
                | ']' -> kind <- TokenKind.CloseBracketToken
                | ';' -> kind <- TokenKind.SemicolonToken
                | ',' -> kind <- TokenKind.CommaToken
                | '$' -> kind <- TokenKind.DollarToken
                | '#' -> kind <- TokenKind.BadToken
                | '.' ->
                    if next = '.' then
                        position <- start + 2
                        kind <- TokenKind.DotDotToken
                    else
                        kind <- TokenKind.DotToken
                | ':' ->
                    if next = ':' then
                        position <- start + 2
                        kind <- TokenKind.ColonColonToken
                    else
                        kind <- TokenKind.ColonToken
                | '?' ->
                    if next = '?' then
                        position <- start + 2

                        if peek source sourceEnd start 2 = '=' then
                            position <- start + 3
                            kind <- TokenKind.QuestionQuestionEqualsToken
                        else
                            kind <- TokenKind.QuestionQuestionToken
                    else
                        kind <- TokenKind.QuestionToken
                | '+' ->
                    if next = '+' then
                        position <- start + 2
                        kind <- TokenKind.PlusPlusToken
                    elif next = '=' then
                        position <- start + 2
                        kind <- TokenKind.PlusEqualsToken
                    else
                        kind <- TokenKind.PlusToken
                | '-' ->
                    if next = '-' then
                        position <- start + 2
                        kind <- TokenKind.MinusMinusToken
                    elif next = '=' then
                        position <- start + 2
                        kind <- TokenKind.MinusEqualsToken
                    elif next = '>' then
                        position <- start + 2
                        kind <- TokenKind.MinusGreaterThanToken
                    else
                        kind <- TokenKind.MinusToken
                | '=' ->
                    if next = '=' then
                        position <- start + 2
                        kind <- TokenKind.EqualsEqualsToken
                    elif next = '>' then
                        position <- start + 2
                        kind <- TokenKind.EqualsGreaterThanToken
                    else
                        kind <- TokenKind.EqualsToken
                | '!' ->
                    if next = '=' then
                        position <- start + 2
                        kind <- TokenKind.ExclamationEqualsToken
                    else
                        kind <- TokenKind.ExclamationToken
                | '&' ->
                    if next = '&' then
                        position <- start + 2
                        kind <- TokenKind.AmpersandAmpersandToken
                    elif next = '=' then
                        position <- start + 2
                        kind <- TokenKind.AmpersandEqualsToken
                    else
                        kind <- TokenKind.AmpersandToken
                | '|' ->
                    if next = '|' then
                        position <- start + 2
                        kind <- TokenKind.BarBarToken
                    elif next = '=' then
                        position <- start + 2
                        kind <- TokenKind.BarEqualsToken
                    else
                        kind <- TokenKind.BarToken
                | '*' ->
                    if next = '=' then
                        position <- start + 2
                        kind <- TokenKind.AsteriskEqualsToken
                    else
                        kind <- TokenKind.AsteriskToken
                | '/' ->
                    if next = '=' then
                        position <- start + 2
                        kind <- TokenKind.SlashEqualsToken
                    else
                        kind <- TokenKind.SlashToken
                | '%' ->
                    if next = '=' then
                        position <- start + 2
                        kind <- TokenKind.PercentEqualsToken
                    else
                        kind <- TokenKind.PercentToken
                | '^' ->
                    if next = '=' then
                        position <- start + 2
                        kind <- TokenKind.CaretEqualsToken
                    else
                        kind <- TokenKind.CaretToken
                | '<' ->
                    if next = '<' then
                        position <- start + 2

                        if peek source sourceEnd start 2 = '=' then
                            position <- start + 3
                            kind <- TokenKind.LessThanLessThanEqualsToken
                        else
                            kind <- TokenKind.LessThanLessThanToken
                    elif next = '=' then
                        position <- start + 2
                        kind <- TokenKind.LessThanEqualsToken
                    else
                        kind <- TokenKind.LessThanToken
                | '>' ->
                    if next = '>' then
                        position <- start + 2

                        if peek source sourceEnd start 2 = '>' then
                            position <- start + 3

                            if peek source sourceEnd start 3 = '=' then
                                position <- start + 4
                                kind <- TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken
                            else
                                kind <- TokenKind.GreaterThanGreaterThanGreaterThanToken
                        elif peek source sourceEnd start 2 = '=' then
                            position <- start + 3
                            kind <- TokenKind.GreaterThanGreaterThanEqualsToken
                        else
                            kind <- TokenKind.GreaterThanGreaterThanToken
                    elif next = '=' then
                        position <- start + 2
                        kind <- TokenKind.GreaterThanEqualsToken
                    else
                        kind <- TokenKind.GreaterThanToken
                | _ ->
                    if Char.IsHighSurrogate ch && Char.IsLowSurrogate next then
                        position <- start + 2
        elif cls = CharClass.IdentifierStart then
            let mutable escaped = false
            position <- identifierEnd &window source sourceEnd position &escaped

            kind <-
                if escaped then
                    TokenKind.IdentifierToken
                else
                    let length = position - start

                    if keywordShaped ch length then
                        Keywords.kind source start length
                    else
                        TokenKind.IdentifierToken
        elif cls = CharClass.Digit then
            position <- numberEnd source sourceEnd start
            kind <- TokenKind.NumericLiteralToken
        elif cls = CharClass.SingleQuote then
            position <- quotedEnd source sourceEnd start '\'' false
            kind <- TokenKind.CharacterLiteralToken
        else
            let stringFinish =
                if cls = CharClass.At && start >= failedPrefixEnd then
                    stringEnd source sourceEnd start &kind &failedPrefixEnd
                else
                    start

            if stringFinish > start then
                position <- stringFinish
            else
                let identifierStart = if ch = '@' then start + 1 else start
                let mutable value = '\000'

                let finish =
                    if identifierStart < sourceEnd then
                        unicodeEscape source sourceEnd identifierStart &value
                    else
                        identifierStart

                if identifierStart < sourceEnd && isIdentifierStart source[identifierStart] then
                    let mutable escaped = true
                    position <- identifierEnd &window source sourceEnd identifierStart &escaped
                    kind <- TokenKind.IdentifierToken
                elif finish > identifierStart && isIdentifierStart value then
                    let mutable escaped = true
                    position <- identifierEnd &window source sourceEnd finish &escaped
                    kind <- TokenKind.IdentifierToken
                elif ch = '\\' then
                    position <- max position finish

                    kind <-
                        if finish > start then
                            TokenKind.BadToken
                        else
                            TokenKind.BackslashToken

        kind

    let private noSymbols: string array = [||]

    let private singleCharKinds: TokenKind array =
        let table = Array.create 128 TokenKind.None
        table[int '('] <- TokenKind.OpenParenToken
        table[int ')'] <- TokenKind.CloseParenToken
        table[int '['] <- TokenKind.OpenBracketToken
        table[int ']'] <- TokenKind.CloseBracketToken
        table[int '{'] <- TokenKind.OpenBraceToken
        table[int '}'] <- TokenKind.CloseBraceToken
        table[int ','] <- TokenKind.CommaToken
        table[int ';'] <- TokenKind.SemicolonToken
        table[int '~'] <- TokenKind.TildeToken
        table

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let private blankRun
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        sourceEnd
        (buffer: TokenBuffer)
        (position: byref<int>)
        =
        let start = position
        position <- skipWhitespaceInWindow &window source position sourceEnd
        buffer.AddLayoutTrivia(TriviaKind.WhitespaceTrivia, start, position - start)

    let inline private lineBreak
        (first: byref<char>)
        (sourceEnd: int)
        (buffer: TokenBuffer)
        (position: byref<int>)
        =
        let start = position
        let ch = Unsafe.Add(&first, start)
        position <- start + 1

        if ch = '\r' && position < sourceEnd && Unsafe.Add(&first, position) = '\n' then
            position <- position + 1

        buffer.AddLayoutTrivia(TriviaKind.EndOfLineTrivia, start, position - start)

    let inline private peekPtr (first: byref<char>) (sourceEnd: int) (position: int) (offset: int) =
        let index = position + offset

        if index < sourceEnd then
            Unsafe.Add(&first, index)
        else
            '\000'

    let inline private isDefinitelyTokenStart
        (first: byref<char>)
        (sourceStart: int)
        (sourceEnd: int)
        (pos: int)
        (ch: char)
        =
        if uint32 (int ch - 0x21) > 0x5du || ch = '#' then
            false
        elif ch = '/' then
            let next = peekPtr &first sourceEnd pos 1
            next <> '/' && next <> '*'
        elif ch = '<' || ch = '|' || ch = '=' then
            not (
                (pos = sourceStart || isNewLine (Unsafe.Add(&first, pos - 1)))
                && pos + 1 < sourceEnd
                && Unsafe.Add(&first, pos + 1) = ch
            )
        else
            true

    let inline private isUnconditionalTokenStart (ch: char) =
        uint32 (int ch - 0x21) <= 0x5du
        && ch <> '#'
        && ch <> '/'
        && ch <> '<'
        && ch <> '|'
        && ch <> '='

    let inline private leadingGap
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        (first: byref<char>)
        (sourceStart: int)
        (sourceEnd: int)
        (buffer: TokenBuffer)
        (position: byref<int>)
        (state: byref<DirectiveState>)
        =
        let mutable scanning = true

        while scanning && position < sourceEnd do
            let ch = Unsafe.Add(&first, position)

            if ch = ' ' || ch = '\t' then
                blankRun &window source sourceEnd buffer &position

                if
                    position >= sourceEnd
                    || isDefinitelyTokenStart
                        &first
                        sourceStart
                        sourceEnd
                        position
                        (Unsafe.Add(&first, position))
                then
                    scanning <- false
            elif ch = '\n' || ch = '\r' then
                lineBreak &first sourceEnd buffer &position
            elif isDefinitelyTokenStart &first sourceStart sourceEnd position ch then
                scanning <- false
            else
                triviaEnd &window source sourceStart sourceEnd buffer false true &position &state
                |> ignore

                scanning <- false

    let inline private trailingGap
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        (first: byref<char>)
        (sourceStart: int)
        (sourceEnd: int)
        (buffer: TokenBuffer)
        (position: byref<int>)
        (state: byref<DirectiveState>)
        =
        if position >= sourceEnd then
            false
        else
            let ch = Unsafe.Add(&first, position)

            if isUnconditionalTokenStart ch then
                false
            elif ch = ' ' || ch = '\t' then
                let nextPos = position + 1

                if
                    nextPos < sourceEnd
                    && (let next = Unsafe.Add(&first, nextPos) in
                        uint32 (int next - 0x21) <= 0x5du && next <> '#' && next <> '/')
                then
                    buffer.AddLayoutTrivia(TriviaKind.WhitespaceTrivia, position, 1)
                    position <- nextPos
                    false
                else
                    blankRun &window source sourceEnd buffer &position

                    if position >= sourceEnd then
                        false
                    else
                        let next = Unsafe.Add(&first, position)

                        if isDefinitelyTokenStart &first sourceStart sourceEnd position next then
                            false
                        elif next = '\n' || next = '\r' then
                            lineBreak &first sourceEnd buffer &position
                            true
                        else
                            triviaEnd
                                &window
                                source
                                sourceStart
                                sourceEnd
                                buffer
                                true
                                true
                                &position
                                &state
            elif ch = '\n' || ch = '\r' then
                lineBreak &first sourceEnd buffer &position
                true
            elif isDefinitelyTokenStart &first sourceStart sourceEnd position ch then
                false
            else
                triviaEnd &window source sourceStart sourceEnd buffer true true &position &state

    let inline private scanTokenKind
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        (first: byref<char>)
        (sourceEnd: int)
        (start: int)
        (position: byref<int>)
        (failedPrefixEnd: byref<int>)
        (scanning: byref<bool>)
        =
        if start = sourceEnd then
            scanning <- false
            TokenKind.EndOfFileToken
        else
            let ch = Unsafe.Add(&first, start)

            if ch > '\u007f' then
                tokenKind &window source sourceEnd &position &failedPrefixEnd
            else
                let cls = Unsafe.Add(&MemoryMarshal.GetArrayDataReference asciiClass, int ch)

                if cls = CharClass.IdentifierStart then
                    let mutable escaped = false
                    position <- identifierEnd &window source sourceEnd (start + 1) &escaped

                    if escaped then
                        TokenKind.IdentifierToken
                    else
                        let length = position - start

                        if keywordShapedAscii ch length then
                            Keywords.kind source start length
                        else
                            TokenKind.IdentifierToken
                else
                    let single =
                        Unsafe.Add(&MemoryMarshal.GetArrayDataReference singleCharKinds, int ch)

                    if single <> TokenKind.None then
                        position <- start + 1
                        single
                    else
                        let next = peekPtr &first sourceEnd start 1
                        let mutable kind = TokenKind.None
                        let mutable length = 1

                        match ch with
                        | '.' ->
                            if next = '.' then
                                kind <- TokenKind.DotDotToken
                                length <- 2
                            elif not (isDigit next) then
                                kind <- TokenKind.DotToken
                        | ':' ->
                            if next = ':' then
                                kind <- TokenKind.ColonColonToken
                                length <- 2
                            else
                                kind <- TokenKind.ColonToken
                        | '=' ->
                            if next = '=' then
                                kind <- TokenKind.EqualsEqualsToken
                                length <- 2
                            elif next = '>' then
                                kind <- TokenKind.EqualsGreaterThanToken
                                length <- 2
                            else
                                kind <- TokenKind.EqualsToken
                        | '!' ->
                            if next = '=' then
                                kind <- TokenKind.ExclamationEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.ExclamationToken
                        | '+' ->
                            if next = '+' then
                                kind <- TokenKind.PlusPlusToken
                                length <- 2
                            elif next = '=' then
                                kind <- TokenKind.PlusEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.PlusToken
                        | '-' ->
                            if next = '-' then
                                kind <- TokenKind.MinusMinusToken
                                length <- 2
                            elif next = '=' then
                                kind <- TokenKind.MinusEqualsToken
                                length <- 2
                            elif next = '>' then
                                kind <- TokenKind.MinusGreaterThanToken
                                length <- 2
                            else
                                kind <- TokenKind.MinusToken
                        | '&' ->
                            if next = '&' then
                                kind <- TokenKind.AmpersandAmpersandToken
                                length <- 2
                            elif next = '=' then
                                kind <- TokenKind.AmpersandEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.AmpersandToken
                        | '|' ->
                            if next = '|' then
                                kind <- TokenKind.BarBarToken
                                length <- 2
                            elif next = '=' then
                                kind <- TokenKind.BarEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.BarToken
                        | '*' ->
                            if next = '=' then
                                kind <- TokenKind.AsteriskEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.AsteriskToken
                        | '/' ->
                            if next = '=' then
                                kind <- TokenKind.SlashEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.SlashToken
                        | '%' ->
                            if next = '=' then
                                kind <- TokenKind.PercentEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.PercentToken
                        | '^' ->
                            if next = '=' then
                                kind <- TokenKind.CaretEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.CaretToken
                        | '?' ->
                            if next = '?' then
                                if peekPtr &first sourceEnd start 2 = '=' then
                                    kind <- TokenKind.QuestionQuestionEqualsToken
                                    length <- 3
                                else
                                    kind <- TokenKind.QuestionQuestionToken
                                    length <- 2
                            else
                                kind <- TokenKind.QuestionToken
                        | '<' ->
                            if next = '<' then
                                if peekPtr &first sourceEnd start 2 = '=' then
                                    kind <- TokenKind.LessThanLessThanEqualsToken
                                    length <- 3
                                else
                                    kind <- TokenKind.LessThanLessThanToken
                                    length <- 2
                            elif next = '=' then
                                kind <- TokenKind.LessThanEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.LessThanToken
                        | '>' ->
                            if next = '>' then
                                if peekPtr &first sourceEnd start 2 = '>' then
                                    if peekPtr &first sourceEnd start 3 = '=' then
                                        kind <-
                                            TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken

                                        length <- 4
                                    else
                                        kind <- TokenKind.GreaterThanGreaterThanGreaterThanToken

                                        length <- 3
                                elif peekPtr &first sourceEnd start 2 = '=' then
                                    kind <- TokenKind.GreaterThanGreaterThanEqualsToken
                                    length <- 3
                                else
                                    kind <- TokenKind.GreaterThanGreaterThanToken
                                    length <- 2
                            elif next = '=' then
                                kind <- TokenKind.GreaterThanEqualsToken
                                length <- 2
                            else
                                kind <- TokenKind.GreaterThanToken
                        | _ -> ()

                        if kind <> TokenKind.None then
                            position <- start + length
                            kind
                        else
                            tokenKind &window source sourceEnd &position &failedPrefixEnd

    let inline private isContextualWordFast (first: byref<char>) (start: int) (length: int) =
        let c0 = Unsafe.Add(&first, start)

        match length with
        | 3 -> c0 = 'v' && Keywords.load2 &first (start + 1) = Keywords.pack2 'a' 'r'
        | 4 -> c0 = 'f' && Keywords.load4 &first start = Keywords.pack4 'f' 'r' 'o' 'm'
        | 5 ->
            if c0 = 'a' then
                let w = Keywords.load4 &first (start + 1)
                w = Keywords.pack4 's' 'y' 'n' 'c' || w = Keywords.pack4 'w' 'a' 'i' 't'
            elif c0 = 'f' then
                Keywords.load4 &first (start + 1) = Keywords.pack4 'i' 'e' 'l' 'd'
            else
                false
        | _ -> false

    let inline private lexNextToken
        (triviaStart: int)
        (window: byref<MaskWindow>)
        (source: ReadOnlySpan<char>)
        (first: byref<char>)
        sourceStart
        sourceEnd
        (buffer: TokenBuffer)
        (position: byref<int>)
        (failedPrefixEnd: byref<int>)
        (scanning: byref<bool>)
        (scanLeading: byref<bool>)
        (directives: byref<DirectiveState>)
        =
        if scanLeading then
            leadingGap &window source &first sourceStart sourceEnd buffer &position &directives

        let leadingCount = buffer.NextTriviaIndex - triviaStart
        let start = position

        let kind =
            scanTokenKind &window source &first sourceEnd start &position &failedPrefixEnd &scanning

        let length = position - start

        if
            kind = TokenKind.IdentifierToken
            && uint32 (length - 3) <= 2u
            && isContextualWordFast &first start length
        then
            buffer.AddContextual start
        elif kind = TokenKind.BadToken then
            buffer.MarkBadToken()

        scanLeading <-
            trailingGap &window source &first sourceStart sourceEnd buffer &position &directives

        buffer.AddToken(
            kind,
            start,
            length,
            triviaStart,
            leadingCount,
            buffer.NextTriviaIndex - triviaStart - leadingCount
        )

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let private lexTokens
        (source: ReadOnlySpan<char>)
        sourceStart
        sourceEnd
        (buffer: TokenBuffer)
        (windowState: byref<MaskWindow>)
        (positionState: byref<int>)
        (failedPrefixEndState: byref<int>)
        (scanLeadingState: byref<bool>)
        (directivesState: byref<DirectiveState>)
        (firstTriviaStart: int)
        (stopAt: int)
        : bool =
        let first = &Unsafe.AsRef(&MemoryMarshal.GetReference source)
        let mutable window = windowState
        let mutable position = positionState
        let mutable failedPrefixEnd = failedPrefixEndState
        let mutable scanLeading = scanLeadingState
        let mutable directives = directivesState
        let mutable scanning = true
        let mutable triviaStart = firstTriviaStart

        while scanning && position < stopAt do
            lexNextToken
                triviaStart
                &window
                source
                &first
                sourceStart
                sourceEnd
                buffer
                &position
                &failedPrefixEnd
                &scanning
                &scanLeading
                &directives

            triviaStart <- buffer.NextTriviaIndex

        windowState <- window
        positionState <- position
        failedPrefixEndState <- failedPrefixEnd
        scanLeadingState <- scanLeading
        directivesState <- directives
        scanning

    let private lexSource
        (source: ReadOnlySpan<char>)
        sourceEnd
        sourceStart
        (symbols: string array)
        tokenHint
        triviaHint
        (buffer: TokenBuffer)
        =
        if uint32 sourceStart > uint32 sourceEnd || uint32 sourceEnd > uint32 source.Length then
            raise (ArgumentOutOfRangeException(nameof sourceStart))

        buffer.Reset()

        if tokenHint >= 0 then
            buffer.EnsureCapacity(tokenHint, triviaHint)
        else
            buffer.EnsureCapacity((sourceEnd - sourceStart) >>> 2)

        let mutable directives: DirectiveState = null

        if symbols.Length > 0 then
            buffer.HasSeededSymbols <- true
            directives <- buffer.AcquireDirectives()
            directives.Symbols.UnionWith symbols

        let mutable window = MaskWindow(Base = -64)
        let mutable position = sourceStart
        let mutable failedPrefixEnd = sourceStart
        let mutable scanLeading = true

        lexTokens
            source
            sourceStart
            sourceEnd
            buffer
            &window
            &position
            &failedPrefixEnd
            &scanLeading
            &directives
            buffer.NextTriviaIndex
            Int32.MaxValue
        |> ignore

    let inline private isStatefulDirectiveOrDisabled (kind: TriviaKind) =
        kind = TriviaKind.DisabledTextTrivia
        || (kind >= TriviaKind.IfDirectiveTrivia && kind <= TriviaKind.UndefDirectiveTrivia)
        || kind = TriviaKind.BadDirectiveTrivia
        || kind = TriviaKind.SkippedTokensTrivia
        || kind = TriviaKind.ConflictMarkerTrivia
        || kind = TriviaKind.ShebangDirectiveTrivia

    let private lowerBoundInt (span: Span<int>) (value: int) =
        let mutable lo = 0
        let mutable hi = span.Length

        while lo < hi do
            let mid = (lo + hi) >>> 1

            if span[mid] < value then lo <- mid + 1 else hi <- mid

        lo

    let private findTokenOwningTrivia (tokens: ReadOnlySpan<Token>) (triviaIdx: int) =
        let mutable lo = 0
        let mutable hi = tokens.Length - 1

        while lo < hi do
            let mid = (lo + hi) >>> 1
            let t = tokens[mid]

            if t.TriviaStart + t.LeadingCount + t.TrailingCount <= triviaIdx then
                lo <- mid + 1
            else
                hi <- mid

        lo

    let internal buildConditionalWindow (defaultBuf: TokenBuffer) : ConditionalLexWindow =
        let tokCount = defaultBuf.TokenCount
        let trivCount = defaultBuf.TriviaCount

        if
            tokCount < 8
            || trivCount = 0
            || defaultBuf.IsVerifyOnly
            || defaultBuf.HasMalformedTrivia
            || defaultBuf.HasBadToken
            || defaultBuf.HasSeededSymbols
            || defaultBuf.LastNonCommentTrivia < 0
        then
            Unchecked.defaultof<ConditionalLexWindow>
        else
            let tokens = defaultBuf.TokenSpan()
            let trivia = defaultBuf.TriviaSpan()
            let maxNonComment = min (trivCount - 1) defaultBuf.LastNonCommentTrivia
            let mutable firstCond = -1
            let mutable idx = 0

            while firstCond < 0 && idx <= maxNonComment do
                if isStatefulDirectiveOrDisabled trivia[idx].Kind then
                    firstCond <- idx
                else
                    idx <- idx + 1

            if firstCond < 0 then
                Unchecked.defaultof<ConditionalLexWindow>
            else
                let mutable lastCond = firstCond
                let mutable back = maxNonComment

                while back > firstCond && lastCond = firstCond do
                    if isStatefulDirectiveOrDisabled trivia[back].Kind then
                        lastCond <- back
                    else
                        back <- back - 1

                let firstOwner = findTokenOwningTrivia tokens firstCond
                let mutable prefixTok = firstOwner
                let mutable foundPrefixBoundary = false

                while prefixTok > 0 && not foundPrefixBoundary do
                    let prev = tokens[prefixTok - 1]
                    let prevEndTriv = prev.TriviaStart + prev.LeadingCount + prev.TrailingCount

                    if
                        prev.TrailingCount > 0
                        && prevEndTriv = tokens[prefixTok].TriviaStart
                        && trivia[prevEndTriv - 1].Kind = TriviaKind.EndOfLineTrivia
                    then
                        foundPrefixBoundary <- true
                    else
                        prefixTok <- prefixTok - 1

                let paSpan = CollectionsMarshal.AsSpan defaultBuf.ParenArrowsList
                let ipSpan = CollectionsMarshal.AsSpan defaultBuf.InterpolatedList
                let ctxSpan = CollectionsMarshal.AsSpan defaultBuf.ContextualOffsets

                let mutable prefixTriv = 0
                let mutable prefixScanStart = 0
                let mutable prefixLastComment = -1
                let mutable prefixLastNonComment = -1
                let mutable prefixLastArrow = -1
                let mutable prefixLastParenArrow = -1
                let mutable prefixPaCount = 0
                let mutable prefixIpCount = 0
                let mutable prefixCtxCount = 0

                if prefixTok > 0 then
                    prefixTriv <- tokens[prefixTok].TriviaStart
                    let lastLineBreak = trivia[prefixTriv - 1]
                    prefixScanStart <- lastLineBreak.Start + lastLineBreak.Length

                    if defaultBuf.LastCommentTrivia >= 0 then
                        if defaultBuf.LastCommentTrivia < prefixTriv then
                            prefixLastComment <- defaultBuf.LastCommentTrivia
                        else
                            let mutable c = prefixTriv - 1

                            while c >= 0 && prefixLastComment < 0 do
                                let k = trivia[c].Kind

                                if
                                    k >= TriviaKind.SingleLineCommentTrivia
                                    && k <= TriviaKind.MultiLineDocumentationCommentTrivia
                                then
                                    prefixLastComment <- c
                                else
                                    c <- c - 1

                    if defaultBuf.LastNonCommentTrivia >= 0 then
                        let mutable nc = min (prefixTriv - 1) defaultBuf.LastNonCommentTrivia

                        while nc >= 0 && prefixLastNonComment < 0 do
                            if trivia[nc].Kind > TriviaKind.MultiLineDocumentationCommentTrivia then
                                prefixLastNonComment <- nc
                            else
                                nc <- nc - 1

                    prefixPaCount <- lowerBoundInt paSpan (prefixTok - 1)

                    if prefixPaCount > 0 then
                        prefixLastParenArrow <- tokens[paSpan[prefixPaCount - 1] + 1].Start

                    if defaultBuf.LastArrowOffset >= 0 then
                        if defaultBuf.LastArrowOffset < prefixScanStart then
                            prefixLastArrow <- defaultBuf.LastArrowOffset
                        else
                            let mutable ti = prefixTok - 1

                            while ti >= 0 && prefixLastArrow < 0 do
                                if tokens[ti].Kind = TokenKind.EqualsGreaterThanToken then
                                    prefixLastArrow <- tokens[ti].Start
                                else
                                    ti <- ti - 1

                    prefixIpCount <- lowerBoundInt ipSpan prefixTok
                    prefixCtxCount <- lowerBoundInt ctxSpan prefixScanStart

                let lastOwner = findTokenOwningTrivia tokens lastCond
                let mutable suffixTok = lastOwner + 1
                let mutable foundSuffixBoundary = false

                while suffixTok < tokCount - 1 && not foundSuffixBoundary do
                    let cur = tokens[suffixTok]
                    let prev = tokens[suffixTok - 1]
                    let prevEndTriv = prev.TriviaStart + prev.LeadingCount + prev.TrailingCount

                    if
                        cur.Kind <> TokenKind.EqualsGreaterThanToken
                        && prev.TrailingCount > 0
                        && prevEndTriv = cur.TriviaStart
                        && trivia[prevEndTriv - 1].Kind = TriviaKind.EndOfLineTrivia
                    then
                        foundSuffixBoundary <- true
                    else
                        suffixTok <- suffixTok + 1

                let mutable suffixTriv = trivCount
                let mutable suffixScanStart = Int32.MaxValue
                let mutable suffixCtxStart = ctxSpan.Length
                let mutable suffixPaStart = paSpan.Length
                let mutable suffixIpStart = ipSpan.Length

                if foundSuffixBoundary && suffixTok < tokCount - 1 then
                    suffixTriv <- tokens[suffixTok].TriviaStart
                    let lastLineBreak = trivia[suffixTriv - 1]
                    let candidatePos = lastLineBreak.Start + lastLineBreak.Length

                    if candidatePos > prefixScanStart then
                        suffixScanStart <- candidatePos
                        suffixCtxStart <- lowerBoundInt ctxSpan suffixScanStart
                        suffixPaStart <- lowerBoundInt paSpan suffixTok
                        suffixIpStart <- lowerBoundInt ipSpan suffixTok
                    else
                        suffixTok <- tokCount

                let valid = prefixTok > 0 || suffixScanStart < Int32.MaxValue

                if not valid then
                    Unchecked.defaultof<ConditionalLexWindow>
                else
                    {
                        Valid = true
                        PrefixTokenCount = prefixTok
                        PrefixTriviaCount = prefixTriv
                        PrefixScanStart = prefixScanStart
                        PrefixLastComment = prefixLastComment
                        PrefixLastNonComment = prefixLastNonComment
                        PrefixLastArrowOffset = prefixLastArrow
                        PrefixLastParenArrowOffset = prefixLastParenArrow
                        PrefixParenArrowCount = prefixPaCount
                        PrefixInterpolatedCount = prefixIpCount
                        PrefixContextualCount = prefixCtxCount
                        SuffixTokenIndex = suffixTok
                        SuffixTriviaStart = suffixTriv
                        SuffixScanStart = suffixScanStart
                        SuffixContextualStart = suffixCtxStart
                        SuffixParenArrowStart = suffixPaStart
                        SuffixInterpolatedStart = suffixIpStart
                    }

    let internal lexSeededFromDefault
        (symbols: string array)
        (source: string)
        (defaultBuf: TokenBuffer)
        (win: inref<ConditionalLexWindow>)
        (buffer: TokenBuffer)
        : struct (int * int * int * int) =
        if Object.ReferenceEquals(defaultBuf, buffer) then
            invalidArg
                (nameof defaultBuf)
                "Seeded conditional lexing requires a separate default buffer."

        let span = source.AsSpan()
        let sourceEnd = span.Length
        let tokHint = defaultBuf.TokenCount + (defaultBuf.TokenCount >>> 3) + 64

        let trivHint =
            max (defaultBuf.TriviaCount + (defaultBuf.TriviaCount >>> 3) + 64) (tokHint + 64)

        if not win.Valid || symbols.Length = 0 then
            lexSource span sourceEnd 0 symbols tokHint trivHint buffer
            struct (0, 0, -1, -1)
        else
            buffer.Reset()
            buffer.EnsureCapacity(tokHint, trivHint)

            if win.PrefixTokenCount > 0 then
                buffer.CopyPrefixFrom(defaultBuf, &win)

            let mutable position = win.PrefixScanStart
            let mutable failedPrefixEnd = win.PrefixScanStart
            let mutable scanLeading = true
            let mutable window = MaskWindow(Base = -64)
            buffer.HasSeededSymbols <- true
            let mutable directives = buffer.AcquireDirectives()
            directives.Symbols.UnionWith symbols
            let mutable syncedTok = -1
            let mutable syncedTriv = -1

            let more =
                lexTokens
                    span
                    0
                    sourceEnd
                    buffer
                    &window
                    &position
                    &failedPrefixEnd
                    &scanLeading
                    &directives
                    buffer.NextTriviaIndex
                    win.SuffixScanStart

            if more then
                if
                    position = win.SuffixScanStart
                    && scanLeading
                    && position >= failedPrefixEnd
                    && directives.Frames.Count = 0
                    && directives.Active
                then
                    let struct (st, str) = buffer.AppendSuffixFrom(defaultBuf, &win)
                    syncedTok <- st
                    syncedTriv <- str
                else
                    lexTokens
                        span
                        0
                        sourceEnd
                        buffer
                        &window
                        &position
                        &failedPrefixEnd
                        &scanLeading
                        &directives
                        buffer.NextTriviaIndex
                        Int32.MaxValue
                    |> ignore

            struct (win.PrefixTokenCount, win.PrefixTriviaCount, syncedTok, syncedTriv)

    let lex (source: string) (buffer: TokenBuffer) : unit =
        lexSource (source.AsSpan()) source.Length 0 noSymbols -1 -1 buffer

    let lexHinted (tokenHint: int) (triviaHint: int) (source: string) (buffer: TokenBuffer) : unit =
        lexSource (source.AsSpan()) source.Length 0 noSymbols tokenHint triviaHint buffer

    let lexHintedSpan
        (tokenHint: int)
        (triviaHint: int)
        (source: ReadOnlySpan<char>)
        (buffer: TokenBuffer)
        : unit =
        lexSource source source.Length 0 noSymbols tokenHint triviaHint buffer

    let inline private tryFastVerifyGap
        (first: byref<char>)
        sourceEnd
        gapStart
        (nextPos: byref<int>)
        =
        if gapStart >= sourceEnd then
            nextPos <- sourceEnd
            true
        else
            let c0 = Unsafe.Add(&first, gapStart)

            if isUnconditionalTokenStart c0 then
                nextPos <- gapStart
                true
            elif
                c0 = ' '
                && gapStart + 1 < sourceEnd
                && (let c1 = Unsafe.Add(&first, gapStart + 1) in
                    uint32 (int c1 - 0x21) <= 0x5du && c1 <> '#' && c1 <> '/')
            then
                nextPos <- gapStart + 1
                true
            else
                let mutable p = gapStart
                let mutable looping = true

                while looping && p < sourceEnd do
                    let c = Unsafe.Add(&first, p)

                    if c = ' ' then
                        p <- p + 1

                        while p + 4 <= sourceEnd
                              && Unsafe.ReadUnaligned<uint64>(
                                  &Unsafe.As<char, byte>(&Unsafe.Add(&first, p))
                              )
                                  =
                                  0x0020002000200020UL do
                            p <- p + 4
                    elif c = '\n' || c = '\r' || c = '\t' then
                        p <- p + 1
                    else
                        looping <- false

                if
                    p >= sourceEnd
                    || isDefinitelyTokenStart &first 0 sourceEnd p (Unsafe.Add(&first, p))
                then
                    nextPos <- p
                    true
                else
                    false

    let lexVerifySpan
        (tokenHint: int)
        (triviaHint: int)
        (source: ReadOnlySpan<char>)
        (buffer: TokenBuffer)
        : unit =
        let sourceEnd = source.Length
        buffer.Reset()
        buffer.IsVerifyOnly <- true

        if tokenHint >= 0 then
            buffer.EnsureCapacity(tokenHint, triviaHint)
        else
            buffer.EnsureCapacity(sourceEnd >>> 2, 64)

        let first = &Unsafe.AsRef(&MemoryMarshal.GetReference source)
        let mutable position = 0
        let mutable failedPrefixEnd = 0
        let mutable scanning = true
        let mutable directives: DirectiveState = null
        let mutable window = MaskWindow(Base = -64)
        let mutable nextPos = 0

        let mutable scanLeading =
            if tryFastVerifyGap &first sourceEnd 0 &nextPos then
                position <- nextPos
                false
            else
                true

        while scanning do
            let triviaStart = buffer.NextTriviaIndex

            if scanLeading then
                leadingGap &window source &first 0 sourceEnd buffer &position &directives

            let leadingCount = buffer.NextTriviaIndex - triviaStart
            let start = position

            let kind =
                scanTokenKind
                    &window
                    source
                    &first
                    sourceEnd
                    start
                    &position
                    &failedPrefixEnd
                    &scanning

            let length = position - start

            if kind = TokenKind.BadToken then
                buffer.MarkBadToken()

            if not scanning then
                buffer.AddVerifyToken(kind, start, 0, triviaStart, leadingCount, 0)
            else
                let gapStart = position

                if tryFastVerifyGap &first sourceEnd gapStart &nextPos then
                    position <- nextPos
                    scanLeading <- false
                    buffer.AddVerifyToken(kind, start, length, triviaStart, leadingCount, 0)
                else
                    position <- gapStart

                    scanLeading <-
                        trailingGap &window source &first 0 sourceEnd buffer &position &directives

                    buffer.AddVerifyToken(
                        kind,
                        start,
                        length,
                        triviaStart,
                        leadingCount,
                        buffer.NextTriviaIndex - triviaStart - leadingCount
                    )

    let lexUnlessGenerated (source: string) (buffer: TokenBuffer) : bool =
        let span = source.AsSpan()
        let sourceEnd = span.Length
        buffer.Reset()
        let mutable position = 0
        let mutable directives: DirectiveState = null
        let mutable window = MaskWindow(Base = -64)

        triviaEnd &window span 0 sourceEnd buffer false true &position &directives
        |> ignore

        let firstLeadingCount = buffer.NextTriviaIndex
        let mutable isGenerated = false
        let mutable i = 0

        while not isGenerated && i < firstLeadingCount do
            let trivia = buffer.Trivia i

            if
                trivia.Kind = TriviaKind.SingleLineCommentTrivia
                || trivia.Kind = TriviaKind.MultiLineCommentTrivia
            then
                let text = span.Slice(trivia.Start, trivia.Length)

                if
                    text.Contains("<auto-generated".AsSpan(), StringComparison.Ordinal)
                    || text.Contains("<autogenerated".AsSpan(), StringComparison.Ordinal)
                then
                    isGenerated <- true

            i <- i + 1

        if isGenerated then
            true
        else
            buffer.EnsureCapacity(sourceEnd >>> 2)
            let mutable failedPrefixEnd = 0
            let mutable scanLeading = false

            lexTokens
                span
                0
                sourceEnd
                buffer
                &window
                &position
                &failedPrefixEnd
                &scanLeading
                &directives
                0
                Int32.MaxValue
            |> ignore

            false

    let lexWith (symbols: string array) (source: string) (buffer: TokenBuffer) : unit =
        lexSource (source.AsSpan()) source.Length 0 symbols -1 -1 buffer

    let lexWithHinted
        (symbols: string array)
        (tokenHint: int)
        (triviaHint: int)
        (source: string)
        (buffer: TokenBuffer)
        : unit =
        lexSource (source.AsSpan()) source.Length 0 symbols tokenHint triviaHint buffer

    let lexRange (source: string) start finish (buffer: TokenBuffer) : unit =
        lexSource (source.AsSpan()) finish start noSymbols -1 -1 buffer

    let private lexHole
        (source: ReadOnlySpan<char>)
        sourceEnd
        start
        opening
        stopAtQuote
        (buffer: TokenBuffer)
        =
        let finish = sourceEnd
        buffer.Reset()
        let mutable position = start
        let mutable failedPrefixEnd = start
        let mutable scanning = true
        let mutable scanLeading = true
        let mutable directives: DirectiveState = null
        let mutable window = MaskWindow(Base = -64)
        let mutable parens, brackets, braces = 0, 0, 0
        let mutable boundary = finish
        let mutable format = false
        let mutable found = false

        while scanning do
            let triviaStart = buffer.NextTriviaIndex

            if scanLeading then
                triviaEnd &window source start sourceEnd buffer false false &position &directives
                |> ignore

            let leadingCount = buffer.NextTriviaIndex - triviaStart
            let tokenStart = position

            let mutable kind =
                if position = finish || (stopAtQuote && source[position] = '"') then
                    boundary <- position
                    scanning <- false
                    TokenKind.EndOfFileToken
                else
                    tokenKind &window source sourceEnd &position &failedPrefixEnd

            let topLevel =
                (not opening || tokenStart > start) && parens = 0 && brackets = 0 && braces = 0

            if topLevel && kind = TokenKind.ColonColonToken then
                kind <- TokenKind.ColonToken
                position <- tokenStart + 1

            let length = position - tokenStart

            if kind = TokenKind.BadToken then
                buffer.MarkBadToken()

            if not opening || tokenStart > start then
                if
                    topLevel && (kind = TokenKind.CloseBraceToken || kind = TokenKind.ColonToken)
                then
                    boundary <- tokenStart
                    format <- kind = TokenKind.ColonToken
                    found <- true
                    scanning <- false
                else
                    match kind with
                    | TokenKind.OpenParenToken -> parens <- parens + 1
                    | TokenKind.CloseParenToken -> parens <- max 0 (parens - 1)
                    | TokenKind.OpenBraceToken -> braces <- braces + 1
                    | TokenKind.CloseBraceToken -> braces <- max 0 (braces - 1)
                    | TokenKind.OpenBracketToken -> brackets <- brackets + 1
                    | TokenKind.CloseBracketToken -> brackets <- max 0 (brackets - 1)
                    | _ -> ()

            scanLeading <-
                if found then
                    false
                else
                    triviaEnd &window source start sourceEnd buffer true false &position &directives

            buffer.AddToken
                {
                    Kind = kind
                    Start = tokenStart
                    Length = length
                    TriviaStart = triviaStart
                    LeadingCount = leadingCount
                    TrailingCount = buffer.NextTriviaIndex - triviaStart - leadingCount
                }

        if found then
            buffer.AddToken
                {
                    Kind = TokenKind.EndOfFileToken
                    Start = position
                    Length = 0
                    TriviaStart = buffer.NextTriviaIndex
                    LeadingCount = 0
                    TrailingCount = 0
                }

        struct (boundary, format)

    let lexInterpolationWithRecovery stopAtQuote (text: string) start finish (buffer: TokenBuffer) =
        lexHole (text.AsSpan()) finish start true stopAtQuote buffer

    let lexInterpolation (text: string) start finish (buffer: TokenBuffer) =
        lexInterpolationWithRecovery false text start finish buffer
