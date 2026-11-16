namespace Csff.Printer

open System
open System.Buffers
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open Csff.Lexer

type ElementKind =
    | Text = 0uy
    | StaticToken = 1uy
    | Line = 2uy
    | Tag = 3uy
    | Trim = 4uy
    | BreakParent = 5uy
    | LeadingComment = 6uy
    | TrailingComment = 7uy
    | BeginRegion = 8uy
    | EndRegion = 9uy
    | GeneratedText = 10uy
    | Shared = 11uy
    | Reindent = 12uy

type Tag =
    | StartGroup = 0
    | EndGroup = 1
    | StartIndent = 2
    | EndIndent = 3
    | StartForceFlat = 4
    | EndForceFlat = 5
    | StartIfBreak = 6
    | Else = 7
    | EndIfBreak = 8
    | StartAlwaysFits = 9
    | EndAlwaysFits = 10
    | StartConditionalGroup = 11
    | EndConditionalGroup = 12
    | StartAlternative = 13
    | EndAlternative = 14

type LineKind =
    | Normal = 0
    | Soft = 1
    | Hard = 2
    | Literal = 3
    | IndentedLiteral = 4

module ElementFlags =
    [<Literal>]
    let Multiline = 1uy

    [<Literal>]
    let NoExpand = 2uy

    [<Literal>]
    let Directive = 4uy

    [<Literal>]
    let Break = 8uy

    [<Literal>]
    let Squash = 16uy

    [<Literal>]
    let SkipBreakIfFirst = 32uy

    [<Literal>]
    let NoTrim = 64uy

    [<Literal>]
    let SquashBlank = 128uy

module ElementFacts =
    [<Literal>]
    let FlatValid = 1uy

    [<Literal>]
    let FlatNonWhitespace = 2uy

    [<Literal>]
    let Code = 4uy

    [<Literal>]
    let TailUnknown = 255uy

[<Struct; StructLayout(LayoutKind.Sequential)>]
type FormatElement =
    {
        Kind: ElementKind
        Flags: byte
        Tail: byte
        mutable Facts: byte
        mutable Width: uint32
        mutable A: int32
        B: int32
    }

module internal FormatElementHeader =
    let private ofElement (e: FormatElement) =
        let mutable copy = e
        Unsafe.As<FormatElement, uint32>(&copy)

    let fastCodeText =
        ofElement
            {
                Kind = ElementKind.Text
                Flags = 0uy
                Tail = 0uy
                Facts =
                    ElementFacts.FlatValid ||| ElementFacts.FlatNonWhitespace ||| ElementFacts.Code
                Width = 0u
                A = 0
                B = 0
            }

    let fastCodeStatic =
        ofElement
            {
                Kind = ElementKind.StaticToken
                Flags = 0uy
                Tail = 0uy
                Facts =
                    ElementFacts.FlatValid ||| ElementFacts.FlatNonWhitespace ||| ElementFacts.Code
                Width = 0u
                A = 0
                B = 0
            }

    let fastSpaceStatic =
        ofElement
            {
                Kind = ElementKind.StaticToken
                Flags = 0uy
                Tail = 1uy
                Facts = ElementFacts.FlatValid
                Width = 0u
                A = 0
                B = 0
            }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let inline read (e: inref<FormatElement>) =
        Unsafe.As<FormatElement, uint32>(&Unsafe.AsRef(&e))

module PrintedWidth =
    let character (c: char) =
        let n = int c

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

    let measure (text: ReadOnlySpan<char>) =
        if text.Length >= 16 && Text.Ascii.IsValid(text) then
            uint32 text.Length
        else
            let mutable width = uint32 text.Length

            for i = 0 to text.Length - 1 do
                if text[i] >= '\u1100' then
                    width <- width + character text[i] - 1u

            width

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let measureLastLine (text: ReadOnlySpan<char>) : struct (uint32 * bool) =
        if text.Length <= 16 then
            let mutable i = text.Length - 1
            let mutable extra = 0u
            let mutable multiline = false

            while i >= 0 && not multiline do
                let c = text[i]

                if uint32 (int c - 0x0e) >= 0x10f2u then
                    if c >= '\u1100' then
                        extra <- extra + character c - 1u
                    elif c = '\n' || c = '\r' then
                        multiline <- true

                if not multiline then
                    i <- i - 1

            struct (uint32 (text.Length - 1 - i) + extra, multiline)
        else
            let lastNewline = text.LastIndexOfAny('\r', '\n')

            if lastNewline < 0 then
                struct (measure text, false)
            else
                struct (measure (text.Slice(lastNewline + 1)), true)

    let lastLine (text: ReadOnlySpan<char>) =
        let struct (width, _) = measureLastLine text
        width

    let firstLine (text: ReadOnlySpan<char>) =
        let fromStart = text.IndexOfAny('\r', '\n')

        if fromStart < 0 then
            measure text
        else
            measure (text.Slice(0, fromStart))

module internal Utf8Text =
    let scalarAt (bytes: ReadOnlySpan<byte>) : struct (int * int) =
        if bytes.IsEmpty then
            struct (0, 0)
        else
            let mutable rune = Unchecked.defaultof<Text.Rune>
            let mutable size = 0

            if Text.Rune.DecodeFromUtf8(bytes, &rune, &size) = OperationStatus.Done then
                struct (rune.Value, size)
            else
                struct (0xfffd, max size 1)

    let lastScalar (bytes: ReadOnlySpan<byte>) : struct (int * int) =
        if bytes.IsEmpty then
            struct (0, 0)
        else
            let mutable rune = Unchecked.defaultof<Text.Rune>
            let mutable size = 0

            if Text.Rune.DecodeLastFromUtf8(bytes, &rune, &size) = OperationStatus.Done then
                struct (rune.Value, size)
            else
                struct (0xfffd, max size 1)

    let scalarWidth (scalar: int) =
        if scalar > 0xffff then
            2u
        else
            PrintedWidth.character (char scalar)

    let character (bytes: ReadOnlySpan<byte>) =
        let struct (scalar, _) = scalarAt bytes
        scalarWidth scalar

    let measure (bytes: ReadOnlySpan<byte>) =
        if bytes.Length >= 16 && Text.Ascii.IsValid(bytes) then
            uint32 bytes.Length
        else
            let mutable width = 0u
            let mutable i = 0

            while i < bytes.Length do
                if bytes[i] < 0x80uy then
                    width <- width + 1u
                    i <- i + 1
                else
                    let struct (scalar, size) = scalarAt (bytes.Slice(i))
                    width <- width + scalarWidth scalar
                    i <- i + size

            width

    let measureLastLine (bytes: ReadOnlySpan<byte>) : struct (uint32 * bool) =
        let lastNewline = bytes.LastIndexOfAny('\r'B, '\n'B)

        if lastNewline < 0 then
            struct (measure bytes, false)
        else
            struct (measure (bytes.Slice(lastNewline + 1)), true)

    let lastLine (bytes: ReadOnlySpan<byte>) =
        let struct (width, _) = measureLastLine bytes
        width

    let firstLine (bytes: ReadOnlySpan<byte>) =
        let fromStart = bytes.IndexOfAny('\r'B, '\n'B)

        if fromStart < 0 then
            measure bytes
        else
            measure (bytes.Slice(0, fromStart))

    let private leadingUnit (bytes: ReadOnlySpan<byte>) =
        let struct (scalar, _) = scalarAt bytes
        if scalar > 0xffff then '\ud800' else char scalar

    let isNewLine (bytes: ReadOnlySpan<byte>) =
        Lexer.Classify.newLine (leadingUnit bytes)

    let isWhitespace (bytes: ReadOnlySpan<byte>) =
        Lexer.Classify.whitespace (leadingUnit bytes)

    let isIdentifierStart (bytes: ReadOnlySpan<byte>) =
        Lexer.Classify.identifierStart (leadingUnit bytes)

    let isIdentifierPart (bytes: ReadOnlySpan<byte>) =
        Lexer.Classify.identifierPart (leadingUnit bytes)

type StaticToken =
    | Space = 0
    | Semicolon = 1
    | OpenBrace = 2
    | CloseBrace = 3
    | OpenParen = 4
    | CloseParen = 5
    | OpenBracket = 6
    | CloseBracket = 7
    | Comma = 8
    | Dot = 9
    | Colon = 10
    | Equals = 11
    | Public = 12
    | Private = 13
    | Protected = 14
    | Internal = 15
    | Static = 16
    | Class = 17
    | Void = 18
    | Return = 19

module internal StaticText =
    let values =
        [|
            " "
            ";"
            "{"
            "}"
            "("
            ")"
            "["
            "]"
            ","
            "."
            ":"
            "="
            "public"
            "private"
            "protected"
            "internal"
            "static"
            "class"
            "void"
            "return"
        |]

    let utf8Bytes = values |> Array.map (fun s -> Text.Encoding.UTF8.GetBytes s)

    let singleBytes =
        values |> Array.map (fun s -> if s.Length = 1 then byte s[0] else 0uy)

module internal TextFacts =
    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let derive (text: ReadOnlySpan<char>, directive: bool) : struct (byte * byte) =
        let len = text.Length

        if len > 0 && uint32 (int text[len - 1] - 0x21) <= 0x5du then
            struct (0uy,
                    if directive then
                        ElementFacts.FlatValid ||| ElementFacts.FlatNonWhitespace
                    else
                        ElementFacts.FlatValid
                        ||| ElementFacts.FlatNonWhitespace
                        ||| ElementFacts.Code)
        else
            let mutable trailing = len

            while trailing > 0 && (text[trailing - 1] = ' ' || text[trailing - 1] = '\t') do
                trailing <- trailing - 1

            let tail = len - trailing

            let code =
                trailing > 0
                && (uint32 (int text[trailing - 1] - 0x21) <= 0x5du
                    || not (text.Slice(0, trailing).IsWhiteSpace()))

            struct ((if tail >= int ElementFacts.TailUnknown then
                         ElementFacts.TailUnknown
                     else
                         byte tail),
                    ElementFacts.FlatValid
                    ||| (if tail < len then ElementFacts.FlatNonWhitespace else 0uy)
                    ||| (if code && not directive then ElementFacts.Code else 0uy))

    let tokens =
        StaticText.values |> Array.map (fun text -> derive (text.AsSpan(), false))

[<Sealed>]
type DocumentBuffer(?initialCapacity: int) =
    let mutable elements =
        match initialCapacity with
        | Some capacity ->
            let cap = max 16 capacity

            if cap <= PoolArray.maxPooledLength then
                SharedBuckets<FormatElement>.Rent cap
            else
                GC.AllocateUninitializedArray<FormatElement> cap
        | None -> Array.empty<FormatElement>

    let mutable generated = Array.empty<char>
    let mutable generatedCount = 0
    let mutable count = 0
    let mutable targetCapacity = 0
    let stats = DocumentStats.enabled
    let mutable textElements = 0
    let mutable groupCount = 0
    let mutable suppressedBreakDepth = 0
    let mutable forceFlatDepth = 0
    let mutable alwaysFitsDepth = 0
    let mutable conditionalDepth = 0
    let mutable conditionalBreakCounts = Array.empty<int>
    let mutable hasShared = false
    let mutable copiedGroups = Array.empty<int>
    let mutable copiedGroupStamps = Array.empty<int>
    let mutable copiedGroupStamp = 0
    let mutable sourceForAscii: string = null
    let mutable sourceIsAscii = false
    let mutable disposed = false

    member internal _.Storage =
        ObjectDisposedException.ThrowIf(disposed, typeof<DocumentBuffer>)
        elements

    member internal _.Generated = generated
    member internal _.GeneratedCount = generatedCount

    member internal _.SourceForAscii
        with get () = sourceForAscii
        and set value = sourceForAscii <- value

    member internal _.SourceIsAscii
        with get () = sourceIsAscii
        and set value = sourceIsAscii <- value

    member _.Count = count

    member internal _.TakeTextElements() =
        let taken = textElements
        textElements <- 0
        taken

    member _.GroupCount = groupCount
    member internal _.SuppressedBreakDepth = suppressedBreakDepth

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal _.ConditionalBreakCount() =
        if conditionalDepth > 0 && conditionalDepth < conditionalBreakCounts.Length then
            conditionalBreakCounts[conditionalDepth]
        else
            0

    member _.Elements =
        ObjectDisposedException.ThrowIf(disposed, typeof<DocumentBuffer>)
        ReadOnlySpan<FormatElement>(elements, 0, count)

    member _.Reset() =
        ObjectDisposedException.ThrowIf(disposed, typeof<DocumentBuffer>)
        count <- 0
        targetCapacity <- 0
        textElements <- 0
        generatedCount <- 0
        groupCount <- 0
        suppressedBreakDepth <- 0
        forceFlatDepth <- 0
        alwaysFitsDepth <- 0
        conditionalDepth <- 0
        hasShared <- false
        sourceForAscii <- null
        sourceIsAscii <- false

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.NewGroupId() =
        let id = groupCount
        groupCount <- groupCount + 1
        id

    member private _.Grow(required: int) =
        ObjectDisposedException.ThrowIf(disposed, typeof<DocumentBuffer>)

        let effective =
            if required > 8192 then
                max required targetCapacity
            else
                required

        let maxPooled = PoolArray.maxPooledLength
        let oldLen = elements.Length
        let nextCapacity = max effective (max 1024 (oldLen * 2))

        if count = 0 && oldLen > 0 && oldLen <= maxPooled then
            SharedBuckets<FormatElement>.Return(elements)
            elements <- Array.empty

        let grown =
            if nextCapacity <= maxPooled then
                SharedBuckets<FormatElement>.Rent(nextCapacity)
            elif required <= targetCapacity && effective > maxPooled then
                GC.AllocateUninitializedArray<FormatElement>(effective)
            else
                let step =
                    if oldLen >= 65536 then
                        oldLen + (oldLen >>> 1)
                    else
                        max 1024 (oldLen * 2)

                GC.AllocateUninitializedArray<FormatElement>(max effective step)

        if count > 0 then
            elements.AsSpan(0, count).CopyTo(grown.AsSpan())

        if elements.Length > 0 && elements.Length <= maxPooled then
            SharedBuckets<FormatElement>.Return(elements)

        elements <- grown

    member internal this.EnsureCapacity(required: int) =
        ObjectDisposedException.ThrowIf(disposed, typeof<DocumentBuffer>)
        targetCapacity <- max targetCapacity required
        let initial = if required > 65536 then 8192 else required

        if initial > elements.Length then
            this.Grow(initial)
        elif required > elements.Length && required <= PoolArray.maxPooledLength then
            this.Grow(required)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.Add(element: FormatElement) =
        if count = elements.Length then
            this.Grow(count + 1)

        elements[count] <- element
        count <- count + 1

    member internal _.Truncate(length: int) = count <- length

    member internal _.Remove(index: int) =
        for i = index to count - 2 do
            elements.[i] <- elements.[i + 1]

        count <- count - 1

        if hasShared then
            for i = index to count - 1 do
                let element = elements[i]

                if element.Kind = ElementKind.Shared then
                    if element.A > index then
                        elements[i] <- { element with A = element.A - 1 }
                    elif element.A + element.B > index then
                        elements[i] <- { element with B = element.B - 1 }

    member internal this.Insert(index: int, element: FormatElement) =
        if element.Kind = ElementKind.Shared then
            hasShared <- true

        this.Add element

        for i = count - 1 downto index + 1 do
            elements.[i] <- elements.[i - 1]

        elements.[index] <- element

        if hasShared then
            for i = index + 1 to count - 1 do
                let existing = elements[i]

                if existing.Kind = ElementKind.Shared then
                    if existing.A >= index then
                        elements[i] <- { existing with A = existing.A + 1 }
                    elif existing.A + existing.B > index then
                        elements[i] <- { existing with B = existing.B + 1 }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddText(source: string, start: int, length: int) =
        this.AddText(source, start, length, 0uy)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddText(source: string, start: int, length: int, flags: byte) =
        if stats then
            textElements <- textElements + 1

        let text = source.AsSpan(start, length)
        let mutable bits = flags

        let width =
            if sourceIsAscii && Object.ReferenceEquals(sourceForAscii, source) then
                let lastNewline = text.LastIndexOfAny('\r', '\n')

                if lastNewline < 0 then
                    uint32 length
                else
                    bits <- bits ||| ElementFlags.Multiline
                    uint32 (length - 1 - lastNewline)
            else
                let struct (w, multiline) = PrintedWidth.measureLastLine text

                if multiline then
                    bits <- bits ||| ElementFlags.Multiline

                w

        let struct (tail, facts) =
            TextFacts.derive (text, bits &&& ElementFlags.Directive <> 0uy)

        this.Add
            {
                Kind = ElementKind.Text
                Flags = bits
                Tail = tail
                Facts = facts
                Width = width
                A = start
                B = length
            }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal this.AddCodeToken(start: int, length: int, width: uint32) =
        if stats then
            textElements <- textElements + 1

        this.Add
            {
                Kind = ElementKind.Text
                Flags = 0uy
                Tail = 0uy
                Facts =
                    ElementFacts.FlatValid ||| ElementFacts.FlatNonWhitespace ||| ElementFacts.Code
                Width = width
                A = start
                B = length
            }

    member this.AddGeneratedText(text: ReadOnlySpan<char>) =
        ObjectDisposedException.ThrowIf(disposed, typeof<DocumentBuffer>)

        if generatedCount + text.Length > generated.Length then
            let maxPooled = PoolArray.maxPooledLength
            let target = max (generatedCount + text.Length) (max 1024 (generated.Length * 2))

            if generatedCount = 0 && generated.Length > 0 && generated.Length <= maxPooled then
                SharedBuckets<char>.Return(generated)
                generated <- Array.empty

            let grown =
                if target <= maxPooled then
                    SharedBuckets<char>.Rent target
                else
                    GC.AllocateUninitializedArray<char> target

            if generatedCount > 0 then
                generated.AsSpan(0, generatedCount).CopyTo(grown.AsSpan())

            if generated.Length > 0 && generated.Length <= maxPooled then
                SharedBuckets<char>.Return(generated)

            generated <- grown

        text.CopyTo(generated.AsSpan(generatedCount))
        let struct (width, multiline) = PrintedWidth.measureLastLine text

        let struct (tail, facts) = TextFacts.derive (text, false)

        this.Add
            {
                Kind = ElementKind.GeneratedText
                Flags = if multiline then ElementFlags.Multiline else 0uy
                Tail = tail
                Facts = facts
                Width = width
                A = generatedCount
                B = text.Length
            }

        generatedCount <- generatedCount + text.Length

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal this.AddSpace() =
        this.Add
            {
                Kind = ElementKind.StaticToken
                Flags = 0uy
                Tail = 1uy
                Facts = ElementFacts.FlatValid
                Width = 1u
                A = int StaticToken.Space
                B = 0
            }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddToken(token: StaticToken) =
        let index = int token

        if uint32 index >= uint32 StaticText.values.Length then
            invalidArg (nameof token) "Unknown static token."

        let struct (tail, facts) = TextFacts.tokens[index]

        this.Add
            {
                Kind = ElementKind.StaticToken
                Flags = 0uy
                Tail = tail
                Facts = facts
                Width = uint32 StaticText.values[index].Length
                A = index
                B = 0
            }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddLine(kind: LineKind) = this.AddLine(kind, 0uy)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddLine(kind: LineKind, flags: byte) =
        if
            conditionalDepth > 0
            && alwaysFitsDepth = 0
            && (int kind >= int LineKind.Literal || (kind = LineKind.Hard && forceFlatDepth = 0))
        then
            conditionalBreakCounts[conditionalDepth] <- conditionalBreakCounts[conditionalDepth] + 1

        this.Add
            {
                Kind = ElementKind.Line
                Flags = flags
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = int kind
                B = 0
            }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddTag(tag: Tag) = this.AddTag(tag, -1, 0uy)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddTag(tag: Tag, payload: int) = this.AddTag(tag, payload, 0uy)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.AddTag(tag: Tag, payload: int, flags: byte) =
        match tag with
        | Tag.StartForceFlat ->
            forceFlatDepth <- forceFlatDepth + 1
            suppressedBreakDepth <- suppressedBreakDepth + 1
        | Tag.EndForceFlat ->
            forceFlatDepth <- forceFlatDepth - 1
            suppressedBreakDepth <- suppressedBreakDepth - 1
        | Tag.StartAlwaysFits ->
            alwaysFitsDepth <- alwaysFitsDepth + 1
            suppressedBreakDepth <- suppressedBreakDepth + 1
        | Tag.EndAlwaysFits ->
            alwaysFitsDepth <- alwaysFitsDepth - 1
            suppressedBreakDepth <- suppressedBreakDepth - 1
        | Tag.StartConditionalGroup ->
            conditionalDepth <- conditionalDepth + 1

            if conditionalDepth >= conditionalBreakCounts.Length then
                Array.Resize(&conditionalBreakCounts, max 16 (conditionalDepth * 2))
        | Tag.EndConditionalGroup -> conditionalDepth <- conditionalDepth - 1
        | Tag.StartGroup when
            conditionalDepth > 0
            && alwaysFitsDepth = 0
            && forceFlatDepth = 0
            && flags &&& ElementFlags.Break <> 0uy
            ->
            conditionalBreakCounts[conditionalDepth] <- conditionalBreakCounts[conditionalDepth] + 1
        | _ -> ()

        this.Add
            {
                Kind = ElementKind.Tag
                Flags = flags
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = payload
                B = int tag
            }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.StartGroup() = this.StartGroup 0uy

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.StartGroup(flags: byte) =
        let id = this.NewGroupId()
        this.AddTag(Tag.StartGroup, id, flags)
        id

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.EndGroup() = this.AddTag(Tag.EndGroup)

    member internal this.AddShared(start: int, length: int) =
        if start < 0 || length < 0 || start + length > count then
            invalidArg (nameof start) "Shared ranges must precede their use."

        hasShared <- true

        this.Add
            {
                Kind = ElementKind.Shared
                Flags = 0uy
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = start
                B = length
            }

    member private _.TrackControlElement(element: FormatElement) =
        if element.Kind = ElementKind.Tag then
            match enum<Tag> element.B with
            | Tag.StartForceFlat ->
                forceFlatDepth <- forceFlatDepth + 1
                suppressedBreakDepth <- suppressedBreakDepth + 1
            | Tag.EndForceFlat ->
                forceFlatDepth <- forceFlatDepth - 1
                suppressedBreakDepth <- suppressedBreakDepth - 1
            | Tag.StartAlwaysFits ->
                alwaysFitsDepth <- alwaysFitsDepth + 1
                suppressedBreakDepth <- suppressedBreakDepth + 1
            | Tag.EndAlwaysFits ->
                alwaysFitsDepth <- alwaysFitsDepth - 1
                suppressedBreakDepth <- suppressedBreakDepth - 1
            | Tag.StartConditionalGroup ->
                conditionalDepth <- conditionalDepth + 1

                if conditionalDepth >= conditionalBreakCounts.Length then
                    Array.Resize(&conditionalBreakCounts, max 16 (conditionalDepth * 2))
            | Tag.EndConditionalGroup -> conditionalDepth <- conditionalDepth - 1
            | Tag.StartGroup when
                conditionalDepth > 0
                && alwaysFitsDepth = 0
                && forceFlatDepth = 0
                && element.Flags &&& ElementFlags.Break <> 0uy
                ->
                conditionalBreakCounts[conditionalDepth] <-
                    conditionalBreakCounts[conditionalDepth] + 1
            | _ -> ()
        elif conditionalDepth > 0 && alwaysFitsDepth = 0 then
            if
                element.Kind = ElementKind.Line
                && (element.A >= int LineKind.Literal
                    || (element.A = int LineKind.Hard && forceFlatDepth = 0))
            then
                conditionalBreakCounts[conditionalDepth] <-
                    conditionalBreakCounts[conditionalDepth] + 1
            elif element.Kind = ElementKind.BreakParent && forceFlatDepth = 0 then
                conditionalBreakCounts[conditionalDepth] <-
                    conditionalBreakCounts[conditionalDepth] + 1
            elif element.Kind = ElementKind.Reindent then
                conditionalBreakCounts[conditionalDepth] <-
                    conditionalBreakCounts[conditionalDepth] + 1

    member internal this.Append(document: DocumentBuffer, start: int, length: int) =
        if
            document.GroupCount = 0
            && document.Generated.Length = 0
            && not document.HasShared
        then
            ObjectDisposedException.ThrowIf(disposed, typeof<DocumentBuffer>)

            if count + length > elements.Length then
                this.Grow(count + length)

            document.Storage.AsSpan(start, length).CopyTo(elements.AsSpan(count))
            count <- count + length

            if conditionalDepth > 0 then
                for i = start to start + length - 1 do
                    let element = document.Storage[i]

                    if element.Kind >= ElementKind.Line then
                        this.TrackControlElement element
        else
            this.AppendGroups(document, start, length)

    member private this.AppendGroups(document: DocumentBuffer, start: int, length: int) =
        let offset = count - start
        let finish = start + length
        hasShared <- hasShared || document.HasShared

        if copiedGroups.Length < document.GroupCount then
            let capacity = max document.GroupCount (max 16 (copiedGroups.Length * 2))
            Array.Resize(&copiedGroups, capacity)
            Array.Resize(&copiedGroupStamps, capacity)

        copiedGroupStamp <- copiedGroupStamp + 1

        if copiedGroupStamp = Int32.MaxValue then
            Array.Clear copiedGroupStamps
            copiedGroupStamp <- 1

        let copyStamp = copiedGroupStamp

        for i = start to finish - 1 do
            let element = document.Storage[i]

            if
                element.Kind = ElementKind.Tag
                && (element.B = int Tag.StartGroup || element.B = int Tag.StartConditionalGroup)
            then
                copiedGroups[element.A] <- this.NewGroupId()
                copiedGroupStamps[element.A] <- copyStamp

        for i = start to finish - 1 do
            let element = document.Storage[i]

            if element.Kind >= ElementKind.Line then
                this.TrackControlElement element

            if
                element.Kind = ElementKind.Tag
                && (element.B = int Tag.StartGroup || element.B = int Tag.StartConditionalGroup)
            then
                this.Add
                    { element with
                        A = copiedGroups[element.A]
                    }
            elif
                element.Kind = ElementKind.Tag
                && element.B = int Tag.StartIfBreak
                && element.A >= 0
                && element.A < copiedGroupStamps.Length
                && copiedGroupStamps[element.A] = copyStamp
            then
                this.Add
                    { element with
                        A = copiedGroups[element.A]
                    }
            elif element.Kind = ElementKind.GeneratedText then
                this.AddGeneratedText(document.Generated.AsSpan(element.A, element.B))
            elif element.Kind = ElementKind.Shared then
                let adjustedA =
                    if element.A >= start && element.A + element.B <= finish then
                        element.A + offset
                    else
                        element.A

                this.Add { element with A = adjustedA }
            else
                this.Add element

    member internal _.HasShared = hasShared

    member this.AddTrim() =
        this.Add
            {
                Kind = ElementKind.Trim
                Flags = 0uy
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = 0
                B = 0
            }

    member this.AddReindent() =
        if conditionalDepth > 0 && alwaysFitsDepth = 0 then
            conditionalBreakCounts[conditionalDepth] <- conditionalBreakCounts[conditionalDepth] + 1

        this.Add
            {
                Kind = ElementKind.Reindent
                Flags = 0uy
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = 0
                B = 0
            }

    member this.AddBreakParent() =
        if conditionalDepth > 0 && alwaysFitsDepth = 0 && forceFlatDepth = 0 then
            conditionalBreakCounts[conditionalDepth] <- conditionalBreakCounts[conditionalDepth] + 1

        this.Add
            {
                Kind = ElementKind.BreakParent
                Flags = 0uy
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = 0
                B = 0
            }

    member this.AddComment
        (source: string, start: int, length: int, leading: bool, multiline: bool)
        =
        this.AddComment(source, start, length, leading, multiline, false)

    member this.AddComment
        (source: string, start: int, length: int, leading: bool, multiline: bool, conditional: bool)
        =
        let _ = source

        this.Add
            {
                Kind =
                    (if leading then
                         ElementKind.LeadingComment
                     else
                         ElementKind.TrailingComment)
                Flags =
                    (if multiline then ElementFlags.Multiline else 0uy)
                    ||| (if conditional then ElementFlags.Directive else 0uy)
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = start
                B = length
            }

    member this.AddRegion(source: string, start: int, length: int, isEnd: bool) =
        let _ = source

        this.Add
            {
                Kind =
                    (if isEnd then
                         ElementKind.EndRegion
                     else
                         ElementKind.BeginRegion)
                Flags = ElementFlags.Directive
                Tail = 0uy
                Facts = 0uy
                Width = 0u
                A = start
                B = length
            }

    member _.Dispose() =
        if not disposed then
            let maxPooled = PoolArray.maxPooledLength

            if elements.Length > 0 && elements.Length <= maxPooled then
                SharedBuckets<FormatElement>.Return(elements)

            if generated.Length > 0 && generated.Length <= maxPooled then
                SharedBuckets<char>.Return(generated)

            generated <- Array.empty
            elements <- Array.empty
            count <- 0
            disposed <- true

    interface IDisposable with
        member this.Dispose() = this.Dispose()
