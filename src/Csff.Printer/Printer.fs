namespace Csff.Printer

open System
open System.Buffers
open System.Runtime.CompilerServices
open System.Text
open System.Runtime.InteropServices
open System.Runtime.Intrinsics
open System.Runtime.Intrinsics.Arm
open Csff.Lexer

module VerificationLimit =
    [<Literal>]
    let Characters = 67108864

    [<Literal>]
    let Message =
        "source or formatted output exceeds the 64 MiB syntax verification limit"

type VerificationLimitException(message: string) =
    inherit InvalidOperationException(message)

type EndOfLine =
    | Lf = 0
    | CrLf = 1
    | Cr = 2

[<Struct>]
type PrinterOptions =
    {
        Width: int
        IndentSize: int
        UseTabs: bool
        EndOfLine: EndOfLine
        TrimInitialLines: bool
    }

    static member Default =
        {
            Width = 100
            IndentSize = 4
            UseTabs = false
            EndOfLine = EndOfLine.Lf
            TrimInitialLines = false
        }

[<Struct>]
type TransformationWitness =
    {
        SortedUsings: bool
        SortedModifiers: bool
        ChangedTrailingCommas: bool
        ReindentedRawStrings: bool
        SymbolSets: string array array
        AllConfigurationsComplete: bool
    }

    static member None =
        {
            SortedUsings = false
            SortedModifiers = false
            ChangedTrailingCommas = false
            ReindentedRawStrings = false
            SymbolSets = null
            AllConfigurationsComplete = false
        }

    static member Searched =
        {
            SortedUsings = true
            SortedModifiers = true
            ChangedTrailingCommas = true
            ReindentedRawStrings = true
            SymbolSets = null
            AllConfigurationsComplete = false
        }

module private Boundary =
    [<Literal>]
    let Code = 1uy

    [<Literal>]
    let Hard = 2uy

    [<Literal>]
    let SkipBefore = 4uy

    [<Literal>]
    let SkipAfter = 8uy

    [<Literal>]
    let NestedSkip = 16uy

    [<Literal>]
    let NestedSkipAfterHard = 32uy

    [<Literal>]
    let Literal = 64uy

    [<Literal>]
    let All = 63uy

    let inline has (flag: byte) (effect: byte) = effect &&& flag <> 0uy

    let inline combine (left: byte, right: byte) : byte =
        if has Hard left then
            left
            ||| (right &&& (Code ||| Hard ||| NestedSkipAfterHard ||| Literal))
            ||| (if has Code left then 0uy else right &&& SkipBefore)
            ||| (if has NestedSkip right then NestedSkipAfterHard else 0uy)
        elif has Code left then
            left
            ||| (right
                 &&& (Code ||| Hard ||| SkipAfter ||| NestedSkip ||| NestedSkipAfterHard ||| Literal))
            ||| ((right &&& SkipBefore) <<< 1)
        else
            left ||| right

module private FlatFlags =
    [<Literal>]
    let Valid = 1uy

    [<Literal>]
    let NonWhitespace = 2uy

    [<Literal>]
    let Code = 4uy

    [<Literal>]
    let Complete = 7uy

module private TagShape =
    [<Literal>]
    let Count = 15u

    [<Literal>]
    let OpeningBits = 0x2A55u

    [<Literal>]
    let OpeningFlatValidBits = 0x0255u

[<Struct>]
type private Preparation =
    {
        Start: int
        mutable Else: int
        mutable Effect: byte
        mutable FlatWidth: int
        mutable FlatTail: int
        mutable FlatFlags: byte
        EnclosingGroup: int
    }

[<Struct>]
type private Range =
    {
        mutable Next: int
        mutable Finish: int
        mutable Indent: int
        mutable Flat: bool
        mutable Force: bool
    }

[<Sealed>]
type Printer() =
    static let sourceLineTerminators = SearchValues.Create("\r\n\u0085\u2028\u2029")

    static let asciiToUtf16Action =
        SpanAction<char, byte array>(fun dst buf ->
            let mutable written = 0

            Ascii.ToUtf16(ReadOnlySpan<byte>(buf, 0, dst.Length), dst, &written) |> ignore)

    static let matchesUtf16 (utf8: ReadOnlySpan<byte>) (utf16: ReadOnlySpan<char>) =
        if utf8.Length < utf16.Length then
            false
        else
            let mutable b = utf8
            let mutable c = utf16
            let mutable same = true

            while same && not b.IsEmpty && not c.IsEmpty do
                let asciiLen = b.IndexOfAnyInRange(0x80uy, 0xffuy)

                if asciiLen < 0 then
                    same <- b.Length = c.Length && Ascii.Equals(b, c)
                    b <- ReadOnlySpan<byte>.Empty
                    c <- ReadOnlySpan<char>.Empty
                else
                    if asciiLen > 0 then
                        if
                            asciiLen > c.Length
                            || not (Ascii.Equals(b.Slice(0, asciiLen), c.Slice(0, asciiLen)))
                        then
                            same <- false
                        else
                            b <- b.Slice asciiLen
                            c <- c.Slice asciiLen

                    if same then
                        let mutable r1 = Unchecked.defaultof<Rune>
                        let mutable r2 = Unchecked.defaultof<Rune>
                        let mutable bConsumed = 0
                        let mutable cConsumed = 0

                        if
                            Rune.DecodeFromUtf8(b, &r1, &bConsumed) = OperationStatus.Done
                            && Rune.DecodeFromUtf16(c, &r2, &cConsumed) = OperationStatus.Done
                            && r1 = r2
                        then
                            b <- b.Slice bConsumed
                            c <- c.Slice cConsumed
                        else
                            same <- false

            same && b.IsEmpty && c.IsEmpty

    let mutable output = Array.empty<byte>
    let mutable outputCount = 0
    let mutable outputUtf16Count = 0
    let mutable pendingHighEnd = -1
    let mutable pendingHigh = '\000'
    let pair = Array.zeroCreate<char> 2
    let mutable writeLimit = 0L
    let mutable disposed = false
    let mutable cachedText: string = null
    let mutable source = ""
    let mutable asciiInput = false
    let mutable generated = Array.empty<char>
    let mutable elements = Array.empty<FormatElement>
    let mutable options = PrinterOptions.Default
    let mutable modes = Array.empty<byte>
    let mutable trialModes = Array.empty<byte>
    let mutable stamps = Array.empty<int>
    let mutable groupParents = Array.empty<int>
    let mutable stamp = 0
    let mutable preparation = Array.empty<Preparation>
    let mutable commands = Array.empty<Range>
    let mutable commandCount = 0
    let mutable trials = Array.empty<Range>
    let mutable regions = Array.empty<int>
    let mutable regionCount = 0
    let mutable column = 0
    let mutable outputLineStart = 0
    let mutable layoutLineEnd = -1
    let mutable sourceLineStart = 0
    let mutable sourceLineFinish = -1
    let mutable sourceLineIndent = 0
    let mutable trailingWidth = 0
    let mutable lineHasCode = false
    let mutable pendingComment = false
    let mutable lineHasDirective = false
    let mutable lineHasLineComment = false
    let mutable pendingSourceIndent = false
    let mutable remeasure = false
    let mutable sharedWork = 0
    let mutable fitCalls = 0
    let mutable fitWork = 0
    let mutable sourceLineScans = 0
    let sourceMappings = ResizeArray<struct (int * int * int)>()

    member val internal TrackSourceMappings = false with get, set
    member val MaxOutputLength = Array.MaxLength with get, set
    member internal _.SourceMappings = sourceMappings

    member private _.TrimSourceMappings() =
        while sourceMappings.Count > 0
              && (let struct (start, _, _) = sourceMappings[sourceMappings.Count - 1] in
                  start >= outputUtf16Count) do
            sourceMappings.RemoveAt(sourceMappings.Count - 1)

        if sourceMappings.Count > 0 then
            let index = sourceMappings.Count - 1
            let struct (start, first, length) = sourceMappings[index]

            sourceMappings[index] <- struct (start, first, min length (outputUtf16Count - start))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.Text(element: FormatElement) : ReadOnlySpan<char> =
        match element.Kind with
        | ElementKind.GeneratedText -> ReadOnlySpan<char>(generated, element.A, element.B)
        | ElementKind.StaticToken -> StaticText.values[element.A].AsSpan()
        | _ -> source.AsSpan(element.A, element.B)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ScanTail(element: FormatElement) =
        let text = this.Text element
        let mutable trailing = text.Length

        while trailing > 0 && (text[trailing - 1] = ' ' || text[trailing - 1] = '\t') do
            trailing <- trailing - 1

        text.Length - trailing

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.TextTail(element: FormatElement) =
        if element.Tail <> ElementFacts.TailUnknown then
            int element.Tail
        else
            this.ScanTail element

    member private _.LeadingWidth(text: ReadOnlySpan<char>) =
        let mutable i = 0
        let mutable width = 0

        while i < text.Length && (text[i] = ' ' || text[i] = '\t') do
            width <- width + (if text[i] = '\t' then options.IndentSize else 1)
            i <- i + 1

        width

    member private this.SourceIndent(start: int) =
        if start < sourceLineStart || start > sourceLineFinish then
            sourceLineScans <- sourceLineScans + 1
            sourceLineStart <- source.AsSpan(0, start).LastIndexOfAny(sourceLineTerminators) + 1
            let finish = source.AsSpan(start).IndexOfAny(sourceLineTerminators)
            sourceLineFinish <- if finish < 0 then source.Length else start + finish
            let mutable position = sourceLineStart
            sourceLineIndent <- 0

            while position < source.Length
                  && (if position < start then
                          Lexer.Classify.whitespace source[position]
                      else
                          source[position] = ' ' || source[position] = '\t') do
                let ch = source[position]

                sourceLineIndent <-
                    sourceLineIndent
                    + (if ch = '\t' then options.IndentSize
                       elif ch = '\ufeff' then 0
                       else int (PrintedWidth.character ch))

                position <- position + 1

        sourceLineIndent

    member private _.OutputIndent() =
        let line =
            ReadOnlySpan<byte>(output, outputLineStart, outputCount - outputLineStart)

        let mutable i = 0
        let mutable width = 0

        while i < line.Length && (line[i] = 32uy || line[i] = 9uy) do
            width <- width + (if line[i] = 9uy then options.IndentSize else 1)
            i <- i + 1

        width

    member private _.CommentDirective(e: FormatElement, line: ReadOnlySpan<char>) =
        let text = line.TrimStart()

        if e.Flags &&& ElementFlags.Directive = 0uy || text.Length = 0 || text[0] <> '#' then
            0
        else
            let text = text.Slice(1).TrimStart()
            let mutable finish = 0

            while finish < text.Length && Char.IsLetter text[finish] do
                finish <- finish + 1

            let keyword = text.Slice(0, finish)

            if
                finish < text.Length
                && (Char.IsLetterOrDigit text[finish] || text[finish] = '_')
            then
                0
            elif keyword.SequenceEqual("if".AsSpan()) then
                1
            elif keyword.SequenceEqual("elif".AsSpan()) then
                2
            elif keyword.SequenceEqual("else".AsSpan()) then
                3
            elif keyword.SequenceEqual("endif".AsSpan()) then
                4
            elif
                keyword.SequenceEqual("pragma".AsSpan())
                || keyword.SequenceEqual("region".AsSpan())
                || keyword.SequenceEqual("endregion".AsSpan())
                || keyword.SequenceEqual("define".AsSpan())
                || keyword.SequenceEqual("undef".AsSpan())
                || keyword.SequenceEqual("warning".AsSpan())
                || keyword.SequenceEqual("error".AsSpan())
                || keyword.SequenceEqual("nullable".AsSpan())
                || keyword.SequenceEqual("line".AsSpan())
                || keyword.SequenceEqual("r".AsSpan())
                || keyword.SequenceEqual("load".AsSpan())
            then
                5
            else
                0

    member private this.CommentAlternate(e: FormatElement, text: ReadOnlySpan<char>) =
        let mutable start = 0
        let mutable finish = 0
        let mutable alternate = false

        while finish < text.Length do
            if text[finish] = '\r' || text[finish] = '\n' then
                let directive = this.CommentDirective(e, text.Slice(start, finish - start))
                alternate <- alternate || directive = 2 || directive = 3
                start <- finish + 1

            finish <- finish + 1

        alternate

    member private this.FailOutputLimit() =
        cachedText <- null
        source <- ""
        elements <- Array.empty
        generated <- Array.empty

        if this.MaxOutputLength < Array.MaxLength then
            raise (VerificationLimitException VerificationLimit.Message)
        else
            invalidOp "Formatted output exceeds the formatter's buffer limit."

    member private this.OutputCeiling() =
        if this.MaxOutputLength < Array.MaxLength then
            min
                (int64 Array.MaxLength)
                (3L * (max 0L (int64 this.MaxOutputLength) + int64 source.Length + 65536L))
        else
            int64 Array.MaxLength

    member private this.ReserveOutput(required: int64) =
        if required > int64 Array.MaxLength then
            this.FailOutputLimit()

        let required = int required

        if required > output.Length then
            let step =
                if output.Length >= 65536 then
                    int64 output.Length + (int64 output.Length >>> 1)
                else
                    int64 output.Length * 2L

            let maxPooled = PoolArray.maxPooledLength

            let target =
                int (min (int64 Array.MaxLength) (max (int64 required) (max 1024L step)))

            if outputCount = 0 && output.Length > 0 && output.Length <= maxPooled then
                SharedBuckets<byte>.Return output
                output <- Array.empty

            let grown =
                if target <= maxPooled then
                    SharedBuckets<byte>.Rent target
                else
                    GC.AllocateUninitializedArray<byte> target

            if outputCount > 0 then
                output.AsSpan(0, outputCount).CopyTo(grown.AsSpan())

            if output.Length > 0 && output.Length <= maxPooled then
                SharedBuckets<byte>.Return(output)

            output <- grown

        writeLimit <- min (this.OutputCeiling()) (int64 output.Length)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ExtendOutput(required: int64) =
        if required > this.OutputCeiling() then
            this.FailOutputLimit()

        this.ReserveOutput required

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.EnsureOutput(required: int64) =
        if required > writeLimit then
            this.ExtendOutput required

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.CopyOutput(text: ReadOnlySpan<char>, start: int) =
        let mutable written = 0
        Ascii.FromUtf16(text, output.AsSpan(start, text.Length), &written) |> ignore

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.AppendCrLayoutSeparator() =
        this.EnsureOutput(int64 outputCount + 1L)
        output[outputCount] <- 10uy
        outputCount <- outputCount + 1
        outputUtf16Count <- outputUtf16Count + 1
        outputLineStart <- outputCount
        layoutLineEnd <- -1

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.RecordSourceMapping(text: ReadOnlySpan<char>) =
        let mutable first = 0

        if MemoryExtensions.Overlaps(source.AsSpan(), text, &first) then
            sourceMappings.Add(struct (outputUtf16Count, first, text.Length))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.UpdateMultilineStart(start: int) =
        let written = ReadOnlySpan<byte>(output, start, outputCount - start)
        outputLineStart <- start + written.LastIndexOfAny(13uy, 10uy) + 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.Append(text: ReadOnlySpan<char>, width: int, multiline: bool, tail: int) =
        if
            layoutLineEnd = outputCount
            && options.EndOfLine = EndOfLine.Cr
            && not text.IsEmpty
            && text[0] = '\n'
        then
            this.AppendCrLayoutSeparator()

        this.EnsureOutput(
            int64 outputCount
            + (if asciiInput then
                   int64 text.Length
               else
                   3L * int64 text.Length)
        )

        if this.TrackSourceMappings && not text.IsEmpty then
            this.RecordSourceMapping text

        let start = outputCount

        if asciiInput || Ascii.IsValid text then
            match text.Length with
            | 0 -> ()
            | 1 -> output[start] <- byte text[0]
            | 2 ->
                let destination = output.AsSpan(start, 2)
                destination[0] <- byte text[0]
                destination[1] <- byte text[1]
            | 3 ->
                let destination = output.AsSpan(start, 3)
                destination[0] <- byte text[0]
                destination[1] <- byte text[1]
                destination[2] <- byte text[2]
            | 4 ->
                let destination = output.AsSpan(start, 4)
                destination[0] <- byte text[0]
                destination[1] <- byte text[1]
                destination[2] <- byte text[2]
                destination[3] <- byte text[3]
            | _ -> this.CopyOutput(text, start)

            outputCount <- start + text.Length
        else
            this.AppendTranscoded text

        outputUtf16Count <- outputUtf16Count + text.Length
        column <- if multiline then width else column + width

        if multiline then
            this.UpdateMultilineStart start

        if tail = text.Length then
            trailingWidth <- trailingWidth + tail
        else
            trailingWidth <- tail

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.AppendTranscoded(text: ReadOnlySpan<char>) =
        let mutable at = outputCount
        let mutable rest = text

        if pendingHighEnd = at && not rest.IsEmpty && Char.IsLowSurrogate rest[0] then
            pair[0] <- pendingHigh
            pair[1] <- rest[0]

            at <-
                at - 3
                + Encoding.UTF8.GetBytes(ReadOnlySpan<char>(pair, 0, 2), output.AsSpan(at - 3))

            rest <- rest.Slice(1)

        at <- at + Encoding.UTF8.GetBytes(rest, output.AsSpan(at))
        outputCount <- at

        if not text.IsEmpty && Char.IsHighSurrogate text[text.Length - 1] then
            pendingHigh <- text[text.Length - 1]
            pendingHighEnd <- at

    member private this.Append(text: ReadOnlySpan<char>) =
        let struct (width, multiline) = PrintedWidth.measureLastLine text

        let mutable trailing = text.Length

        while trailing > 0 && (text[trailing - 1] = ' ' || text[trailing - 1] = '\t') do
            trailing <- trailing - 1

        this.Append(text, int width, multiline, text.Length - trailing)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.Space() =
        this.EnsureOutput(int64 outputCount + 1L)
        output[outputCount] <- 32uy
        outputCount <- outputCount + 1
        outputUtf16Count <- outputUtf16Count + 1
        column <- column + 1
        trailingWidth <- trailingWidth + 1

    member private this.AppendComment(text: ReadOnlySpan<char>) =
        let mutable start = 0
        let mutable nl = text.IndexOfAny('\r', '\n')

        while nl >= 0 do
            let finish = start + nl
            this.Append(text.Slice(start, nl).TrimEnd())
            this.Append(text.Slice(finish, 1))
            start <- finish + 1
            nl <- text.Slice(start).IndexOfAny('\r', '\n')

        this.Append(text.Slice(start).TrimEnd())

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.FillOutput(start: int, count: int, value: byte) =
        let destination = output.AsSpan(start, count)

        if count > 64 then
            destination.Fill(value)
        else
            let runs = MemoryMarshal.Cast<byte, uint64>(destination)

            if runs.Length > 0 then
                let pattern = uint64 value * 0x0101010101010101UL

                for i = 0 to runs.Length - 1 do
                    runs[i] <- pattern

            let mutable i = runs.Length * 8

            while i < count do
                destination[i] <- value
                i <- i + 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.Indent(width: int) =
        if width > 0 then
            let outArr = output
            let start = outputCount

            if
                not options.UseTabs
                && width <= 32
                && int64 start + 32L <= writeLimit
                && start + 32 <= outArr.Length
            then
                let v = Vector128.Create 32uy
                v.StoreUnsafe(&outArr[start])

                if width > 16 then
                    v.StoreUnsafe(&outArr[start + 16])

                outputCount <- start + width
                outputUtf16Count <- outputUtf16Count + width
                column <- column + width
                trailingWidth <- trailingWidth + width
            else
                let tabs = if options.UseTabs then width / options.IndentSize else 0
                let spaces = width - tabs * options.IndentSize
                let count = tabs + spaces

                this.EnsureOutput(int64 start + int64 count)

                if tabs > 0 then
                    this.FillOutput(outputCount, tabs, 9uy)

                if spaces > 0 then
                    this.FillOutput(outputCount + tabs, spaces, 32uy)

                outputCount <- outputCount + count
                outputUtf16Count <- outputUtf16Count + count
                column <- column + width
                trailingWidth <- trailingWidth + width

    member private this.Trim() =
        if outputCount > 0 && output[outputCount - 1] <= 32uy then
            let initialCount = outputCount

            while outputCount > 0
                  && (output[outputCount - 1] = 32uy || output[outputCount - 1] = 9uy) do
                outputCount <- outputCount - 1
                outputUtf16Count <- outputUtf16Count - 1

            if this.TrackSourceMappings && outputCount < initialCount then
                this.TrimSourceMappings()

        column <- column - trailingWidth
        trailingWidth <- 0

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.OwnsLine(e: FormatElement) =
        if e.Kind <> ElementKind.Text || e.Flags &&& ElementFlags.Directive = 0uy then
            false
        else
            let mutable i = e.A

            while i > 0 && (source[i - 1] = ' ' || source[i - 1] = '\t') do
                i <- i - 1

            i = 0 || sourceLineTerminators.Contains source[i - 1]

    member private _.EndsWithDelimitedComment() =
        outputCount >= 2
        && output[outputCount - 1] = 47uy
        && output[outputCount - 2] = 42uy

    member private _.AtLineStart() =
        let mutable i = outputCount

        while i > outputLineStart && (output[i - 1] = 32uy || output[i - 1] = 9uy) do
            i <- i - 1

        i = outputLineStart

    member private this.Newline(indent: int, trim: bool) =
        if trim then
            this.Trim()

        if
            int64 outputUtf16Count >= int64 this.MaxOutputLength
            && not options.TrimInitialLines
            && outputCount > 0
            && output[outputCount - 1] > 32uy
            && output[outputCount - 1] < 127uy
        then
            this.FailOutputLimit()

        this.EnsureOutput(int64 outputCount + 2L)

        if options.EndOfLine = EndOfLine.CrLf then
            output[outputCount] <- 13uy
            outputCount <- outputCount + 1
            outputUtf16Count <- outputUtf16Count + 1

        output[outputCount] <- if options.EndOfLine = EndOfLine.Cr then 13uy else 10uy
        outputCount <- outputCount + 1
        outputUtf16Count <- outputUtf16Count + 1
        outputLineStart <- outputCount
        layoutLineEnd <- outputCount
        column <- 0
        trailingWidth <- 0
        lineHasCode <- false
        lineHasDirective <- false
        lineHasLineComment <- false
        this.Indent(indent * options.IndentSize)
        pendingComment <- false
        pendingSourceIndent <- false
        remeasure <- true

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.NewlinesAtEndSlow() =
        let outArr = output
        let mutable i = outputCount - 1
        let mutable count = 0
        let mutable scanning = true

        while scanning && count < 2 && i >= 0 do
            while i >= 7 && Unsafe.ReadUnaligned<uint64>(&outArr[i - 7]) = 0x2020202020202020UL do
                i <- i - 8

            if i >= 0 then
                let b = outArr[i]

                if b = 10uy then
                    count <- count + 1

                    if i > 0 && outArr[i - 1] = 13uy then
                        i <- i - 1

                    i <- i - 1
                elif b = 13uy then
                    count <- count + 1
                    i <- i - 1
                elif b = 32uy || b = 9uy then
                    i <- i - 1
                elif b = 0x85uy && i >= 1 && outArr[i - 1] = 0xC2uy then
                    count <- count + 1
                    i <- i - 2
                elif
                    (b = 0xA8uy || b = 0xA9uy)
                    && i >= 2
                    && outArr[i - 1] = 0x80uy
                    && outArr[i - 2] = 0xE2uy
                then
                    count <- count + 1
                    i <- i - 3
                else
                    scanning <- false

        count

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.NewlinesAtEnd() =
        let outArr = output
        let cnt = outputCount

        if cnt = 0 then
            0
        else
            let last = outArr[cnt - 1]

            if last > 32uy && last < 127uy then
                0
            else
                this.NewlinesAtEndSlow()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    static member private InvalidDocument(message: string) =
        raise (ArgumentException(message, "document"))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.EnsurePrepareBuffers(groupCount: int) =
        if preparation.Length = 0 then
            preparation <- Array.zeroCreate 256
            commands <- Array.zeroCreate 256
            trials <- Array.zeroCreate 256
            regions <- Array.zeroCreate 64

        if modes.Length < groupCount then
            PoolArray.grow &modes 0 groupCount
            PoolArray.grow &trialModes 0 groupCount
            PoolArray.grow &stamps 0 groupCount
            PoolArray.grow &groupParents 0 groupCount
            stamp <- 0
            Array.Clear(stamps, 0, stamps.Length)

    member private this.Prepare(count: int, groupCount: int, hasShared: bool) =
        if preparation.Length = 0 || modes.Length < groupCount then
            this.EnsurePrepareBuffers groupCount

        let modesArr = modes
        let parentsArr = groupParents
        Array.Clear(modesArr, 0, groupCount)

        let elems = Span<FormatElement>(elements, 0, count)
        let mutable prep = preparation
        let mutable depth = 0
        let mutable alwaysFits = 0
        let mutable topStart = 0
        let mutable topElse = -1
        let mutable topEffect = 0uy
        let mutable topFlatWidth = 0
        let mutable topFlatTail = 0
        let mutable topFlatFlags = 0uy
        let mutable topEnclosing = -1

        for i = 0 to elems.Length - 1 do
            let e = &elems[i]
            let hdr = FormatElementHeader.read &e

            if
                hdr = FormatElementHeader.fastCodeText
                || hdr = FormatElementHeader.fastCodeStatic
            then
                if depth > 0 then
                    topEffect <- topEffect ||| Boundary.Code

                    if topFlatFlags <> 0uy then
                        topFlatWidth <- topFlatWidth + int e.Width
                        topFlatTail <- 0
                        topFlatFlags <- FlatFlags.Complete
            elif hdr = FormatElementHeader.fastSpaceStatic then
                if depth > 0 && topFlatFlags <> 0uy then
                    topFlatWidth <- topFlatWidth + int e.Width
                    topFlatTail <- topFlatTail + 1
            elif not hasShared && e.Kind = ElementKind.Line then
                let lineKind = e.A

                if lineKind = int LineKind.Soft then
                    ()
                elif lineKind = int LineKind.Normal then
                    if depth > 0 && topFlatFlags <> 0uy then
                        topFlatWidth <- topFlatWidth + 1
                        topFlatTail <- topFlatTail + 1
                elif lineKind >= int LineKind.Hard then
                    if depth > 0 then
                        topFlatFlags <- 0uy

                        if alwaysFits = 0 then
                            let eff =
                                if
                                    lineKind = int LineKind.Hard
                                    && e.Flags &&& ElementFlags.SkipBreakIfFirst <> 0uy
                                then
                                    Boundary.SkipBefore
                                elif lineKind >= int LineKind.Literal then
                                    Boundary.Hard ||| Boundary.Literal
                                else
                                    Boundary.Hard

                            topEffect <- Boundary.combine (topEffect, eff)
                elif depth > 0 then
                    topFlatFlags <- 0uy
            elif
                byte e.Kind < byte ElementKind.Line
                && e.Flags = 0uy
                && e.Tail <> ElementFacts.TailUnknown
            then
                if depth > 0 then
                    topEffect <- topEffect ||| ((e.Facts >>> 2) &&& Boundary.Code)

                    if topFlatFlags <> 0uy then
                        topFlatWidth <- topFlatWidth + int e.Width

                        topFlatTail <-
                            if e.Facts &&& FlatFlags.NonWhitespace <> 0uy then
                                int e.Tail
                            else
                                topFlatTail + int e.Tail

                        topFlatFlags <- topFlatFlags ||| e.Facts
            else

                let mutable effect = 0uy
                let mutable flatWidth = 0
                let mutable flatTail = 0
                let mutable flatFlags = 0uy
                let mutable emit = true

                if e.Kind = ElementKind.Tag then
                    let tag = enum<Tag> e.B
                    e.Width <- uint32 -1
                    let ub = uint32 e.B

                    if ub < TagShape.Count && ((TagShape.OpeningBits >>> e.B) &&& 1u <> 0u) then
                        let enclosing = if depth > 0 then topEnclosing else -1

                        if tag = Tag.StartGroup || tag = Tag.StartConditionalGroup then
                            if uint32 e.A >= uint32 groupCount || modesArr[e.A] <> 0uy then
                                Printer.InvalidDocument "Group IDs must be unique and reserved."

                            modesArr[e.A] <- 3uy
                            parentsArr[e.A] <- enclosing
                            e.Facts <- 0uy

                        if tag = Tag.StartIfBreak then
                            if
                                e.A >= 0
                                && (enclosing < 0
                                    || elems[enclosing].B <> int Tag.StartGroup
                                    || elems[enclosing].A <> e.A)
                                && e.A < groupCount
                                && modesArr[e.A] <> 0uy
                            then
                                let mutable parent = parentsArr[e.A]

                                while parent >= 0 && (elems[parent].Facts &&& 128uy = 0uy) do
                                    let parentId = elems[parent].A
                                    elems[parent].Facts <- elems[parent].Facts ||| 128uy
                                    let parentEnd = int elems[parent].Width

                                    if parentEnd >= 0 then
                                        elems[parentEnd].A <- -1

                                    parent <-
                                        if uint32 parentId < uint32 groupCount then
                                            parentsArr[parentId]
                                        else
                                            -1

                        if
                            tag = Tag.StartAlternative
                            && (depth = 0 || elems[topStart].B <> int Tag.StartConditionalGroup)
                        then
                            Printer.InvalidDocument "An alternative needs a conditional group."

                        if depth > 0 then
                            prep[depth - 1] <-
                                {
                                    Start = topStart
                                    Else = topElse
                                    Effect = topEffect
                                    FlatWidth = topFlatWidth
                                    FlatTail = topFlatTail
                                    FlatFlags = topFlatFlags
                                    EnclosingGroup = topEnclosing
                                }

                        topStart <- i
                        topElse <- -1
                        topEffect <- 0uy
                        topFlatWidth <- 0
                        topFlatTail <- 0
                        topFlatFlags <- byte ((TagShape.OpeningFlatValidBits >>> e.B) &&& 1u)

                        topEnclosing <-
                            if tag = Tag.StartGroup || tag = Tag.StartConditionalGroup then
                                i
                            else
                                enclosing

                        depth <- depth + 1

                        if depth = prep.Length then
                            Array.Resize(&preparation, prep.Length * 2)
                            prep <- preparation

                        if tag = Tag.StartAlwaysFits then
                            alwaysFits <- alwaysFits + 1

                        emit <- false
                    elif e.B = int Tag.Else then
                        if depth = 0 || elems[topStart].B <> int Tag.StartIfBreak then
                            Printer.InvalidDocument "Else needs an IfBreak scope."

                        if topElse >= 0 then
                            Printer.InvalidDocument "Duplicate Else."

                        topElse <- i
                        topFlatWidth <- 0
                        topFlatTail <- 0
                        topFlatFlags <- FlatFlags.Valid
                        emit <- false
                    else
                        if depth = 0 then
                            Printer.InvalidDocument "Unmatched closing tag."

                        let fStart = topStart
                        let fElse = topElse
                        let fEffect = topEffect
                        let fFlatWidth = topFlatWidth
                        let fFlatTail = topFlatTail
                        let fFlatFlags = topFlatFlags
                        let fEnclosing = topEnclosing
                        let opening = elems[fStart]

                        let expected =
                            opening.B + (if opening.B = int Tag.StartIfBreak then 2 else 1)

                        if e.B <> expected then
                            Printer.InvalidDocument "Mismatched document tags."

                        depth <- depth - 1

                        if depth > 0 then
                            let p = &prep[depth - 1]
                            topStart <- p.Start
                            topElse <- p.Else
                            topEffect <- p.Effect
                            topFlatWidth <- p.FlatWidth
                            topFlatTail <- p.FlatTail
                            topFlatFlags <- p.FlatFlags
                            topEnclosing <- p.EnclosingGroup

                        elems[fStart].Width <- uint32 i
                        effect <- fEffect
                        let mutable groupFlag = opening.Facts &&& 128uy

                        if opening.B = int Tag.StartGroup then
                            let forcedFlat = opening.Flags &&& ElementFlags.NoExpand <> 0uy

                            let shouldBreak =
                                not forcedFlat
                                && (Boundary.has
                                        (Boundary.Hard
                                         ||| Boundary.SkipAfter
                                         ||| Boundary.NestedSkip)
                                        effect
                                    || opening.Flags &&& ElementFlags.Break <> 0uy)

                            if shouldBreak then
                                groupFlag <- groupFlag ||| 64uy

                            e.Facts <- effect &&& Boundary.Literal

                            effect <-
                                if forcedFlat then
                                    (effect &&& Boundary.Code)
                                    ||| (if Boundary.has Boundary.Literal effect then
                                             Boundary.Hard ||| Boundary.Literal
                                         else
                                             0uy)
                                else
                                    (effect
                                     &&& (Boundary.Code
                                          ||| Boundary.Hard
                                          ||| Boundary.NestedSkip
                                          ||| Boundary.Literal))
                                    ||| (if shouldBreak then Boundary.Hard else 0uy)
                                    ||| (if Boundary.has Boundary.SkipBefore effect then
                                             Boundary.NestedSkip
                                         else
                                             0uy)

                            if alwaysFits > 0 then
                                effect <- effect &&& Boundary.Code

                            let flatValid =
                                (opening.Facts &&& 128uy = 0uy)
                                && not shouldBreak
                                && (fFlatFlags &&& FlatFlags.Valid <> 0uy)

                            if flatValid && fFlatFlags = FlatFlags.Complete then
                                e.A <- fFlatWidth
                                e.Width <- uint32 ~~~fFlatTail
                            else
                                e.A <- -1

                            if flatValid then
                                flatWidth <- fFlatWidth
                                flatTail <- fFlatTail
                                flatFlags <- fFlatFlags
                        elif opening.B = int Tag.StartIndent then
                            flatWidth <- fFlatWidth
                            flatTail <- fFlatTail
                            flatFlags <- fFlatFlags
                        elif opening.B = int Tag.StartForceFlat then
                            effect <-
                                (effect &&& Boundary.Code)
                                ||| (if Boundary.has Boundary.Literal effect then
                                         Boundary.Hard ||| Boundary.Literal
                                     else
                                         0uy)

                            flatWidth <- fFlatWidth
                            flatTail <- fFlatTail
                            flatFlags <- fFlatFlags
                        elif opening.B = int Tag.StartConditionalGroup then
                            let forcedFlat = opening.Flags &&& ElementFlags.NoExpand <> 0uy
                            let mutable alternative = fStart + 1
                            let mutable code = false

                            let mutable shouldBreak =
                                not forcedFlat && opening.Flags &&& ElementFlags.Break <> 0uy

                            if alternative = i then
                                Printer.InvalidDocument "A conditional group needs an alternative."

                            while alternative < i do
                                if
                                    elems[alternative].Kind <> ElementKind.Tag
                                    || elems[alternative].B <> int Tag.StartAlternative
                                    || int elems[alternative].Width < alternative
                                then
                                    Printer.InvalidDocument
                                        "Conditional groups contain only alternatives."

                                let choice = elems[alternative].Facts
                                code <- code || Boundary.has Boundary.Code choice

                                if not forcedFlat then
                                    shouldBreak <-
                                        shouldBreak
                                        || Boundary.has
                                            (Boundary.NestedSkip ||| Boundary.NestedSkipAfterHard)
                                            choice

                                alternative <- int elems[alternative].Width + 1

                            if shouldBreak then
                                groupFlag <- groupFlag ||| 64uy

                            effect <- if code then Boundary.Code else 0uy
                        elif opening.B = int Tag.StartIfBreak then
                            e.Width <- uint32 ~~~(fElse + 1)

                            let validTarget =
                                opening.A < 0
                                || (fEnclosing >= 0
                                    && elems[fEnclosing].B = int Tag.StartGroup
                                    && elems[fEnclosing].A = opening.A)

                            if validTarget then
                                if fElse < 0 then
                                    flatFlags <- FlatFlags.Valid
                                else
                                    flatWidth <- fFlatWidth
                                    flatTail <- fFlatTail
                                    flatFlags <- fFlatFlags
                        elif opening.B = int Tag.StartAlwaysFits then
                            effect <- 0uy
                            alwaysFits <- alwaysFits - 1
                            flatFlags <- FlatFlags.Valid

                        elems[fStart].Facts <-
                            if
                                opening.B = int Tag.StartGroup
                                || opening.B = int Tag.StartConditionalGroup
                            then
                                (effect &&& Boundary.All) ||| groupFlag
                            else
                                effect ||| groupFlag
                elif byte e.Kind < byte ElementKind.Line || e.Kind = ElementKind.GeneratedText then
                    if e.Facts &&& ElementFacts.Code <> 0uy then
                        effect <- Boundary.Code

                    if e.Flags &&& (ElementFlags.Directive ||| ElementFlags.Multiline) = 0uy then
                        flatWidth <- int e.Width

                        flatTail <-
                            if e.Tail <> ElementFacts.TailUnknown then
                                int e.Tail
                            else
                                this.ScanTail e

                        flatFlags <- e.Facts
                elif e.Kind = ElementKind.Line then
                    if
                        (e.A >= int LineKind.Literal || e.A = int LineKind.Hard) && alwaysFits = 0
                    then
                        if
                            e.A = int LineKind.Hard
                            && e.Flags &&& ElementFlags.SkipBreakIfFirst <> 0uy
                        then
                            effect <- Boundary.SkipBefore
                        else
                            effect <-
                                if e.A >= int LineKind.Literal then
                                    Boundary.Hard ||| Boundary.Literal
                                else
                                    Boundary.Hard

                    if e.A = int LineKind.Normal then
                        flatWidth <- 1
                        flatTail <- 1
                        flatFlags <- FlatFlags.Valid
                    elif e.A = int LineKind.Soft then
                        flatFlags <- FlatFlags.Valid
                elif e.Kind = ElementKind.Shared then
                    let mutable j = e.A
                    let finish = e.A + e.B

                    if e.A < 0 || e.B < 0 || finish > i then
                        Printer.InvalidDocument "Shared ranges must precede their use."

                    while j < finish do
                        sharedWork <- sharedWork + 1
                        let ej = elems[j]

                        let jEffect =
                            if
                                byte ej.Kind < byte ElementKind.Line
                                || ej.Kind = ElementKind.GeneratedText
                            then
                                if ej.Facts &&& ElementFacts.Code <> 0uy then
                                    Boundary.Code
                                else
                                    0uy
                            elif ej.Kind = ElementKind.Tag && int ej.Width >= 0 then
                                if ej.B = int Tag.StartGroup then
                                    (ej.Facts &&& Boundary.All)
                                    ||| (elems[int ej.Width].Facts &&& Boundary.Literal)
                                elif ej.B = int Tag.StartConditionalGroup then
                                    ej.Facts &&& Boundary.All
                                else
                                    ej.Facts &&& (Boundary.All ||| Boundary.Literal)
                            else
                                ej.Facts &&& (Boundary.All ||| Boundary.Literal)

                        effect <- Boundary.combine (effect, jEffect)

                        if ej.Kind = ElementKind.Tag && int ej.Width >= 0 then
                            j <- int ej.Width + 1
                        else
                            j <- j + 1

                    if alwaysFits > 0 then
                        effect <- effect &&& Boundary.Code
                elif e.Kind = ElementKind.BreakParent then
                    effect <- if alwaysFits = 0 then Boundary.Hard else 0uy
                elif e.Kind = ElementKind.Reindent then
                    effect <-
                        if alwaysFits = 0 then
                            Boundary.Hard ||| Boundary.Literal
                        else
                            0uy

                if emit then
                    if
                        hasShared
                        && not (
                            byte e.Kind < byte ElementKind.Line
                            || e.Kind = ElementKind.GeneratedText
                            || e.Kind = ElementKind.Tag
                        )
                    then
                        e.Facts <- effect

                    if depth > 0 then
                        if effect <> 0uy then
                            topEffect <- Boundary.combine (topEffect, effect)

                        if topFlatFlags = 0uy || flatFlags &&& FlatFlags.Valid = 0uy then
                            topFlatFlags <- 0uy
                        else
                            topFlatWidth <- topFlatWidth + flatWidth

                            topFlatTail <-
                                if flatFlags &&& FlatFlags.NonWhitespace <> 0uy then
                                    flatTail
                                else
                                    topFlatTail + flatTail

                            topFlatFlags <- topFlatFlags ||| flatFlags

        if depth <> 0 then
            Printer.InvalidDocument "Unclosed document tag."

    member private _.GroupMode(id: int, speculative: bool, flat: bool) =
        let mode =
            if speculative && stamps[id] = stamp then
                trialModes[id]
            else
                modes[id]

        if (mode - 1uy) > 1uy && not speculative then
            invalidArg "document" "IfBreak refers to a group that has not been printed."

        if (mode - 1uy) > 1uy then not flat else mode = 2uy

    member private this.Fits(candidate: Range, id: int, alternative: bool) =
        fitCalls <- fitCalls + 1
        let mutable curStamp = stamp + 1

        if curStamp = Int32.MaxValue then
            Array.Clear stamps
            curStamp <- 1

        stamp <- curStamp
        let elems = elements
        let stampsArr = stamps
        let trialModesArr = trialModes
        let mutable trialsArr = trials
        let cmdsArr = commands
        let maxWidth = options.Width
        let indentSize = options.IndentSize

        if id >= 0 then
            stampsArr[id] <- curStamp
            trialModesArr[id] <- if candidate.Flat then 1uy else 2uy

        let mutable trialCount = 1
        let mutable tNext = candidate.Next
        let mutable tFinish = candidate.Finish
        let mutable tIndent = candidate.Indent
        let mutable tFlat = candidate.Flat
        let mutable tForce = candidate.Force
        let mutable borrowed = commandCount - 1

        let mutable width =
            if pendingComment then
                candidate.Indent * indentSize
            else
                column

        let mutable pending = pendingComment
        let mutable inheritedPending = pendingComment
        let mutable whitespace = trailingWidth

        if pending then
            whitespace <- width

        let mutable lineContent =
            if lineHasCode && not pending then width - whitespace else 0

        let mutable lineIndent = if pending then width else -1

        let leadingBreak =
            alternative || Boundary.has Boundary.NestedSkip elems[candidate.Next - 1].Facts

        let mutable first = true
        let mutable firstText = true
        let mutable result = false
        let mutable finished = false

        if
            not alternative
            && candidate.Flat
            && not pending
            && id >= 0
            && elems[candidate.Finish].A >= 0
        then
            fitWork <- fitWork + 1
            width <- width + elems[candidate.Finish].A
            whitespace <- ~~~(int elems[candidate.Finish].Width)
            lineContent <- width - whitespace
            firstText <- false
            first <- false
            trialCount <- 0

        while not finished do
            if width > maxWidth && not first then
                finished <- true
            elif trialCount = 0 then
                if borrowed < 0 then
                    result <- width < maxWidth
                    finished <- true
                else
                    let b = &cmdsArr[borrowed]
                    tNext <- b.Next
                    tFinish <- b.Finish
                    tIndent <- b.Indent
                    tFlat <- b.Flat
                    tForce <- b.Force
                    borrowed <- borrowed - 1
                    trialCount <- 1
            elif tNext >= tFinish then
                trialCount <- trialCount - 1

                if trialCount > 0 then
                    let p = &trialsArr[trialCount - 1]
                    tNext <- p.Next
                    tFinish <- p.Finish
                    tIndent <- p.Indent
                    tFlat <- p.Flat
                    tForce <- p.Force
            else
                let index = tNext
                let e = &elems[index]
                tNext <- index + 1
                fitWork <- fitWork + 1

                match e.Kind with
                | ElementKind.Tag ->
                    let ending = int e.Width
                    let tag = enum<Tag> e.B

                    if ending >= 0 then
                        tNext <- ending + 1
                        let mutable cNext = index + 1
                        let mutable cFinish = ending
                        let mutable cIndent = tIndent
                        let mutable cFlat = tFlat
                        let mutable cForce = tForce
                        let mutable push = true

                        match tag with
                        | Tag.StartGroup ->
                            let force = tForce || e.Flags &&& ElementFlags.NoExpand <> 0uy
                            let groupBreaks = e.Facts &&& 64uy <> 0uy
                            cFlat <- tFlat || force
                            cForce <- force

                            if groupBreaks && not cForce then
                                cFlat <- false

                            stampsArr[e.A] <- curStamp
                            trialModesArr[e.A] <- if cFlat then 1uy else 2uy
                            let flatWidth = elems[ending].A

                            if cFlat && not pending && flatWidth >= 0 then
                                width <- width + flatWidth
                                whitespace <- ~~~(int elems[ending].Width)
                                lineContent <- width - whitespace
                                firstText <- false
                                first <- false
                                push <- false
                        | Tag.StartConditionalGroup ->
                            let force = tForce || e.Flags &&& ElementFlags.NoExpand <> 0uy
                            let groupBreaks = e.Facts &&& 64uy <> 0uy

                            if groupBreaks && tFlat && not force then
                                finished <- true

                            let mutable alt = index + 1

                            if (groupBreaks || not tFlat) && not force then
                                while int elems[alt].Width + 1 < ending do
                                    alt <- int elems[alt].Width + 1

                            cNext <- alt + 1
                            cFinish <- int elems[alt].Width
                            cFlat <- (tFlat && not groupBreaks) || force
                            cForce <- force
                            stampsArr[e.A] <- curStamp
                            trialModesArr[e.A] <- if cFlat then 1uy else 2uy
                        | Tag.StartIndent -> cIndent <- tIndent + 1
                        | Tag.StartForceFlat ->
                            cForce <- true
                            cFlat <- true
                        | Tag.StartAlwaysFits -> push <- false
                        | Tag.StartIfBreak ->
                            let broken =
                                if e.A < 0 then
                                    not tFlat
                                else
                                    let mode =
                                        if stampsArr[e.A] = curStamp then
                                            trialModesArr[e.A]
                                        else
                                            modes[e.A]

                                    if (mode - 1uy) > 1uy then not tFlat else mode = 2uy

                            let middle = ~~~(int elems[ending].Width) - 1

                            if broken then
                                cFinish <- (if middle < 0 then ending else middle)
                            else
                                cNext <- (if middle < 0 then ending else middle + 1)
                        | _ -> ()

                        if push then
                            if trialCount = trialsArr.Length then
                                Array.Resize(&trials, trialsArr.Length * 2)
                                trialsArr <- trials

                            trialsArr[trialCount - 1] <-
                                {
                                    Next = tNext
                                    Finish = tFinish
                                    Indent = tIndent
                                    Flat = tFlat
                                    Force = tForce
                                }

                            tNext <- cNext
                            tFinish <- cFinish
                            tIndent <- cIndent
                            tFlat <- cFlat
                            tForce <- cForce
                            trialCount <- trialCount + 1
                | ElementKind.Shared ->
                    if trialCount = trialsArr.Length then
                        Array.Resize(&trials, trialsArr.Length * 2)
                        trialsArr <- trials

                    trialsArr[trialCount - 1] <-
                        {
                            Next = tNext
                            Finish = tFinish
                            Indent = tIndent
                            Flat = tFlat
                            Force = tForce
                        }

                    tNext <- e.A
                    tFinish <- e.A + e.B
                    trialCount <- trialCount + 1
                | ElementKind.Trim ->
                    width <- width - whitespace
                    whitespace <- 0
                | ElementKind.Reindent ->
                    result <- true
                    finished <- true
                | ElementKind.Line ->
                    let literal = e.A >= int LineKind.Literal

                    if pending then
                        if not tFlat || e.A >= int LineKind.Hard then
                            result <- true
                            finished <- true
                    elif tForce && not literal then
                        if e.A <> int LineKind.Soft then
                            width <- width + 1
                            whitespace <- whitespace + 1
                    elif e.A >= int LineKind.Hard || not tFlat then
                        if
                            e.A = int LineKind.Hard
                            && e.Flags &&& ElementFlags.SkipBreakIfFirst <> 0uy
                            && first
                        then
                            width <- tIndent * indentSize
                            whitespace <- width
                            lineIndent <- width
                            lineContent <- 0
                        else
                            result <- true
                            finished <- true
                    elif e.A = int LineKind.Normal then
                        width <- width + 1
                        whitespace <- whitespace + 1
                | ElementKind.Text
                | ElementKind.GeneratedText
                | ElementKind.StaticToken ->
                    if e.Flags &&& ElementFlags.Directive = 0uy then
                        let hasCode = e.Facts &&& ElementFacts.Code <> 0uy

                        if pending && not inheritedPending then
                            finished <- true

                        if pending && hasCode then
                            width <- tIndent * indentSize
                            whitespace <- width
                            lineIndent <- width
                            lineContent <- 0
                            pending <- false
                            inheritedPending <- false

                        if e.Flags &&& ElementFlags.Multiline <> 0uy then
                            let text = this.Text e

                            if width + int (PrintedWidth.firstLine text) > maxWidth then
                                finished <- true

                            width <- int e.Width

                            lineIndent <-
                                this.LeadingWidth(text.Slice(text.LastIndexOfAny('\r', '\n') + 1))

                            lineContent <- width
                        else
                            width <- width + int e.Width
                            lineContent <- width

                        let tail = this.TextTail e

                        let length =
                            if e.Kind = ElementKind.StaticToken then
                                int e.Width
                            else
                                e.B

                        whitespace <- if tail = length then whitespace + tail else tail
                        lineContent <- width - whitespace

                        if e.Kind = ElementKind.StaticToken || e.B > 0 then
                            firstText <- false

                        if hasCode then
                            first <- false
                | ElementKind.LeadingComment when pending && not inheritedPending ->
                    finished <- true
                | ElementKind.LeadingComment ->
                    if lineIndent < 0 then
                        lineIndent <- this.OutputIndent()

                    if
                        pending
                        || (lineContent = 0 && width > whitespace && not tForce)
                        || (first && firstText && lineContent > 0 && not tForce)
                        || (leadingBreak
                            && (alternative || firstText)
                            && first
                            && (lineContent > 0 || width > lineIndent)
                            && not tForce)
                    then
                        width <- tIndent * indentSize
                        whitespace <- width
                        lineIndent <- width
                        lineContent <- 0
                        pending <- false
                        inheritedPending <- false

                    if lineContent > 0 || width > lineIndent then
                        result <- not tFlat
                        finished <- true
                    else
                        let text = this.Text e

                        if width = whitespace then
                            width <- tIndent * indentSize
                            whitespace <- width
                            lineIndent <- width

                        if text.IndexOfAny('\r', '\n') >= 0 then
                            let last = text.Slice(text.LastIndexOfAny('\r', '\n') + 1)
                            let delta = lineIndent - this.SourceIndent(e.A)

                            lineIndent <-
                                if this.CommentDirective(e, last) > 0 then
                                    this.LeadingWidth(last)
                                elif this.CommentAlternate(e, text) then
                                    max (this.LeadingWidth(last)) lineIndent
                                else
                                    max 0 (this.LeadingWidth(last) + delta)

                            width <- lineIndent + int (PrintedWidth.measure (last.Trim()))
                        else
                            width <- width + int (PrintedWidth.measure (text.Trim()))

                        whitespace <- 0
                        lineContent <- width
                | ElementKind.TrailingComment ->
                    if not tForce || (this.Text e).TrimStart().StartsWith("//".AsSpan()) then
                        if pending then
                            finished <- true
                        else
                            pending <- true
                            inheritedPending <- false
                | _ -> ()

        result

    member private this.Comment(e: FormatElement, command: Range) =
        if lineHasDirective then
            this.Newline(command.Indent, true)

        if lineHasLineComment then
            this.Newline(command.Indent, true)

        if pendingComment && e.Kind = ElementKind.LeadingComment then
            this.Newline(command.Indent, true)

        let text = this.Text e
        let trimmedStart = text.TrimStart()

        let startsWithSlashSlash =
            trimmedStart.Length >= 2 && trimmedStart[0] = '/' && trimmedStart[1] = '/'

        let lineComment = e.Flags &&& ElementFlags.Multiline = 0uy && startsWithSlashSlash

        if e.Kind = ElementKind.TrailingComment then
            if
                column > 0
                && outputCount > 0
                && output[outputCount - 1] <> 32uy
                && output[outputCount - 1] <> 9uy
            then
                this.Space()

            this.AppendComment text
            pendingComment <- not command.Force || startsWithSlashSlash
        else
            let mutable lineStart = outputCount

            while lineStart > 0 && (output[lineStart - 1] = 32uy || output[lineStart - 1] = 9uy) do
                lineStart <- lineStart - 1

            if lineStart = 0 || output[lineStart - 1] = 10uy || output[lineStart - 1] = 13uy then
                this.Trim()
                this.Indent(command.Indent * options.IndentSize)
            else
                this.Newline(command.Indent, true)

            if startsWithSlashSlash && trimmedStart.Length >= 3 && trimmedStart[2] = '/' then
                let mutable start = 0
                let mutable nl = text.IndexOfAny('\r', '\n')

                while nl >= 0 do
                    let mutable finish = start + nl
                    this.Append(text.Slice(start, nl).Trim())

                    if
                        text[finish] = '\r' && finish + 1 < text.Length && text[finish + 1] = '\n'
                    then
                        finish <- finish + 1

                    this.Newline(command.Indent, false)
                    start <- finish + 1
                    nl <- text.Slice(start).IndexOfAny('\r', '\n')

                this.Append(text.Slice(start).Trim())
            elif e.Flags &&& ElementFlags.Multiline = 0uy then
                this.Append(text.TrimEnd())
            else
                let mutable first = 0

                while first < text.Length && (text[first] = ' ' || text[first] = '\t') do
                    first <- first + 1

                let delta = this.OutputIndent() - this.SourceIndent(e.A)
                let mutable start = first
                let mutable alternate = false
                let mutable nl = text.Slice(start).IndexOfAny('\r', '\n')

                while nl >= 0 do
                    let mutable finish = start + nl
                    let lineSlice = text.Slice(start, nl)
                    let directive = this.CommentDirective(e, lineSlice)
                    alternate <- alternate || directive = 2 || directive = 3
                    this.Append(lineSlice.TrimEnd())

                    if
                        text[finish] = '\r' && finish + 1 < text.Length && text[finish + 1] = '\n'
                    then
                        finish <- finish + 1

                    this.Newline(0, false)
                    start <- finish + 1
                    let mutable indent = 0

                    while start < text.Length && (text[start] = ' ' || text[start] = '\t') do
                        indent <- indent + (if text[start] = '\t' then options.IndentSize else 1)

                        start <- start + 1

                    let column =
                        if this.CommentDirective(e, text.Slice(start)) > 0 then
                            indent
                        elif alternate then
                            max indent (command.Indent * options.IndentSize)
                        else
                            max 0 (indent + delta)

                    this.Indent column
                    nl <- text.Slice(start).IndexOfAny('\r', '\n')

                this.Append(text.Slice(start).TrimEnd())

        if lineComment then
            lineHasLineComment <- true

        if e.Kind = ElementKind.LeadingComment && lineComment then
            pendingComment <- true

        if not command.Force || pendingComment then
            remeasure <- true

    member internal _.SharedPreparationWork = sharedWork
    member internal _.FitCalls = fitCalls
    member internal _.FitWork = fitWork

    member internal _.SourceLineScans = sourceLineScans

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    static member private InvalidPrintOptions(message: string) =
        raise (ArgumentException(message, "printerOptions"))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintRegion(e: FormatElement, commandIndent: int) =
        if e.B = 0 then
            if e.Kind = ElementKind.BeginRegion then
                if regionCount = regions.Length then
                    Array.Resize(&regions, regions.Length * 2)

                regions[regionCount] <- -1
                regionCount <- regionCount + 1
            elif regionCount > 0 then
                regionCount <- regionCount - 1
        else
            if pendingComment || lineHasDirective || not (this.AtLineStart()) then
                this.Newline(0, true)

            let mutable indent = commandIndent

            if e.Kind = ElementKind.BeginRegion then
                if regionCount = regions.Length then
                    Array.Resize(&regions, regions.Length * 2)

                regions[regionCount] <- indent
                regionCount <- regionCount + 1
            elif regionCount > 0 then
                regionCount <- regionCount - 1

                if regions[regionCount] >= 0 then
                    indent <- regions[regionCount]
                else
                    let mutable enclosing = regionCount - 1

                    while enclosing >= 0 && regions[enclosing] < 0 do
                        enclosing <- enclosing - 1

                    if enclosing >= 0 then
                        indent <- regions[enclosing]

            this.Trim()
            this.Indent(indent * options.IndentSize)
            this.Append(this.Text e)
            lineHasDirective <- true

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ApplyTrimInitialLines() =
        let mutable i = 0
        let mutable start = 0
        let mutable units = 0
        let mutable startUnits = 0
        let mutable scanning = true

        while scanning && i < outputCount do
            let struct (scalar, size) =
                Utf8Text.scalarAt (ReadOnlySpan<byte>(output, i, outputCount - i))

            if size > 0 && Rune.IsWhiteSpace(Rune scalar) then
                let unit = if scalar > 0xFFFF then 2 else 1

                if scalar = 10 || scalar = 13 then
                    start <- i + size
                    startUnits <- units + unit

                i <- i + size
                units <- units + unit
            else
                scanning <- false

        output.AsSpan(start, outputCount - start).CopyTo(output.AsSpan())
        outputCount <- outputCount - start
        outputUtf16Count <- outputUtf16Count - startUnits

        if this.TrackSourceMappings && start > 0 then
            let mutable count = 0

            for index = 0 to sourceMappings.Count - 1 do
                let struct (position, first, length) = sourceMappings[index]
                let skipped = max 0 (startUnits - position)

                if skipped < length then
                    sourceMappings[count] <-
                        struct (max 0 (position - startUnits), first + skipped, length - skipped)

                    count <- count + 1

            sourceMappings.RemoveRange(count, sourceMappings.Count - count)

    member this.Print(input: string, document: DocumentBuffer, printerOptions: PrinterOptions) =
        ObjectDisposedException.ThrowIf(disposed, typeof<Printer>)

        if printerOptions.Width <= 0 then
            Printer.InvalidPrintOptions "Width must be greater than zero."

        if printerOptions.IndentSize <= 0 then
            Printer.InvalidPrintOptions "IndentSize must be greater than zero."

        if uint32 printerOptions.EndOfLine > 2u then
            Printer.InvalidPrintOptions "EndOfLine must be Lf, CrLf or Cr."

        cachedText <- null
        source <- input
        elements <- document.Storage
        generated <- document.Generated

        asciiInput <-
            (if Object.ReferenceEquals(document.SourceForAscii, input) then
                 document.SourceIsAscii
             else
                 Ascii.IsValid(input.AsSpan()))
            && (document.GeneratedCount = 0
                || Ascii.IsValid(generated.AsSpan(0, document.GeneratedCount)))

        options <- printerOptions
        outputCount <- 0
        pendingHighEnd <- -1
        outputUtf16Count <- 0
        sourceMappings.Clear()
        column <- 0
        outputLineStart <- 0
        layoutLineEnd <- -1
        sourceLineStart <- 0
        sourceLineFinish <- -1
        trailingWidth <- 0
        lineHasCode <- false
        lineHasDirective <- false
        lineHasLineComment <- false
        regionCount <- 0
        pendingComment <- false
        pendingSourceIndent <- false
        remeasure <- false
        sharedWork <- 0
        fitCalls <- 0
        fitWork <- 0
        sourceLineScans <- 0

        this.ReserveOutput(
            min
                (int64 Array.MaxLength)
                (max
                    0L
                    (min
                        (int64 this.MaxOutputLength)
                        (int64 source.Length
                         + (int64 source.Length >>> 1)
                         + (int64 source.Length >>> 3)
                         + 64L)))
        )

        this.Prepare(document.Count, document.GroupCount, document.HasShared)

        if commands.Length = 0 then
            Array.Resize(&commands, 16)
            Array.Resize(&trials, 16)

        let elems = elements
        let modesArr = modes
        let mutable cmds = commands
        let optIndentSize = printerOptions.IndentSize
        let trackMappings = this.TrackSourceMappings
        let srcLen = source.Length
        let srcFirst = &Unsafe.AsRef(&MemoryMarshal.GetReference(source.AsSpan()))
        let mutable curNext = 0
        let mutable curFinish = document.Count
        let mutable curIndent = 0
        let mutable curFlat = false
        let mutable curForce = false
        commandCount <- 1

        while commandCount > 0 do
            if curNext >= curFinish then
                commandCount <- commandCount - 1

                if commandCount > 0 then
                    let p = &cmds[commandCount - 1]
                    curNext <- p.Next
                    curFinish <- p.Finish
                    curIndent <- p.Indent
                    curFlat <- p.Flat
                    curForce <- p.Force
            else
                let index = curNext
                let e = &elems[index]
                let hdr = FormatElementHeader.read &e
                curNext <- index + 1

                match e.Kind with
                | ElementKind.Tag ->
                    let ending = int e.Width

                    if ending >= 0 then
                        if commandCount = cmds.Length then
                            Array.Resize(&commands, cmds.Length * 2)
                            cmds <- commands

                        cmds[commandCount - 1] <-
                            {
                                Next = ending + 1
                                Finish = curFinish
                                Indent = curIndent
                                Flat = curFlat
                                Force = curForce
                            }

                        let mutable child =
                            {
                                Next = index + 1
                                Finish = ending
                                Indent = curIndent
                                Flat = curFlat
                                Force = curForce
                            }

                        match enum<Tag> e.B with
                        | Tag.StartGroup ->
                            if pendingComment then
                                remeasure <- true

                            let force = curForce || e.Flags &&& ElementFlags.NoExpand <> 0uy

                            let flat =
                                force
                                || ((e.Facts &&& 64uy = 0uy)
                                    && ((curFlat && not remeasure)
                                        || this.Fits({ child with Flat = true }, e.A, false)))

                            child.Flat <- flat
                            child.Force <- force
                            modesArr[e.A] <- if flat then 1uy else 2uy
                            remeasure <- false
                        | Tag.StartConditionalGroup ->
                            if pendingComment then
                                remeasure <- true

                            let force = curForce || e.Flags &&& ElementFlags.NoExpand <> 0uy
                            let forced = (e.Facts &&& 64uy <> 0uy) && not force
                            let mutable alt = index + 1
                            let mutable chosen = false
                            let mutable flat = true

                            while not chosen do
                                let altEnd = int elems[alt].Width
                                let next = altEnd + 1

                                let candidate =
                                    { child with
                                        Next = alt + 1
                                        Finish = altEnd
                                        Flat = curFlat || alt = index + 1 || force
                                        Force = force
                                    }

                                if
                                    not forced
                                    && (force
                                        || (curFlat && not remeasure)
                                        || this.Fits(candidate, e.A, true))
                                then
                                    chosen <- true
                                    flat <- candidate.Flat
                                elif next >= ending then
                                    chosen <- true
                                    flat <- not forced && candidate.Flat
                                else
                                    alt <- next

                            child.Next <- alt + 1
                            child.Finish <- int elems[alt].Width
                            child.Flat <- flat || force
                            child.Force <- force
                            modesArr[e.A] <- if child.Flat then 1uy else 2uy
                            remeasure <- false
                        | Tag.StartIndent -> child.Indent <- curIndent + 1
                        | Tag.StartForceFlat ->
                            child.Flat <- true
                            child.Force <- true
                        | Tag.StartIfBreak ->
                            let broken =
                                if e.A < 0 then
                                    not curFlat
                                else
                                    this.GroupMode(e.A, false, curFlat)

                            let middle = ~~~(int elems[ending].Width) - 1

                            if broken then
                                child.Finish <- (if middle < 0 then ending else middle)
                            else
                                child.Next <- (if middle < 0 then ending else middle + 1)
                        | _ -> ()

                        curNext <- child.Next
                        curFinish <- child.Finish
                        curIndent <- child.Indent
                        curFlat <- child.Flat
                        curForce <- child.Force
                        commandCount <- commandCount + 1
                | ElementKind.Shared ->
                    if commandCount = cmds.Length then
                        Array.Resize(&commands, cmds.Length * 2)
                        cmds <- commands

                    cmds[commandCount - 1] <-
                        {
                            Next = curNext
                            Finish = curFinish
                            Indent = curIndent
                            Flat = curFlat
                            Force = curForce
                        }

                    curNext <- e.A
                    curFinish <- e.A + e.B
                    commandCount <- commandCount + 1
                | ElementKind.StaticToken when e.A = int StaticToken.Space ->
                    if not pendingComment then
                        if pendingSourceIndent then
                            this.Indent(curIndent * optIndentSize)
                            pendingSourceIndent <- false

                        let start = outputCount
                        let outArr = output

                        if int64 start < writeLimit && uint32 start < uint32 outArr.Length then
                            Unsafe.Add(&MemoryMarshal.GetArrayDataReference outArr, start) <- 32uy
                            outputCount <- start + 1
                            outputUtf16Count <- outputUtf16Count + 1
                            column <- column + 1
                            trailingWidth <- trailingWidth + 1
                        else
                            this.Space()
                | ElementKind.StaticToken when
                    not pendingComment
                    && not lineHasLineComment
                    && not lineHasDirective
                    && not pendingSourceIndent
                    && not trackMappings
                    && int64 outputCount + 16L <= writeLimit
                    ->
                    let start = outputCount
                    let outArr = output
                    let a = e.A

                    if uint32 (a - 1) < 11u && uint32 start < uint32 outArr.Length then
                        Unsafe.Add(&MemoryMarshal.GetArrayDataReference outArr, start) <-
                            Unsafe.Add(
                                &MemoryMarshal.GetArrayDataReference StaticText.singleBytes,
                                a
                            )

                        outputCount <- start + 1
                        outputUtf16Count <- outputUtf16Count + 1
                        column <- column + 1
                        trailingWidth <- 0
                        lineHasCode <- true
                    else
                        let bytes = StaticText.utf8Bytes[a]
                        let len = bytes.Length
                        bytes.AsSpan().CopyTo(outArr.AsSpan(start, len))
                        outputCount <- start + len
                        outputUtf16Count <- outputUtf16Count + len
                        column <- column + len
                        trailingWidth <- 0
                        lineHasCode <- true
                | ElementKind.Text
                | ElementKind.GeneratedText
                | ElementKind.StaticToken ->
                    if
                        hdr = FormatElementHeader.fastCodeText
                        && asciiInput
                        && not trackMappings
                        && not pendingComment
                        && not lineHasLineComment
                        && not lineHasDirective
                        && not pendingSourceIndent
                        && uint32 e.A <= uint32 srcLen
                        && uint32 e.B <= uint32 (srcLen - e.A)
                        && int64 outputCount + int64 e.B <= writeLimit
                    then
                        let len = e.B
                        let start = outputCount
                        let outArr = output

                        if uint32 start <= uint32 (outArr.Length - len) then
                            let outBase =
                                &Unsafe.Add(&MemoryMarshal.GetArrayDataReference outArr, start)

                            let inBase = &Unsafe.Add(&srcFirst, e.A)

                            if len = 1 then
                                outBase <- byte inBase
                            elif len = 2 then
                                outBase <- byte inBase
                                Unsafe.Add(&outBase, 1) <- byte (Unsafe.Add(&inBase, 1))
                            elif len = 3 then
                                outBase <- byte inBase
                                Unsafe.Add(&outBase, 1) <- byte (Unsafe.Add(&inBase, 1))
                                Unsafe.Add(&outBase, 2) <- byte (Unsafe.Add(&inBase, 2))
                            elif len = 4 then
                                outBase <- byte inBase
                                Unsafe.Add(&outBase, 1) <- byte (Unsafe.Add(&inBase, 1))
                                Unsafe.Add(&outBase, 2) <- byte (Unsafe.Add(&inBase, 2))
                                Unsafe.Add(&outBase, 3) <- byte (Unsafe.Add(&inBase, 3))
                            elif
                                AdvSimd.IsSupported
                                && len <= 8
                                && e.A <= srcLen - 8
                                && start <= outArr.Length - 8
                            then
                                let v = Vector128.LoadUnsafe(&Unsafe.As<char, uint16>(&inBase))
                                (AdvSimd.ExtractNarrowingLower v).StoreUnsafe(&outBase)
                            elif
                                AdvSimd.IsSupported
                                && len <= 16
                                && e.A <= srcLen - 16
                                && start <= outArr.Length - 16
                            then
                                let u16Ref = &Unsafe.As<char, uint16>(&inBase)
                                let lo = Vector128.LoadUnsafe(&u16Ref, 0un)
                                let hi = Vector128.LoadUnsafe(&u16Ref, 8un)

                                AdvSimd
                                    .ExtractNarrowingUpper(AdvSimd.ExtractNarrowingLower lo, hi)
                                    .StoreUnsafe(&outBase)
                            elif len > 0 then
                                this.CopyOutput(source.AsSpan(e.A, len), start)
                        elif len > 0 then
                            this.CopyOutput(source.AsSpan(e.A, len), start)

                        outputCount <- start + len
                        outputUtf16Count <- outputUtf16Count + len
                        column <- column + len
                        trailingWidth <- 0
                        lineHasCode <- true
                    else
                        let text = this.Text e

                        let multiline = e.Flags &&& ElementFlags.Multiline <> 0uy

                        let directive = e.Flags &&& ElementFlags.Directive <> 0uy

                        let hasCode =
                            if directive then
                                not (text.IsWhiteSpace())
                            else
                                e.Facts &&& ElementFacts.Code <> 0uy

                        if hasCode && (pendingComment || lineHasLineComment) then
                            this.Newline(curIndent, true)

                        let ownsLine = directive && this.OwnsLine e

                        if
                            hasCode && (lineHasDirective || (ownsLine && not (this.AtLineStart())))
                        then
                            this.Newline((if ownsLine then 0 else curIndent), true)

                        if not pendingComment then
                            if pendingSourceIndent then
                                this.Indent(curIndent * options.IndentSize)
                                pendingSourceIndent <- false

                            this.Append(text, int e.Width, multiline, this.TextTail e)

                            if ownsLine && hasCode then
                                lineHasDirective <- not (this.AtLineStart())

                            if multiline then
                                lineHasCode <-
                                    not (
                                        text
                                            .Slice(text.LastIndexOfAny('\r', '\n') + 1)
                                            .IsWhiteSpace()
                                    )
                            elif hasCode && not directive then
                                lineHasCode <- true
                | ElementKind.Trim ->
                    if pendingComment then
                        this.Newline(curIndent, true)

                    this.Trim()
                    pendingSourceIndent <- false
                | ElementKind.Reindent ->
                    this.Trim()
                    outputLineStart <- outputCount
                    column <- 0
                    trailingWidth <- 0
                    lineHasCode <- false
                    lineHasDirective <- false
                    lineHasLineComment <- false
                    pendingSourceIndent <- true
                    pendingComment <- false
                    remeasure <- true
                | ElementKind.Line ->
                    let literal = e.A = int LineKind.Literal

                    if
                        e.Flags &&& ElementFlags.SquashBlank <> 0uy
                        && not curForce
                        && not literal
                        && outputCount > 0
                        && this.NewlinesAtEnd() = 0
                    then
                        this.Newline(curIndent, true)

                    if pendingComment && curFlat && e.A < int LineKind.Hard then
                        ()
                    elif pendingComment then
                        this.Newline((if literal then 0 else curIndent), not literal)
                    elif curForce && e.A < int LineKind.Literal then
                        if
                            e.A <> int LineKind.Soft
                            && e.Flags &&& ElementFlags.SquashBlank = 0uy
                            && not (e.A = int LineKind.Hard && this.EndsWithDelimitedComment())
                        then
                            this.Space()
                    elif e.A >= int LineKind.Hard || not curFlat then
                        let newlines =
                            if
                                e.Flags &&& (ElementFlags.Squash ||| ElementFlags.SquashBlank)
                                <> 0uy
                            then
                                this.NewlinesAtEnd()
                            else
                                0

                        if
                            not (literal && outputCount = 0)
                            && not (e.Flags &&& ElementFlags.Squash <> 0uy && newlines > 0)
                            && not (e.Flags &&& ElementFlags.SquashBlank <> 0uy && newlines > 1)
                        then
                            this.Newline(
                                (if literal then 0 else curIndent),
                                not literal && e.Flags &&& ElementFlags.NoTrim = 0uy
                            )
                    elif e.A = int LineKind.Normal then
                        this.Space()
                | ElementKind.LeadingComment
                | ElementKind.TrailingComment ->
                    pendingSourceIndent <- false

                    this.Comment(
                        e,
                        {
                            Next = curNext
                            Finish = curFinish
                            Indent = curIndent
                            Flat = curFlat
                            Force = curForce
                        }
                    )
                | ElementKind.BeginRegion
                | ElementKind.EndRegion -> this.PrintRegion(e, curIndent)
                | _ -> ()

        let initialEndCount = outputCount
        let mutable trimming = true

        while trimming && outputCount > 0 do
            let lastByte = output[outputCount - 1]

            if lastByte > 32uy && lastByte < 127uy then
                trimming <- false
            elif lastByte = 32uy || lastByte = 9uy || lastByte = 10uy || lastByte = 13uy then
                outputCount <- outputCount - 1
                outputUtf16Count <- outputUtf16Count - 1
            else
                let struct (scalar, size) =
                    Utf8Text.lastScalar (ReadOnlySpan<byte>(output, 0, outputCount))

                if size > 0 && Rune.IsWhiteSpace(Rune scalar) then
                    outputCount <- outputCount - size
                    outputUtf16Count <- outputUtf16Count - (if scalar > 0xFFFF then 2 else 1)
                else
                    trimming <- false

        if this.TrackSourceMappings && outputCount < initialEndCount then
            this.TrimSourceMappings()

        if options.TrimInitialLines then
            this.ApplyTrimInitialLines()

        if outputCount > 0 then
            this.Newline(0, false)

        if int64 outputUtf16Count > int64 this.MaxOutputLength then
            this.FailOutputLimit()

        if outputUtf16Count = source.Length then
            if asciiInput || outputCount = outputUtf16Count then
                if Ascii.Equals(ReadOnlySpan<byte>(output, 0, outputCount), source.AsSpan()) then
                    cachedText <- source
            elif matchesUtf16 (ReadOnlySpan<byte>(output, 0, outputCount)) (source.AsSpan()) then
                cachedText <- source

        source <- ""
        elements <- Array.empty
        generated <- Array.empty

    member internal this.CheckOutputLimit() =
        if int64 outputUtf16Count > int64 this.MaxOutputLength then
            this.FailOutputLimit()

    member _.OutputBytes: ReadOnlySpan<byte> =
        ObjectDisposedException.ThrowIf(disposed, typeof<Printer>)
        ReadOnlySpan<byte>(output, 0, outputCount)

    member _.OutputText: string =
        ObjectDisposedException.ThrowIf(disposed, typeof<Printer>)

        if isNull cachedText then
            cachedText <-
                if outputCount = 0 then
                    ""
                elif asciiInput || outputCount = outputUtf16Count then
                    String.Create(outputCount, output, asciiToUtf16Action)
                else
                    Encoding.UTF8.GetString(ReadOnlySpan<byte>(output, 0, outputCount))

        cachedText

    member _.MatchesText(text: string) =
        Object.ReferenceEquals(cachedText, text)

    member _.HasCachedText = not (isNull cachedText)

    member _.DecodeOutputTo(destination: Span<char>) : int =
        ObjectDisposedException.ThrowIf(disposed, typeof<Printer>)

        if outputCount = 0 then
            0
        elif asciiInput || outputCount = outputUtf16Count then
            let mutable written = 0

            Ascii.ToUtf16(ReadOnlySpan<byte>(output, 0, outputCount), destination, &written)
            |> ignore

            written
        else
            Encoding.UTF8.GetChars(ReadOnlySpan<byte>(output, 0, outputCount), destination)

    member internal _.OutputIsAscii = asciiInput || outputCount = outputUtf16Count

    member _.OutputUtf16Length =
        ObjectDisposedException.ThrowIf(disposed, typeof<Printer>)
        outputUtf16Count

    member internal _.OutputBufferLength = output.Length

    member internal _.SwapOutputBuffer(replacement: byte array) : struct (byte array * int) =
        ObjectDisposedException.ThrowIf(disposed, typeof<Printer>)
        let taken = output
        let takenCount = outputCount
        output <- if isNull replacement then Array.empty else replacement
        outputCount <- 0
        outputUtf16Count <- 0
        writeLimit <- 0L
        cachedText <- null
        struct (taken, takenCount)

    member _.Dispose() =
        if not disposed then
            PoolArray.release &output
            PoolArray.release &modes
            PoolArray.release &trialModes
            PoolArray.release &stamps
            PoolArray.release &groupParents
            outputCount <- 0
            outputUtf16Count <- 0
            writeLimit <- 0L
            cachedText <- null
            elements <- Array.empty
            generated <- Array.empty
            source <- ""
            preparation <- Array.empty
            commands <- Array.empty
            trials <- Array.empty
            regions <- Array.empty
            disposed <- true

    interface IDisposable with
        member this.Dispose() = this.Dispose()
