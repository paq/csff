namespace Csff.Lexer

open System
open System.Buffers
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Runtime.InteropServices

[<assembly: InternalsVisibleTo("Csff.Parser")>]
[<assembly: InternalsVisibleTo("Csff.Printer")>]
[<assembly: InternalsVisibleTo("Csff.Conformance")>]
[<assembly: InternalsVisibleTo("Csff.Cli")>]
[<assembly: InternalsVisibleTo("Csff.Tests")>]
do ()

module internal PoolLimits =
    let bucketCount =
        if GC.GetGCMemoryInfo().TotalAvailableMemoryBytes < 4L * 1024L * 1024L * 1024L then
            11
        else
            13

    let maxPooledLength = 1024 <<< (bucketCount - 1)

[<AbstractClass; Sealed>]
type internal SharedBuckets<'T> =
    [<DefaultValue>]
    static val mutable private buckets: ResizeArray<'T[]>[]

    [<DefaultValue>]
    static val mutable private fast: 'T[][]

    static do
        let n = PoolLimits.bucketCount

        SharedBuckets<'T>.buckets <-
            Array.init n (fun b -> ResizeArray<'T[]>(if b >= 11 then 4 else 64))

        SharedBuckets<'T>.fast <- Array.zeroCreate<'T[]> n

    static member inline private BucketIndex(size: int) =
        let b = 32 - System.Numerics.BitOperations.LeadingZeroCount(uint32 (size - 1))
        max 0 (b - 10)

    static member private TryPop(b: int) : 'T[] =
        let quick = System.Threading.Interlocked.Exchange(&SharedBuckets<'T>.fast[b], null)

        if not (isNull quick) then
            quick
        else
            let stack = SharedBuckets<'T>.buckets[b]
            let mutable popped: 'T[] = null

            lock stack (fun () ->
                let last = stack.Count - 1

                if last >= 0 then
                    popped <- stack[last]
                    stack.RemoveAt last)

            popped

    static member Rent(minCapacity: int) : 'T[] =
        let b = SharedBuckets<'T>.BucketIndex(max 1024 minCapacity)

        if b < PoolLimits.bucketCount then
            let popped = SharedBuckets<'T>.TryPop b

            if not (isNull popped) then
                popped
            else
                GC.AllocateUninitializedArray<'T>(1024 <<< b)
        else
            GC.AllocateUninitializedArray<'T> minCapacity

    static member RentZeroed(minCapacity: int) : 'T[] =
        let b = SharedBuckets<'T>.BucketIndex(max 1024 minCapacity)

        if b < PoolLimits.bucketCount then
            let popped = SharedBuckets<'T>.TryPop b

            if not (isNull popped) then
                Array.Clear popped
                popped
            else
                Array.zeroCreate<'T>(1024 <<< b)
        else
            Array.zeroCreate<'T> minCapacity

    static member Return(arr: 'T[]) =
        let len = arr.Length

        if len >= 1024 && len <= PoolLimits.maxPooledLength && (len &&& (len - 1)) = 0 then
            let b = System.Numerics.BitOperations.TrailingZeroCount(uint32 len) - 10

            if
                uint32 b < uint32 PoolLimits.bucketCount
                && not (
                    isNull (
                        System.Threading.Interlocked.CompareExchange(
                            &SharedBuckets<'T>.fast[b],
                            arr,
                            null
                        )
                    )
                )
            then
                let stack = SharedBuckets<'T>.buckets[b]

                let maxStack =
                    if b >= 11 then
                        if PoolLimits.bucketCount > 11 then 3 else 1
                    else
                        8192

                lock stack (fun () ->
                    if stack.Count < maxStack then
                        stack.Add arr)

module internal PoolArray =
    let maxPooledLength = PoolLimits.maxPooledLength

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let grow (arr: 'T[] byref) (count: int) (minCapacity: int) =
        let maxLen = PoolLimits.maxPooledLength

        let step =
            if arr.Length >= 16384 then
                arr.Length + (arr.Length >>> 1)
            else
                max 1024 (arr.Length * 2)

        let target =
            if count = 0 && minCapacity > maxLen then
                minCapacity
            else
                max minCapacity step

        if count = 0 && arr.Length > 0 && arr.Length <= maxLen then
            SharedBuckets<'T>.Return arr
            arr <- Array.empty

        let grown =
            if target <= maxLen then
                SharedBuckets<'T>.Rent target
            else
                GC.AllocateUninitializedArray<'T> target

        if count > 0 then
            arr.AsSpan(0, count).CopyTo(grown.AsSpan())

            if arr.Length > 0 && arr.Length <= maxLen then
                SharedBuckets<'T>.Return arr

        arr <- grown

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    let growZeroed (arr: 'T[] byref) (count: int) (minCapacity: int) =
        let maxLen = PoolLimits.maxPooledLength

        let step =
            if arr.Length >= 16384 then
                arr.Length + (arr.Length >>> 1)
            else
                max 1024 (arr.Length * 2)

        let target =
            if count = 0 && minCapacity > maxLen then
                minCapacity
            else
                max minCapacity step

        if count = 0 && arr.Length > 0 && arr.Length <= maxLen then
            SharedBuckets<'T>.Return arr
            arr <- Array.empty

        let grown =
            if target <= maxLen then
                SharedBuckets<'T>.RentZeroed target
            else
                Array.zeroCreate<'T> target

        if count > 0 then
            arr.AsSpan(0, count).CopyTo(grown.AsSpan())

            if arr.Length > 0 && arr.Length <= maxLen then
                SharedBuckets<'T>.Return arr

        arr <- grown

    let release (arr: 'T[] byref) =
        if arr.Length > 0 && arr.Length <= PoolLimits.maxPooledLength then
            SharedBuckets<'T>.Return arr

        arr <- Array.empty

[<Struct>]
type Trivia =
    {
        Kind: TriviaKind
        Start: int
        Length: int
    }

[<Struct>]
type Token =
    {
        Kind: TokenKind
        Start: int
        Length: int
        TriviaStart: int
        LeadingCount: int
        TrailingCount: int
    }

    member inline this.End = this.Start + this.Length

[<Struct>]
type internal DirectiveFrame =
    {
        Region: bool
        ParentActive: bool
        BranchTaken: bool
        ElseSeen: bool
    }

[<AllowNullLiteral; Sealed>]
type internal DirectiveState() =
    member val Frames = ResizeArray<DirectiveFrame>()
    member val Symbols = HashSet<string>(StringComparer.Ordinal)
    member val Active = true with get, set

    member this.Reset() =
        this.Frames.Clear()
        this.Symbols.Clear()
        this.Active <- true

[<Struct>]
type internal ConditionalLexWindow =
    {
        Valid: bool
        PrefixTokenCount: int
        PrefixTriviaCount: int
        PrefixScanStart: int
        PrefixLastComment: int
        PrefixLastNonComment: int
        PrefixLastArrowOffset: int
        PrefixLastParenArrowOffset: int
        PrefixParenArrowCount: int
        PrefixInterpolatedCount: int
        PrefixContextualCount: int
        SuffixTokenIndex: int
        SuffixTriviaStart: int
        SuffixScanStart: int
        SuffixContextualStart: int
        SuffixParenArrowStart: int
        SuffixInterpolatedStart: int
    }

[<Sealed>]
type TokenBuffer() =
    let mutable tokens: Token[] = Array.empty
    let mutable trivia: Trivia[] = Array.empty
    let mutable tokenCount = 0
    let mutable triviaCount = 0
    let mutable hasInterpolated = false
    let mutable hasIfDirective = false
    let mutable lastArrowOffset = -1
    let mutable lastParenArrowOffset = -1
    let mutable lastCommentTrivia = -1
    let mutable lastNonCommentTrivia = -1
    let mutable hasDisabledText = false
    let mutable hasSingleConfigBlocker = false
    let mutable hasMalformedTrivia = false
    let mutable hasSeededSymbols = false
    let mutable isVerifyOnly = false
    let mutable directives: DirectiveState = null
    let inactive = ResizeArray<int>()
    let parenArrows = ResizeArray<int>()
    let interpolated = ResizeArray<int>()
    let contextual = ResizeArray<int>()
    let mutable hasBadToken = false
    let mutable version = 0

    member _.TokenCount = tokenCount
    member _.TriviaCount = triviaCount
    member _.Version = version
    member _.HasInterpolated = hasInterpolated
    member _.HasIfDirective = hasIfDirective
    member _.LastArrowOffset = lastArrowOffset
    member _.LastParenArrowOffset = lastParenArrowOffset
    member _.ParenArrowCount = parenArrows.Count

    member _.ParenArrow(index: int) = parenArrows[index]

    member _.InterpolatedCount = interpolated.Count

    member _.Interpolated(index: int) = interpolated[index]

    member internal _.ContextualOffsets = contextual

    member internal _.AddContextual(offset: int) = contextual.Add offset

    member _.HasBadToken = hasBadToken

    member internal _.MarkBadToken() = hasBadToken <- true
    member internal _.MarkMalformedTrivia() = hasMalformedTrivia <- true
    member _.HasComments = lastCommentTrivia >= 0
    member _.HasNonCommentContent = lastNonCommentTrivia >= 0
    member _.LastCommentTrivia = lastCommentTrivia
    member _.LastNonCommentTrivia = lastNonCommentTrivia
    member _.HasDisabledText = hasDisabledText
    member _.HasSingleConfigBlocker = hasSingleConfigBlocker
    member _.HasMalformedTrivia = hasMalformedTrivia
    member internal _.TokensStorage = tokens
    member internal _.TriviaStorage = trivia
    member internal _.ResizeTrivia(used: int, size: int) = PoolArray.grow &trivia used size

    member internal _.AcquireDirectives() =
        if isNull directives then
            directives <- DirectiveState()
        else
            directives.Reset()

        directives

    member _.HasSeededSymbols
        with get () = hasSeededSymbols
        and internal set value = hasSeededSymbols <- value

    member internal _.IsVerifyOnly
        with get () = isVerifyOnly
        and set value = isVerifyOnly <- value

    member _.Reset() =
        version <- version + 1
        tokenCount <- 0
        triviaCount <- 0
        hasInterpolated <- false
        hasIfDirective <- false
        lastArrowOffset <- -1
        lastParenArrowOffset <- -1
        lastCommentTrivia <- -1
        lastNonCommentTrivia <- -1
        hasDisabledText <- false
        hasSingleConfigBlocker <- false
        hasMalformedTrivia <- false
        hasSeededSymbols <- false
        isVerifyOnly <- false
        inactive.Clear()
        parenArrows.Clear()
        interpolated.Clear()
        contextual.Clear()
        hasBadToken <- false

    member this.ReleasePooledBuffers() =
        PoolArray.release &tokens
        PoolArray.release &trivia
        this.Reset()

    member _.EnsureCapacity(estimated: int) =
        let tokenEstimated = min 524288 (max 64 (estimated >>> 1))

        if tokenCount = 0 && tokenEstimated > tokens.Length then
            PoolArray.grow &tokens 0 tokenEstimated

        let triviaEstimated = min 524288 (max 64 (estimated >>> 1))

        if triviaEstimated > trivia.Length then
            PoolArray.grow &trivia triviaCount triviaEstimated

    member _.EnsureCapacity(estimatedTokens: int, estimatedTrivia: int) =
        let tokenEstimated = min 524288 estimatedTokens

        if tokenCount = 0 && tokenEstimated > tokens.Length then
            PoolArray.grow &tokens 0 tokenEstimated

        let triviaEstimated = min 524288 (max 64 estimatedTrivia)

        if triviaEstimated > trivia.Length then
            PoolArray.grow &trivia triviaCount triviaEstimated

    member internal _.MarkInactive(index: int) = inactive.Add index

    member _.IsInactiveDirective(index: int) =
        inactive.Count > 0 && inactive.BinarySearch index >= 0

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.AddLayoutTrivia(kind: TriviaKind, start: int, length: int) =
        let tc = triviaCount

        if uint32 tc >= uint32 trivia.Length then
            PoolArray.grow &trivia tc (tc + 1)

        Unsafe.Add(&MemoryMarshal.GetArrayDataReference trivia, tc) <-
            {
                Kind = kind
                Start = start
                Length = length
            }

        triviaCount <- tc + 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.AddTrivia(kind: TriviaKind, start: int, length: int) =
        let tc = triviaCount

        if uint32 tc >= uint32 trivia.Length then
            PoolArray.grow &trivia tc (tc + 1)

        if kind > TriviaKind.WhitespaceTrivia then
            if
                kind >= TriviaKind.SingleLineCommentTrivia
                && kind <= TriviaKind.MultiLineDocumentationCommentTrivia
            then
                lastCommentTrivia <- tc
            else
                lastNonCommentTrivia <- tc

                match kind with
                | TriviaKind.IfDirectiveTrivia ->
                    hasIfDirective <- true
                    hasSingleConfigBlocker <- true
                | TriviaKind.DisabledTextTrivia ->
                    hasDisabledText <- true
                    hasSingleConfigBlocker <- true
                | TriviaKind.ElifDirectiveTrivia
                | TriviaKind.ElseDirectiveTrivia
                | TriviaKind.EndIfDirectiveTrivia
                | TriviaKind.DefineDirectiveTrivia
                | TriviaKind.UndefDirectiveTrivia -> hasSingleConfigBlocker <- true
                | TriviaKind.SkippedTokensTrivia
                | TriviaKind.BadDirectiveTrivia
                | TriviaKind.ConflictMarkerTrivia -> hasMalformedTrivia <- true
                | _ -> ()

        Unsafe.Add(&MemoryMarshal.GetArrayDataReference trivia, tc) <-
            {
                Kind = kind
                Start = start
                Length = length
            }

        triviaCount <- tc + 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.AddToken(token: Token) =
        let tc = tokenCount

        if uint32 tc >= uint32 tokens.Length then
            PoolArray.grow &tokens tc (tc + 1)

        let baseRef = &MemoryMarshal.GetArrayDataReference tokens

        if token.Kind = TokenKind.InterpolatedStringToken then
            hasInterpolated <- true
            interpolated.Add tc
        elif token.Kind = TokenKind.EqualsGreaterThanToken then
            lastArrowOffset <- token.Start

            if tc > 0 && Unsafe.Add(&baseRef, tc - 1).Kind = TokenKind.CloseParenToken then
                lastParenArrowOffset <- token.Start
                parenArrows.Add(tc - 1)

        Unsafe.Add(&baseRef, tc) <- token
        tokenCount <- tc + 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.AddToken
        (
            kind: TokenKind,
            start: int,
            length: int,
            triviaStart: int,
            leadingCount: int,
            trailingCount: int
        ) =
        let tc = tokenCount

        if uint32 tc >= uint32 tokens.Length then
            PoolArray.grow &tokens tc (tc + 1)

        let baseRef = &MemoryMarshal.GetArrayDataReference tokens

        if kind = TokenKind.InterpolatedStringToken then
            hasInterpolated <- true
            interpolated.Add tc
        elif kind = TokenKind.EqualsGreaterThanToken then
            lastArrowOffset <- start

            if tc > 0 && Unsafe.Add(&baseRef, tc - 1).Kind = TokenKind.CloseParenToken then
                lastParenArrowOffset <- start
                parenArrows.Add(tc - 1)

        Unsafe.Add(&baseRef, tc) <-
            {
                Kind = kind
                Start = start
                Length = length
                TriviaStart = triviaStart
                LeadingCount = leadingCount
                TrailingCount = trailingCount
            }

        tokenCount <- tc + 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal _.AddVerifyToken
        (
            kind: TokenKind,
            start: int,
            length: int,
            triviaStart: int,
            leadingCount: int,
            trailingCount: int
        ) =
        let tc = tokenCount

        if uint32 tc >= uint32 tokens.Length then
            PoolArray.grow &tokens tc (tc + 1)

        if kind = TokenKind.InterpolatedStringToken then
            hasInterpolated <- true

        Unsafe.Add(&MemoryMarshal.GetArrayDataReference tokens, tc) <-
            {
                Kind = kind
                Start = start
                Length = length
                TriviaStart = triviaStart
                LeadingCount = leadingCount
                TrailingCount = trailingCount
            }

        tokenCount <- tc + 1

    member _.NextTriviaIndex = triviaCount

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Token(index: int) = tokens[index]

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Trivia(index: int) = trivia[index]

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.TokenSpan() =
        ReadOnlySpan<Token>(tokens, 0, tokenCount)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.TriviaSpan() =
        ReadOnlySpan<Trivia>(trivia, 0, triviaCount)

    member internal _.ParenArrowsList = parenArrows
    member internal _.InterpolatedList = interpolated
    member internal _.InactiveList = inactive

    member internal this.CopyAllFrom(other: TokenBuffer) =
        this.Reset()
        let tCount = other.TokenCount
        let trCount = other.TriviaCount

        if tCount > tokens.Length then
            PoolArray.grow &tokens 0 tCount

        if trCount > trivia.Length then
            PoolArray.grow &trivia 0 trCount

        if tCount > 0 then
            other.TokensStorage.AsSpan(0, tCount).CopyTo(tokens.AsSpan(0, tCount))

        if trCount > 0 then
            other.TriviaStorage.AsSpan(0, trCount).CopyTo(trivia.AsSpan(0, trCount))

        tokenCount <- tCount
        triviaCount <- trCount
        hasInterpolated <- other.HasInterpolated
        hasIfDirective <- other.HasIfDirective
        lastArrowOffset <- other.LastArrowOffset
        lastParenArrowOffset <- other.LastParenArrowOffset
        lastCommentTrivia <- other.LastCommentTrivia
        lastNonCommentTrivia <- other.LastNonCommentTrivia
        hasDisabledText <- other.HasDisabledText
        hasSingleConfigBlocker <- other.HasSingleConfigBlocker
        hasMalformedTrivia <- other.HasMalformedTrivia
        hasSeededSymbols <- other.HasSeededSymbols
        isVerifyOnly <- other.IsVerifyOnly
        hasBadToken <- other.HasBadToken

        let copyList (src: ResizeArray<int>) (dst: ResizeArray<int>) =
            let n = src.Count

            if n > 0 then
                dst.EnsureCapacity n |> ignore
                CollectionsMarshal.SetCount(dst, n)
                CollectionsMarshal.AsSpan(src).CopyTo(CollectionsMarshal.AsSpan dst)

        copyList other.InactiveList inactive
        copyList other.ParenArrowsList parenArrows
        copyList other.InterpolatedList interpolated
        copyList other.ContextualOffsets contextual

    member internal _.CopyPrefixFrom(defaultBuf: TokenBuffer, win: inref<ConditionalLexWindow>) =
        version <- version + 1
        let pTok = win.PrefixTokenCount
        let pTriv = win.PrefixTriviaCount

        if pTok > 0 then
            if pTok > tokens.Length then
                PoolArray.grow &tokens 0 pTok

            defaultBuf.TokensStorage.AsSpan(0, pTok).CopyTo(tokens.AsSpan(0, pTok))
            tokenCount <- pTok

        if pTriv > 0 then
            if pTriv > trivia.Length then
                PoolArray.grow &trivia 0 pTriv

            defaultBuf.TriviaStorage.AsSpan(0, pTriv).CopyTo(trivia.AsSpan(0, pTriv))
            triviaCount <- pTriv

        lastCommentTrivia <- win.PrefixLastComment
        lastNonCommentTrivia <- win.PrefixLastNonComment
        lastArrowOffset <- win.PrefixLastArrowOffset
        lastParenArrowOffset <- win.PrefixLastParenArrowOffset

        if win.PrefixParenArrowCount > 0 then
            let n = win.PrefixParenArrowCount
            parenArrows.EnsureCapacity n |> ignore
            CollectionsMarshal.SetCount(parenArrows, n)

            CollectionsMarshal
                .AsSpan(defaultBuf.ParenArrowsList)
                .Slice(0, n)
                .CopyTo(CollectionsMarshal.AsSpan parenArrows)

        if win.PrefixInterpolatedCount > 0 then
            hasInterpolated <- true
            let n = win.PrefixInterpolatedCount
            interpolated.EnsureCapacity n |> ignore
            CollectionsMarshal.SetCount(interpolated, n)

            CollectionsMarshal
                .AsSpan(defaultBuf.InterpolatedList)
                .Slice(0, n)
                .CopyTo(CollectionsMarshal.AsSpan interpolated)

        if win.PrefixContextualCount > 0 then
            let n = win.PrefixContextualCount
            contextual.EnsureCapacity n |> ignore
            CollectionsMarshal.SetCount(contextual, n)

            CollectionsMarshal
                .AsSpan(defaultBuf.ContextualOffsets)
                .Slice(0, n)
                .CopyTo(CollectionsMarshal.AsSpan contextual)

    member internal _.AppendSuffixFrom(defaultBuf: TokenBuffer, win: inref<ConditionalLexWindow>) =
        let syncedTok = tokenCount
        let syncedTriv = triviaCount
        let remTok = defaultBuf.TokenCount - win.SuffixTokenIndex
        let remTriv = defaultBuf.TriviaCount - win.SuffixTriviaStart
        let tokDelta = syncedTok - win.SuffixTokenIndex
        let trivDelta = syncedTriv - win.SuffixTriviaStart

        if remTriv > 0 then
            if syncedTriv + remTriv > trivia.Length then
                PoolArray.grow &trivia syncedTriv (syncedTriv + remTriv)

            defaultBuf.TriviaStorage
                .AsSpan(win.SuffixTriviaStart, remTriv)
                .CopyTo(trivia.AsSpan(syncedTriv, remTriv))

            triviaCount <- syncedTriv + remTriv

        if remTok > 0 then
            if syncedTok + remTok > tokens.Length then
                PoolArray.grow &tokens syncedTok (syncedTok + remTok)

            let srcToks = defaultBuf.TokensStorage.AsSpan(win.SuffixTokenIndex, remTok)
            let dstToks = tokens.AsSpan(syncedTok, remTok)

            if trivDelta = 0 then
                srcToks.CopyTo dstToks
            else
                for idx = 0 to remTok - 1 do
                    let t = srcToks[idx]

                    dstToks[idx] <-
                        { t with
                            TriviaStart = t.TriviaStart + trivDelta
                        }

            tokenCount <- syncedTok + remTok

        if defaultBuf.LastCommentTrivia >= win.SuffixTriviaStart then
            lastCommentTrivia <- defaultBuf.LastCommentTrivia + trivDelta

        if defaultBuf.LastNonCommentTrivia >= win.SuffixTriviaStart then
            lastNonCommentTrivia <- defaultBuf.LastNonCommentTrivia + trivDelta

        if defaultBuf.LastArrowOffset >= win.SuffixScanStart then
            lastArrowOffset <- defaultBuf.LastArrowOffset

        let defPa = defaultBuf.ParenArrowsList
        let remPa = defPa.Count - win.SuffixParenArrowStart

        if remPa > 0 then
            let curPa = parenArrows.Count
            parenArrows.EnsureCapacity(curPa + remPa) |> ignore
            CollectionsMarshal.SetCount(parenArrows, curPa + remPa)
            let srcPa = CollectionsMarshal.AsSpan(defPa).Slice(win.SuffixParenArrowStart, remPa)
            let dstPa = CollectionsMarshal.AsSpan(parenArrows).Slice(curPa, remPa)

            if tokDelta = 0 then
                srcPa.CopyTo dstPa
            else
                for idx = 0 to remPa - 1 do
                    dstPa[idx] <- srcPa[idx] + tokDelta

            lastParenArrowOffset <- defaultBuf.LastParenArrowOffset

        let defIp = defaultBuf.InterpolatedList
        let remIp = defIp.Count - win.SuffixInterpolatedStart

        if remIp > 0 then
            hasInterpolated <- true
            let curIp = interpolated.Count
            interpolated.EnsureCapacity(curIp + remIp) |> ignore
            CollectionsMarshal.SetCount(interpolated, curIp + remIp)

            let srcIp =
                CollectionsMarshal.AsSpan(defIp).Slice(win.SuffixInterpolatedStart, remIp)

            let dstIp = CollectionsMarshal.AsSpan(interpolated).Slice(curIp, remIp)

            if tokDelta = 0 then
                srcIp.CopyTo dstIp
            else
                for idx = 0 to remIp - 1 do
                    dstIp[idx] <- srcIp[idx] + tokDelta

        let defCtx = defaultBuf.ContextualOffsets
        let remCtx = defCtx.Count - win.SuffixContextualStart

        if remCtx > 0 then
            let curCtx = contextual.Count
            contextual.EnsureCapacity(curCtx + remCtx) |> ignore
            CollectionsMarshal.SetCount(contextual, curCtx + remCtx)

            CollectionsMarshal
                .AsSpan(defCtx)
                .Slice(win.SuffixContextualStart, remCtx)
                .CopyTo(CollectionsMarshal.AsSpan(contextual).Slice(curCtx, remCtx))

        struct (syncedTok, syncedTriv)
