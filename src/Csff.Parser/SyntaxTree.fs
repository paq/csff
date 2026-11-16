namespace Csff.Parser

open System
open System.Buffers
open System.Collections.Generic
open System.Runtime.CompilerServices
open Csff.Lexer

[<assembly: InternalsVisibleTo("Csff.Printer")>]
[<assembly: InternalsVisibleTo("Csff.Conformance")>]
[<assembly: InternalsVisibleTo("Csff.Tests")>]
do ()

[<Struct; NoEquality; NoComparison>]
type internal DelimiterEnd =
    val mutable Generation: int
    val mutable Offset: int
    val mutable Hint: int

[<Sealed>]
type internal TokenInput() =
    static let mutable nextGeneration = 0

    let mutable dedicated: Token[] = Array.empty
    let mutable tokens = dedicated
    let mutable count = 0
    let mutable gapStart = 0
    let mutable gapEnd = 0
    let mutable copied = 0L
    let mutable lastArrowOffset = -1
    let mutable lastParenArrowOffset = -1

    let mutable ends: DelimiterEnd[] = Array.empty
    let mutable generation = 0
    let mutable endsUsed = false
    let parenArrows = ResizeArray<struct (int * int)>()

    let freshEnds () =
        endsUsed <- false
        generation <- 0

    let ensureGeneration () =
        if not endsUsed then
            endsUsed <- true
            let next = System.Threading.Interlocked.Increment(&nextGeneration)

            if next > 0 && next < Int32.MaxValue then
                generation <- next
            else
                if ends.Length > 0 then
                    Array.Clear ends

                generation <- 1

    let keepEnds (length: int) =
        if ends.Length < length then
            let copyCount = if endsUsed then ends.Length else 0

            if generation = 1 && nextGeneration < 0 then
                let grown = Array.zeroCreate<DelimiterEnd>(max length (ends.Length * 2))

                if copyCount > 0 then
                    Array.Copy(ends, grown, copyCount)

                ends <- grown
            else
                PoolArray.growZeroed &ends copyCount length

    member _.Count = count
    member _.CopiedTokenCount = copied
    member _.LastArrowOffset = lastArrowOffset
    member _.LastParenArrowOffset = lastParenArrowOffset

    member _.Clear() =
        parenArrows.Clear()
        tokens <- dedicated
        count <- 0
        gapStart <- 0
        gapEnd <- dedicated.Length
        copied <- 0L
        lastArrowOffset <- -1
        lastParenArrowOffset <- -1
        freshEnds ()

    member this.ReleasePooledBuffers() =
        PoolArray.release &dedicated
        PoolArray.release &ends
        this.Clear()

    member private _.Materialize(minCapacity: int, gapAt: int) =
        let needed = max minCapacity (count + 128)

        if needed > dedicated.Length then
            PoolArray.grow &dedicated 0 needed

        let newGapEnd = dedicated.Length - (count - gapAt)

        if count > 0 then
            Array.Copy(tokens, 0, dedicated, 0, gapAt)
            Array.Copy(tokens, gapAt, dedicated, newGapEnd, count - gapAt)
            copied <- copied + int64 count

        tokens <- dedicated
        gapStart <- gapAt
        gapEnd <- newGapEnd

        if endsUsed then
            keepEnds tokens.Length

            if count > gapAt then
                Array.Copy(ends, gapAt, ends, newGapEnd, count - gapAt)

    member private this.Materialize(minCapacity: int) = this.Materialize(minCapacity, count)

    member this.EnsureCapacity(capacity: int) =
        if not (obj.ReferenceEquals(tokens, dedicated)) then
            this.Materialize capacity
        elif capacity > dedicated.Length then
            let step =
                if dedicated.Length >= 16384 then
                    dedicated.Length + (dedicated.Length >>> 1)
                else
                    max 1024 (dedicated.Length * 2)

            let target = max capacity step

            if count = 0 && dedicated.Length > 0 && dedicated.Length <= 1048576 then
                SharedBuckets<Token>.Return dedicated
                dedicated <- Array.empty

            let grown =
                if target <= 1048576 then
                    SharedBuckets<Token>.Rent target
                else
                    GC.AllocateUninitializedArray<Token> target

            let newGapEnd = grown.Length - (count - gapStart)

            if count > 0 then
                Array.Copy(dedicated, 0, grown, 0, gapStart)
                Array.Copy(dedicated, gapEnd, grown, newGapEnd, count - gapStart)
                copied <- copied + int64 count

            if endsUsed then
                let endsTarget = max grown.Length ends.Length

                let movedEnds =
                    if generation = 1 && nextGeneration < 0 then
                        Array.zeroCreate<DelimiterEnd> endsTarget
                    elif endsTarget <= 1048576 then
                        SharedBuckets<DelimiterEnd>.RentZeroed endsTarget
                    else
                        Array.zeroCreate<DelimiterEnd> endsTarget

                if count > 0 && ends.Length >= dedicated.Length then
                    Array.Copy(ends, 0, movedEnds, 0, gapStart)
                    Array.Copy(ends, gapEnd, movedEnds, newGapEnd, count - gapStart)

                PoolArray.release &ends
                ends <- movedEnds

            if dedicated.Length > 0 && dedicated.Length <= 1048576 then
                SharedBuckets<Token>.Return dedicated

            dedicated <- grown
            tokens <- grown
            gapEnd <- newGapEnd

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.PhysicalIndex(index: int) =
        if index < gapStart then
            index
        else
            index + gapEnd - gapStart

    member this.Item
        with get index = tokens[this.PhysicalIndex index]
        and set index token =
            if not (obj.ReferenceEquals(tokens, dedicated)) then
                this.Materialize(count + 128, min count (index + 1))

            let physical = this.PhysicalIndex index

            if endsUsed && tokens[physical].Start <> token.Start && physical < ends.Length then
                ends[physical].Generation <- 0

            tokens[physical] <- token
            copied <- copied + 1L

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.KindOf(index: int) = tokens[this.PhysicalIndex index].Kind

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.KindAt(index: int) = this.KindOf(min index (count - 1))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.ItemRef(index: int) : inref<Token> = &tokens[this.PhysicalIndex index]

    member _.NextDelimiter(index: int) =
        let inline delimiter (kind: TokenKind) =
            let offset = uint (int kind - int TokenKind.OpenParenToken)
            offset <= 8u && ((0b110000011u >>> int offset) &&& 1u) <> 0u

        let mutable result = -1
        let mutable logical = index

        if logical < gapStart then
            let mutable physical = logical

            while physical < gapStart && not (delimiter tokens[physical].Kind) do
                physical <- physical + 1

            if physical < gapStart then
                result <- physical
            else
                logical <- gapStart

        if result < 0 then
            let shift = gapEnd - gapStart
            let finish = count + shift
            let mutable physical = logical + shift

            while physical < finish && not (delimiter tokens[physical].Kind) do
                physical <- physical + 1

            result <- physical - shift

        result

    member this.TryEnd(index: int, offset: outref<int>, hint: outref<int>) =
        if not endsUsed then
            false
        else
            let physical = this.PhysicalIndex index

            if physical < ends.Length && ends[physical].Generation = generation then
                offset <- ends[physical].Offset
                hint <- ends[physical].Hint
                true
            else
                false

    member this.SetEnd(index: int, offset: int, hint: int) =
        let physical = this.PhysicalIndex index
        keepEnds tokens.Length
        ensureGeneration ()
        let slot = &ends[physical]
        slot.Generation <- generation
        slot.Offset <- offset
        slot.Hint <- hint

    member this.Insert(index: int, token: Token) =
        this.EnsureCapacity(count + 1)

        if endsUsed then
            keepEnds tokens.Length

        if index < gapStart then
            let length = gapStart - index
            Array.Copy(tokens, index, tokens, gapEnd - length, length)

            if endsUsed then
                Array.Copy(ends, index, ends, gapEnd - length, length)

            copied <- copied + int64 length
            gapStart <- index
            gapEnd <- gapEnd - length
        elif index > gapStart then
            let length = index - gapStart
            Array.Copy(tokens, gapEnd, tokens, gapStart, length)

            if endsUsed then
                Array.Copy(ends, gapEnd, ends, gapStart, length)

            copied <- copied + int64 length
            gapStart <- index
            gapEnd <- gapEnd + length

        if endsUsed then
            ends[gapStart].Generation <- 0

        if token.Kind = TokenKind.EqualsGreaterThanToken then
            if token.Start > lastArrowOffset then
                lastArrowOffset <- token.Start

            if
                gapStart > 0
                && tokens[gapStart - 1].Kind = TokenKind.CloseParenToken
                && token.Start > lastParenArrowOffset
            then
                lastParenArrowOffset <- token.Start

        tokens[gapStart] <- token
        copied <- copied + 1L
        gapStart <- gapStart + 1
        count <- count + 1

    member this.Add(token: Token) =
        if gapStart = count && gapStart < gapEnd then
            if token.Kind = TokenKind.EqualsGreaterThanToken then
                if token.Start > lastArrowOffset then
                    lastArrowOffset <- token.Start

                if gapStart > 0 && tokens[gapStart - 1].Kind = TokenKind.CloseParenToken then
                    parenArrows.Add(struct (tokens[gapStart - 1].Start, gapStart - 1))

                    if token.Start > lastParenArrowOffset then
                        lastParenArrowOffset <- token.Start

            tokens[gapStart] <- token
            copied <- copied + 1L
            gapStart <- gapStart + 1
            count <- count + 1
        else
            this.Insert(count, token)

    member _.AddParenArrow(offset: int, index: int) = parenArrows.Add(struct (offset, index))

    member _.ParenArrows = parenArrows

    member this.AddRange(span: ReadOnlySpan<Token>) =
        if span.Length > 0 then
            this.EnsureCapacity(count + span.Length)

            if gapStart <> count then
                for i = 0 to span.Length - 1 do
                    this.Add span[i]
            else
                span.CopyTo(tokens.AsSpan(gapStart, span.Length))
                copied <- copied + int64 span.Length
                gapStart <- gapStart + span.Length
                count <- count + span.Length

    member _.MergeArrows(lastArrow: int, lastParenArrow: int) =
        lastArrowOffset <- max lastArrowOffset lastArrow
        lastParenArrowOffset <- max lastParenArrowOffset lastParenArrow

    member _.BorrowFrom(storage: Token[], length: int, lastArrow: int, lastParenArrow: int) =
        parenArrows.Clear()
        tokens <- storage
        count <- length
        gapStart <- length
        gapEnd <- length
        copied <- 0L
        lastArrowOffset <- lastArrow
        lastParenArrowOffset <- lastParenArrow
        freshEnds ()

    member this.BorrowFrom(storage: Token[], length: int, lastArrow: int) =
        this.BorrowFrom(storage, length, lastArrow, lastArrow)

    member this.CopyFrom(span: ReadOnlySpan<Token>, lastArrow: int) =
        this.Clear()
        lastArrowOffset <- lastArrow
        lastParenArrowOffset <- lastArrow
        this.EnsureCapacity(span.Length + 128)
        span.CopyTo(tokens.AsSpan(0, span.Length))
        count <- span.Length
        gapStart <- span.Length
        gapEnd <- tokens.Length
        copied <- int64 span.Length

    member this.CopyFrom(span: ReadOnlySpan<Token>) = this.CopyFrom(span, Int32.MaxValue)

[<Struct>]
type Node =
    {
        Kind: NodeKind
        mutable Parent: int32
        ChildStart: int32
        ChildCount: int32
        TokenStart: int32
        TokenCount: int32
    }

[<Sealed>]
type internal ChildArena() =
    let mutable values: int[] = Array.empty
    let mutable entryCount = 0

    member _.Reset() = entryCount <- 0

    member _.ReleasePooledBuffers() =
        PoolArray.release &values
        entryCount <- 0

    member _.Checkpoint() = entryCount

    member _.Restore(entries: int) = entryCount <- entries

    member _.EnsureCapacity(estimatedEntries: int) =
        if entryCount = 0 && estimatedEntries > values.Length then
            PoolArray.grow &values 0 estimatedEntries

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Begin() = entryCount

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Release(start: int) = entryCount <- start

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Add(value: int) =
        if entryCount = values.Length then
            PoolArray.grow &values entryCount (values.Length + 1)

        let index = entryCount
        entryCount <- entryCount + 1
        values[index] <- value

    member _.EntryCount = entryCount
    member _.Values = values

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Value(index: int) = values[index]

    member _.Set(index: int, value: int) = values[index] <- value

[<Struct; NoEquality; NoComparison>]
type internal ChildList =
    val private arena: ChildArena
    val private start: int

    new(arena, start) = { arena = arena; start = start }

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.Add(value) = this.arena.Add(value)

    member inline this.Count = this.arena.EntryCount - this.start
    member inline this.Start = this.start

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.Value(index) = this.arena.Value(index)

    member this.Item
        with get offset = this.arena.Value(this.start + offset)

    member this.Set(offset, value) =
        this.arena.Set(this.start + offset, value)

[<Sealed>]
type SyntaxTree() =
    let childArena = ChildArena()
    let lexerBuffer = TokenBuffer()
    let interpolationBuffer = TokenBuffer()
    let interpolationTokens = ResizeArray<Token>()
    let contextualOffsets = ResizeArray<int>()
    let mutable inputMayHoldIncomplete = true
    let inputTokens = TokenInput()
    let mutable tupleSpineDepths: Dictionary<int, int> = null

    let mutable expressionEnds =
        Dictionary<
            struct (int * int * bool * bool * bool * bool * bool),
            struct (int * int * NodeKind * bool)
         >()

    let parameterOpenings = ResizeArray<int>()
    let tupleOpenings = ResizeArray<int>()
    let localParentheses = ResizeArray<int>()
    let localBrackets = ResizeArray<int>()
    let lambdaParentheses = ResizeArray<struct (int * int)>()
    let lambdaBrackets = ResizeArray<struct (int * int)>()
    let mutable nodes: Node[] = Array.empty
    let mutable collectionConditionals: bool[] = Array.empty
    let mutable children: int32[] = Array.empty
    let mutable tokens: Token[] = Array.empty
    let mutable nodeCount = 0
    let mutable childCount = 0
    let mutable tokenCount = 0
    let mutable dedicatedTrivia: Trivia[] = Array.empty
    let mutable trivia: Trivia[] = dedicatedTrivia
    let mutable triviaCount = 0
    let mutable hasIfDirective = false
    let mutable recoveredTokens = 0
    let mutable incompleteCount = 0
    let mutable lambdaBalanceVisits = 0
    let mutable lambdaDelimiterResetWork = 0

    let isIncompleteToken (token: Token) = SyntaxTree.IsIncomplete token

    member _.LexerBuffer = lexerBuffer
    member _.HasIfDirective = hasIfDirective || lexerBuffer.HasIfDirective
    member internal _.InterpolationBuffer = interpolationBuffer
    member internal _.InterpolationTokens = interpolationTokens
    member internal _.ContextualOffsets = contextualOffsets

    member internal _.InputMayHoldIncomplete
        with get () = inputMayHoldIncomplete
        and set value = inputMayHoldIncomplete <- value

    static member internal IsIncomplete(token: Token) =
        token.Kind = TokenKind.BadToken
        || (token.Length <= 0
            && token.Kind <> TokenKind.EndOfFileToken
            && token.Kind <> TokenKind.OmittedArraySizeExpressionToken
            && token.Kind <> TokenKind.OmittedTypeArgumentToken
            && token.Kind <> TokenKind.InterpolatedStringTextToken)

    member internal _.InputTokens = inputTokens

    member internal _.TupleSpineDepths =
        if isNull tupleSpineDepths then
            tupleSpineDepths <- Dictionary<int, int>()

        tupleSpineDepths

    member internal _.ExpressionEnds = expressionEnds
    member internal _.CollectionConditionals = collectionConditionals
    member internal _.ParameterOpenings = parameterOpenings
    member internal _.TupleOpenings = tupleOpenings
    member internal _.LocalParentheses = localParentheses
    member internal _.LocalBrackets = localBrackets
    member internal _.LambdaParentheses = lambdaParentheses
    member internal _.LambdaBrackets = lambdaBrackets
    member internal _.InputTokenCopyCount = inputTokens.CopiedTokenCount

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal _.NewChildren() =
        ChildList(childArena, childArena.Begin())

    member _.NodeCount = nodeCount
    member _.ChildCount = childCount
    member _.TokenCount = tokenCount
    member _.TriviaCount = triviaCount
    member _.RootIndex = if nodeCount = 0 then -1 else 0

    member _.LambdaBalanceVisits = lambdaBalanceVisits

    member _.LambdaDelimiterResetWork = lambdaDelimiterResetWork

    member internal _.AddLambdaBalanceVisits(count: int) =
        lambdaBalanceVisits <- lambdaBalanceVisits + count

    member internal _.ResetParsed() =
        nodeCount <- 0
        childCount <- 0
        tokenCount <- 0
        trivia <- dedicatedTrivia
        triviaCount <- 0
        hasIfDirective <- false
        recoveredTokens <- 0
        incompleteCount <- 0
        lambdaBalanceVisits <- 0
        lambdaDelimiterResetWork <- 0

        if not (isNull tupleSpineDepths) && tupleSpineDepths.Count > 0 then
            tupleSpineDepths.Clear()

        if expressionEnds.Count > 0 then
            let expressionCapacity = expressionEnds.EnsureCapacity 0

            if
                expressionCapacity > 2048
                && int64 expressionCapacity > 16L * int64 expressionEnds.Count
            then
                expressionEnds <-
                    Dictionary<
                        struct (int * int * bool * bool * bool * bool * bool),
                        struct (int * int * NodeKind * bool)
                     >(
                        128
                    )
            else
                expressionEnds.Clear()

        lambdaParentheses.Clear()
        lambdaBrackets.Clear()
        childArena.Reset()

    member this.Reset() =
        this.ResetParsed()
        lexerBuffer.Reset()

    member this.ReleasePooledBuffers() =
        childArena.ReleasePooledBuffers()
        lexerBuffer.ReleasePooledBuffers()
        interpolationBuffer.ReleasePooledBuffers()
        inputTokens.ReleasePooledBuffers()
        PoolArray.release &nodes
        PoolArray.release &collectionConditionals
        PoolArray.release &children
        PoolArray.release &tokens
        PoolArray.release &dedicatedTrivia
        trivia <- dedicatedTrivia
        this.Reset()

    member internal _.Checkpoint() =
        struct (nodeCount,
                childCount,
                tokenCount,
                recoveredTokens,
                incompleteCount,
                childArena.Checkpoint())

    member internal _.Restore(struct (nodes, children, tokens, recovered, incomplete, arena)) =
        if ParseStats.enabled then
            ParseStats.bump ParseStats.nNodesDropped (nodeCount - nodes)
            ParseStats.bump ParseStats.nChildrenDropped (childCount - children)
            ParseStats.bump ParseStats.nTokensDropped (tokenCount - tokens)
            ParseStats.bump ParseStats.nArenaEntriesDropped (childArena.EntryCount - arena)

        nodeCount <- nodes
        childCount <- children
        tokenCount <- tokens
        recoveredTokens <- recovered
        incompleteCount <- incomplete
        childArena.Restore arena

    member internal _.ArenaCounts = struct (0, childArena.EntryCount)

    member _.RecoveredTokens = recoveredTokens

    member _.IsComplete = recoveredTokens = 0 && incompleteCount = 0

    member internal _.Recover() = recoveredTokens <- recoveredTokens + 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.AddNode(node: Node) =
        if nodeCount = nodes.Length then
            let nextLen = nodes.Length + 1
            PoolArray.grow &nodes nodeCount nextLen
            PoolArray.grow &collectionConditionals nodeCount nextLen

        if node.Kind = NodeKind.IncompleteMember then
            incompleteCount <- incompleteCount + 1

        let index = nodeCount
        nodes[index] <- node
        collectionConditionals[index] <- false
        nodeCount <- nodeCount + 1
        index

    member _.SetNode(index: int, node: Node) =
        if index < nodeCount then
            if nodes[index].Kind = NodeKind.IncompleteMember then
                incompleteCount <- incompleteCount - 1

            if node.Kind = NodeKind.IncompleteMember then
                incompleteCount <- incompleteCount + 1

        nodes[index] <- node

    member internal _.NodeStorage = nodes
    member internal _.ChildStorage = children
    member internal _.TokenStorage = tokens
    member internal _.TriviaStorage = trivia

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Node(index: int) = nodes[index]

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.AddChild(child: int32) =
        if childCount = children.Length then
            PoolArray.grow &children childCount (children.Length + 1)

        let index = childCount
        children[index] <- child
        childCount <- childCount + 1
        index

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal this.AddLeaf(kind: NodeKind, tokenStart: int, child: int) =
        let childStart = this.AddChild child

        if nodeCount = nodes.Length then
            let nextLen = nodes.Length + 1
            PoolArray.grow &nodes nodeCount nextLen
            PoolArray.grow &collectionConditionals nodeCount nextLen

        let index = nodeCount

        nodes[index] <-
            {
                Kind = kind
                Parent = -1
                ChildStart = childStart
                ChildCount = 1
                TokenStart = tokenStart
                TokenCount = tokenCount - tokenStart
            }

        collectionConditionals[index] <- false
        nodeCount <- nodeCount + 1
        index

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.Adopt(child: int, parent: int) =
        if child >= 0 then
            nodes[child].Parent <- parent
            collectionConditionals[child]
        else
            false

    member internal this.AddNode1(kind: NodeKind, tokenStart: int, only: int) =
        if childCount + 1 > children.Length then
            PoolArray.grow &children childCount (childCount + 1)

        if nodeCount = nodes.Length then
            let nextLen = nodes.Length + 1
            PoolArray.grow &nodes nodeCount nextLen
            PoolArray.grow &collectionConditionals nodeCount nextLen

        let index = nodeCount
        let childStart = childCount
        children[childStart] <- only
        childCount <- childStart + 1

        nodes[index] <-
            {
                Kind = kind
                Parent = -1
                ChildStart = childStart
                ChildCount = 1
                TokenStart = tokenStart
                TokenCount = tokenCount - tokenStart
            }

        collectionConditionals[index] <- this.Adopt(only, index)
        nodeCount <- index + 1
        index

    member internal this.AddNode2(kind: NodeKind, tokenStart: int, first: int, second: int) =
        if childCount + 2 > children.Length then
            PoolArray.grow &children childCount (childCount + 2)

        if nodeCount = nodes.Length then
            let nextLen = nodes.Length + 1
            PoolArray.grow &nodes nodeCount nextLen
            PoolArray.grow &collectionConditionals nodeCount nextLen

        let index = nodeCount
        let childStart = childCount
        children[childStart] <- first
        children[childStart + 1] <- second
        childCount <- childStart + 2

        nodes[index] <-
            {
                Kind = kind
                Parent = -1
                ChildStart = childStart
                ChildCount = 2
                TokenStart = tokenStart
                TokenCount = tokenCount - tokenStart
            }

        let conditional = this.Adopt(first, index)
        collectionConditionals[index] <- this.Adopt(second, index) || conditional
        nodeCount <- index + 1
        index

    member internal this.AddNode3
        (kind: NodeKind, tokenStart: int, first: int, second: int, third: int)
        =
        if childCount + 3 > children.Length then
            PoolArray.grow &children childCount (childCount + 3)

        if nodeCount = nodes.Length then
            let nextLen = nodes.Length + 1
            PoolArray.grow &nodes nodeCount nextLen
            PoolArray.grow &collectionConditionals nodeCount nextLen

        let index = nodeCount
        let childStart = childCount
        children[childStart] <- first
        children[childStart + 1] <- second
        children[childStart + 2] <- third
        childCount <- childStart + 3

        nodes[index] <-
            {
                Kind = kind
                Parent = -1
                ChildStart = childStart
                ChildCount = 3
                TokenStart = tokenStart
                TokenCount = tokenCount - tokenStart
            }

        let conditional = this.Adopt(first, index)
        let conditional = this.Adopt(second, index) || conditional
        collectionConditionals[index] <- this.Adopt(third, index) || conditional
        nodeCount <- index + 1
        index

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal _.AppendChildren(items: ChildList, parent: int) =
        let start = items.Start
        let finish = childArena.EntryCount
        let needed = childCount + (finish - start)

        if needed > children.Length then
            PoolArray.grow &children childCount needed

        let values = childArena.Values
        let mutable conditionals = false
        let mutable cursor = start
        let mutable written = childCount

        while cursor < finish do
            let child = values[cursor]
            children[written] <- child
            written <- written + 1

            if child >= 0 then
                conditionals <- conditionals || collectionConditionals[child]
                nodes[child].Parent <- parent

            cursor <- cursor + 1

        childCount <- written
        childArena.Release items.Start
        conditionals

    member internal this.MakeNode(kind: NodeKind, tokenStart: int, items: ChildList) =
        if nodeCount = nodes.Length then
            let nextLen = nodes.Length + 1
            PoolArray.grow &nodes nodeCount nextLen
            PoolArray.grow &collectionConditionals nodeCount nextLen

        if kind = NodeKind.IncompleteMember then
            incompleteCount <- incompleteCount + 1

        let index = nodeCount
        let start = items.Start
        let finish = childArena.EntryCount

        nodes[index] <-
            {
                Kind = kind
                Parent = -1
                ChildStart = childCount
                ChildCount = finish - start
                TokenStart = tokenStart
                TokenCount = tokenCount - tokenStart
            }

        nodeCount <- index + 1
        collectionConditionals[index] <- this.AppendChildren(items, index)
        index

    member _.SetChild(index: int, child: int32) = children[index] <- child

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Child(index: int) = children[index]

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.AddToken(token: Token) =
        if tokenCount = tokens.Length then
            PoolArray.grow &tokens tokenCount (tokens.Length + 1)

        if token.Length <= 0 || token.Kind = TokenKind.BadToken then
            if isIncompleteToken token then
                incompleteCount <- incompleteCount + 1

        let index = tokenCount
        tokens[index] <- token
        tokenCount <- tokenCount + 1
        index

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member internal _.AddTokenRef(token: inref<Token>) =
        if tokenCount = tokens.Length then
            PoolArray.grow &tokens tokenCount (tokens.Length + 1)

        if inputMayHoldIncomplete && (token.Length <= 0 || token.Kind = TokenKind.BadToken) then
            if isIncompleteToken token then
                incompleteCount <- incompleteCount + 1

        let index = tokenCount

        Unsafe.CopyBlockUnaligned(
            &Unsafe.As<Token, byte>(&tokens[index]),
            &Unsafe.As<Token, byte>(&Unsafe.AsRef(&token)),
            uint32 sizeof<Token>
        )

        tokenCount <- tokenCount + 1
        index

    member _.SetToken(index: int, token: Token) =
        if index < tokenCount then
            if isIncompleteToken tokens[index] then
                incompleteCount <- incompleteCount - 1

            if isIncompleteToken token then
                incompleteCount <- incompleteCount + 1

        tokens[index] <- token

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Token(index: int) = tokens[index]

    member _.AddTrivia(item: Trivia) =
        if item.Kind = TriviaKind.IfDirectiveTrivia then
            hasIfDirective <- true

        if
            obj.ReferenceEquals(trivia, lexerBuffer.TriviaStorage)
            && triviaCount >= lexerBuffer.TriviaCount
        then
            if triviaCount = trivia.Length then
                lexerBuffer.ResizeTrivia(triviaCount, max 64 (trivia.Length * 2))
                trivia <- lexerBuffer.TriviaStorage
        else if obj.ReferenceEquals(trivia, lexerBuffer.TriviaStorage) then
            if triviaCount + 1 > dedicatedTrivia.Length then
                PoolArray.grow &dedicatedTrivia 0 (triviaCount + 1)

            trivia.AsSpan(0, triviaCount).CopyTo(dedicatedTrivia.AsSpan(0, triviaCount))
            trivia <- dedicatedTrivia
        elif triviaCount = dedicatedTrivia.Length then
            PoolArray.grow &dedicatedTrivia triviaCount (triviaCount + 1)
            trivia <- dedicatedTrivia

        let index = triviaCount
        trivia[index] <- item
        triviaCount <- triviaCount + 1
        index

    member internal _.PrepareForParse(inputTokenCount: int) =
        childArena.EnsureCapacity(inputTokenCount >>> 2)
        let nodeEstimate = min 524288 ((inputTokenCount * 3 >>> 2) + 64)

        if nodeCount = 0 && nodeEstimate > nodes.Length then
            PoolArray.grow &nodes 0 nodeEstimate
            PoolArray.grow &collectionConditionals 0 nodeEstimate

        let childEstimate = inputTokenCount * 2 + (inputTokenCount >>> 3) + 128

        if childCount = 0 && childEstimate > children.Length then
            PoolArray.grow &children 0 childEstimate

        let tokenEstimate = inputTokenCount + 128

        if tokenCount = 0 && tokenEstimate > tokens.Length then
            PoolArray.grow &tokens 0 tokenEstimate

    member _.CopyLexicalTrivia() =
        let span = lexerBuffer.TriviaSpan()

        if triviaCount = 0 then
            trivia <- lexerBuffer.TriviaStorage
            triviaCount <- span.Length
        elif span.Length > 0 then
            let needed = triviaCount + span.Length

            if obj.ReferenceEquals(trivia, lexerBuffer.TriviaStorage) then
                if needed > dedicatedTrivia.Length then
                    PoolArray.grow &dedicatedTrivia 0 needed

                trivia.AsSpan(0, triviaCount).CopyTo(dedicatedTrivia.AsSpan(0, triviaCount))
                trivia <- dedicatedTrivia
            elif needed > dedicatedTrivia.Length then
                PoolArray.grow &dedicatedTrivia triviaCount needed
                trivia <- dedicatedTrivia

            span.CopyTo(trivia.AsSpan(triviaCount, span.Length))
            triviaCount <- needed

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.Trivia(index: int) = trivia[index]

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.NodeSpan() = ReadOnlySpan<Node>(nodes, 0, nodeCount)

    member _.ChildMemory(index: int) =
        let node = &nodes[index]
        ReadOnlyMemory<int>(children, node.ChildStart, node.ChildCount)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.ChildRange(index: int) =
        let node = &nodes[index]
        struct (children, node.ChildStart, node.ChildCount)

    member inline this.NodeKind(index: int) : NodeKind =
        let span = this.NodeSpan()
        span[index].Kind

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.ChildSpan() =
        ReadOnlySpan<int32>(children, 0, childCount)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.TokenSpan() =
        ReadOnlySpan<Token>(tokens, 0, tokenCount)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member _.TriviaSpan() =
        ReadOnlySpan<Trivia>(trivia, 0, triviaCount)

    member _.SourceSpan(index: int) =
        let node = &nodes[index]

        if node.TokenCount > 0 then
            let first = &tokens[node.TokenStart]
            let last = &tokens[node.TokenStart + node.TokenCount - 1]
            struct (first.Start, last.End - first.Start)
        elif node.TokenStart < tokenCount then
            struct (tokens[node.TokenStart].Start, 0)
        elif tokenCount > 0 then
            struct (tokens[tokenCount - 1].End, 0)
        else
            struct (0, 0)
