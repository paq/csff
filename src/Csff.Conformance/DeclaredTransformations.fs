namespace Csff.Conformance

open System
open System.Buffers
open System.Collections.Generic
open System.Text
open System.Threading
open Csff.Lexer
open Csff.Parser
open Csff.Printer

module DeclaredTransformations =

    [<NoComparison; NoEquality>]
    type Rule =
        {
            Name: string
            Witnessed: TransformationWitness -> bool
            RewriteInput: PrinterOptions -> string -> string -> string
        }

    module Census =
        let enabled = Environment.GetEnvironmentVariable "CSFF_ROSLYNSTATS" = "1"
        let mutable interpolationEntries = 0L
        let mutable interpolationRoslynParses = 0L
        let mutable interpolationHoleScans = 0L
        let mutable lineEndingEntries = 0L
        let mutable lineEndingRoslynParses = 0L
        let mutable lineEndingPieceScans = 0L
        let mutable uncertainSegmentations = 0L

        let inline bump (slot: byref<int64>) = Interlocked.Increment(&slot) |> ignore

        let report () =
            String.Format(
                "roslynstats interpolation entries={0} roslyn={1} holes={2}",
                interpolationEntries,
                interpolationRoslynParses,
                interpolationHoleScans
            )
            + String.Format(
                " | line-endings entries={0} roslyn={1} scans={2}",
                lineEndingEntries,
                lineEndingRoslynParses,
                lineEndingPieceScans
            )
            + String.Format(" | uncertain={0}", uncertainSegmentations)

    let private deferredProofMarker = String([| '\u0000' |])

    [<NoComparison; NoEquality>]
    type private PairCache =
        {
            Before: TokenBuffer
            After: TokenBuffer
            OwnBeforeTree: SyntaxTree
            OwnAfterTree: SyntaxTree
            Stack: Stack<int>
            BeforeDecls: ResizeArray<int>
            AfterDecls: ResizeArray<int>
            mutable Closings: Dictionary<int, struct (int * bool * bool)>
            ProofEdits: ResizeArray<int * int * string>
            ProofDropped: ResizeArray<int>
            ProofAdded: ResizeArray<int>
            ProofClosings: ResizeArray<int>
            mutable DeferSeparatorProof: bool
            mutable ProofFromTree: bool
            mutable ProofSource: string
            mutable ProofRewrite: string
            mutable SeededBeforeTree: SyntaxTree
            mutable OwnedBeforeTree: SyntaxTree
            mutable SeededAfterTree: SyntaxTree
            mutable LastSource: string
            mutable LastFormatted: string
            mutable LastParseSource: string
            mutable LastParseFormatted: string
            mutable SeededSymbols: string array
            mutable LastRewriteSource: string
            LastRewriteEdits: ResizeArray<int * int * string>
            mutable LastRewriteResult: string
            mutable ChainOrigin: string
            ChainVariants: ResizeArray<string>
            mutable HoleTree: SyntaxTree
        }

    let private maxCachedStringLength = 262144

    let private pairCache =
        new ThreadLocal<PairCache>(fun () ->
            {
                Before = TokenBuffer()
                After = TokenBuffer()
                OwnBeforeTree = SyntaxTree()
                OwnAfterTree = SyntaxTree()
                Stack = Stack<int>()
                BeforeDecls = ResizeArray<int>()
                AfterDecls = ResizeArray<int>()
                Closings = Dictionary<int, struct (int * bool * bool)>()
                ProofEdits = ResizeArray<int * int * string>()
                ProofDropped = ResizeArray<int>()
                ProofAdded = ResizeArray<int>()
                ProofClosings = ResizeArray<int>()
                DeferSeparatorProof = false
                ProofFromTree = false
                ProofSource = null
                ProofRewrite = null
                SeededBeforeTree = Unchecked.defaultof<SyntaxTree>
                OwnedBeforeTree = Unchecked.defaultof<SyntaxTree>
                SeededAfterTree = Unchecked.defaultof<SyntaxTree>
                LastSource = null
                LastFormatted = null
                LastParseSource = null
                LastParseFormatted = null
                SeededSymbols = Array.empty
                LastRewriteSource = null
                LastRewriteEdits = ResizeArray<int * int * string>()
                LastRewriteResult = null
                ChainOrigin = null
                ChainVariants = ResizeArray<string>()
                HoleTree = Unchecked.defaultof<SyntaxTree>
            })

    let private inChainVariants (state: PairCache) (text: string) =
        let mutable i = 0
        let mutable found = false

        while not found && i < state.ChainVariants.Count do
            if Object.ReferenceEquals(state.ChainVariants[i], text) then
                found <- true

            i <- i + 1

        found

    let private recordChainVariant (state: PairCache) (source: string) (rewritten: string) =
        if
            not (isNull state.ChainOrigin)
            && not (isNull rewritten)
            && not (Object.ReferenceEquals(source, rewritten))
            && inChainVariants state source
            && not (inChainVariants state rewritten)
        then
            state.ChainVariants.Add rewritten

    let internal tryChainOrigin (text: string) =
        if isNull text then
            ValueNone
        else
            let state = pairCache.Value

            if not (isNull state.ChainOrigin) && inChainVariants state text then
                ValueSome state.ChainOrigin
            else
                ValueNone

    let internal clearRewriteChain () =
        let state = pairCache.Value
        state.ChainOrigin <- null
        state.ChainVariants.Clear()

    let internal rewrite (source: string) (edits: ResizeArray<int * int * string>) =
        if edits.Count = 0 then
            source
        else
            let state = pairCache.Value

            let sameAsLast =
                Object.ReferenceEquals(source, state.LastRewriteSource)
                && edits.Count = state.LastRewriteEdits.Count
                && (let mutable same = true
                    let mutable k = 0

                    while same && k < edits.Count do
                        let (o1, l1, r1) = edits[k]
                        let (o2, l2, r2) = state.LastRewriteEdits[k]

                        same <-
                            o1 = o2 && l1 = l2 && String.Equals(r1, r2, StringComparison.Ordinal)

                        k <- k + 1

                    same)

            if sameAsLast then
                recordChainVariant state source state.LastRewriteResult
                state.LastRewriteResult
            else
                let mutable total = source.Length

                for _, length, replacement in edits do
                    total <- total - length + replacement.Length

                let buffer = ArrayPool<char>.Shared.Rent total

                try
                    let mutable start = 0
                    let mutable cursor = 0

                    for offset, length, replacement in edits do
                        source.AsSpan(start, offset - start).CopyTo(buffer.AsSpan cursor)
                        cursor <- cursor + offset - start
                        replacement.AsSpan().CopyTo(buffer.AsSpan cursor)
                        cursor <- cursor + replacement.Length
                        start <- offset + length

                    source.AsSpan(start).CopyTo(buffer.AsSpan cursor)
                    cursor <- cursor + source.Length - start
                    let rewritten = String(ReadOnlySpan<char>(buffer, 0, cursor))
                    state.LastRewriteSource <- source
                    state.LastRewriteEdits.Clear()
                    state.LastRewriteEdits.AddRange edits
                    state.LastRewriteResult <- rewritten
                    recordChainVariant state source rewritten
                    rewritten
                finally
                    ArrayPool<char>.Shared.Return buffer

    let internal seedParsedPairWith
        (symbols: string array)
        (source: string)
        (before: SyntaxTree)
        (ownedBefore: SyntaxTree)
        (formatted: string)
        (after: SyntaxTree)
        (deferSeparatorProof: bool)
        =
        let state = pairCache.Value
        state.SeededBeforeTree <- before
        state.OwnedBeforeTree <- ownedBefore
        state.SeededAfterTree <- after
        state.LastParseSource <- source
        state.LastParseFormatted <- formatted
        state.SeededSymbols <- symbols
        state.DeferSeparatorProof <- deferSeparatorProof
        state.ChainOrigin <- source
        state.ChainVariants.Clear()

        if not (isNull source) then
            state.ChainVariants.Add source

    let internal seedParsedPair
        (source: string)
        (before: SyntaxTree)
        (formatted: string)
        (after: SyntaxTree)
        (deferSeparatorProof: bool)
        =
        seedParsedPairWith Array.empty source before before formatted after deferSeparatorProof

    let internal clearSeededPair () =
        let state = pairCache.Value
        state.SeededBeforeTree <- Unchecked.defaultof<SyntaxTree>
        state.OwnedBeforeTree <- Unchecked.defaultof<SyntaxTree>
        state.SeededAfterTree <- Unchecked.defaultof<SyntaxTree>
        state.LastParseSource <- null
        state.LastParseFormatted <- null
        state.SeededSymbols <- Array.empty
        state.DeferSeparatorProof <- false
        state.ProofSource <- null
        state.ProofRewrite <- null

    let internal isSeededBefore (tree: SyntaxTree) =
        Object.ReferenceEquals(tree, pairCache.Value.SeededBeforeTree)

    let internal isParsedInSeededBefore (source: string) (before: SyntaxTree) =
        let state = pairCache.Value

        let parsed =
            Object.ReferenceEquals(before, state.SeededBeforeTree)
            && Object.ReferenceEquals(source, state.LastParseSource)

        parsed

    let internal tryTakeSeparatorProof
        (rewritten: string)
        (before: SyntaxTree)
        (dropped: HashSet<int>)
        (added: HashSet<int>)
        (closings: HashSet<int>)
        (edits: ResizeArray<int * int * string>)
        =
        let state = pairCache.Value

        if
            not (isNull state.ProofSource)
            && Object.ReferenceEquals(rewritten, state.ProofRewrite)
            && isParsedInSeededBefore state.ProofSource before
        then
            dropped.Clear()
            added.Clear()
            closings.Clear()
            edits.Clear()

            for index = 0 to state.ProofDropped.Count - 1 do
                dropped.Add state.ProofDropped[index] |> ignore

            for index = 0 to state.ProofAdded.Count - 1 do
                added.Add state.ProofAdded[index] |> ignore

            for index = 0 to state.ProofClosings.Count - 1 do
                closings.Add state.ProofClosings[index] |> ignore

            for index = 0 to state.ProofEdits.Count - 1 do
                edits.Add state.ProofEdits[index]

            state.ProofSource
        else
            null

    let private lexPair (source: string) (formatted: string) =
        let state = pairCache.Value
        let seeded = not (isNull (box state.SeededBeforeTree))

        let before =
            if seeded && Object.ReferenceEquals(source, state.LastParseSource) then
                state.SeededBeforeTree.LexerBuffer
            elif seeded then
                state.LastParseSource <- null

                if not (isNull (box state.OwnedBeforeTree)) then
                    state.SeededBeforeTree <- state.OwnedBeforeTree

                if state.SeededSymbols.Length > 0 then
                    Parser.parseWith state.SeededSymbols source state.SeededBeforeTree
                else
                    Parser.parse source state.SeededBeforeTree

                state.LastParseSource <- source
                state.SeededBeforeTree.LexerBuffer
            else
                if not (Object.ReferenceEquals(source, state.LastSource)) then
                    state.LastSource <- null
                    Lexer.lex source state.Before

                    if source.Length <= maxCachedStringLength then
                        state.LastSource <- source

                state.Before

        let after =
            if
                not (isNull (box state.SeededAfterTree))
                && Object.ReferenceEquals(formatted, state.LastParseFormatted)
            then
                state.SeededAfterTree.LexerBuffer
            else
                if not (Object.ReferenceEquals(formatted, state.LastFormatted)) then
                    state.LastFormatted <- null
                    Lexer.lex formatted state.After

                    if formatted.Length <= maxCachedStringLength then
                        state.LastFormatted <- formatted

                state.After

        struct (before, after)

    let private parsePair (source: string) (formatted: string) =
        let state = pairCache.Value

        if
            not (isNull (box state.SeededBeforeTree))
            && not (isNull (box state.SeededAfterTree))
        then
            if not (Object.ReferenceEquals(source, state.LastParseSource)) then
                state.LastParseSource <- null

                if not (isNull (box state.OwnedBeforeTree)) then
                    state.SeededBeforeTree <- state.OwnedBeforeTree

                if state.SeededSymbols.Length > 0 then
                    Parser.parseWith state.SeededSymbols source state.SeededBeforeTree
                else
                    Parser.parse source state.SeededBeforeTree

                state.LastParseSource <- source

            if not (Object.ReferenceEquals(formatted, state.LastParseFormatted)) then
                state.LastParseFormatted <- null

                if state.SeededSymbols.Length > 0 then
                    Parser.parseWith state.SeededSymbols formatted state.SeededAfterTree
                else
                    Parser.parse formatted state.SeededAfterTree

                state.LastParseFormatted <- formatted

            struct (state.SeededBeforeTree, state.SeededAfterTree)
        else
            Parser.parse source state.OwnBeforeTree
            Parser.parse formatted state.OwnAfterTree
            struct (state.OwnBeforeTree, state.OwnAfterTree)

    let private hasSubstringTwice (text: string) (value: string) =
        let first = text.IndexOf(value, StringComparison.Ordinal)

        first >= 0
        && text.IndexOf(value, first + value.Length, StringComparison.Ordinal) >= 0

    let inline private hasAmbiguousTrivia (buffer: TokenBuffer) =
        buffer.HasDisabledText || buffer.HasMalformedTrivia

    let internal hasMalformedTrivia (buffer: TokenBuffer) = buffer.HasMalformedTrivia

    let private hasMalformedTriviaSpan (span: ReadOnlySpan<Trivia>) =
        let mutable index = 0
        let mutable malformed = false

        while not malformed && index < span.Length do
            match span[index].Kind with
            | TriviaKind.SkippedTokensTrivia
            | TriviaKind.BadDirectiveTrivia
            | TriviaKind.ConflictMarkerTrivia -> malformed <- true
            | _ -> index <- index + 1

        malformed

    let inline private isLexicalModifier (source: string) (token: Token) =
        match token.Kind with
        | TokenKind.PublicKeyword
        | TokenKind.PrivateKeyword
        | TokenKind.ProtectedKeyword
        | TokenKind.InternalKeyword
        | TokenKind.StaticKeyword
        | TokenKind.ReadOnlyKeyword
        | TokenKind.VolatileKeyword
        | TokenKind.VirtualKeyword
        | TokenKind.SealedKeyword
        | TokenKind.OverrideKeyword
        | TokenKind.AbstractKeyword
        | TokenKind.ExternKeyword
        | TokenKind.UnsafeKeyword
        | TokenKind.NewKeyword
        | TokenKind.FixedKeyword -> true
        | TokenKind.IdentifierToken when token.Length >= 4 && token.Length <= 8 ->
            let span = source.AsSpan(token.Start, token.Length)

            span.SequenceEqual("async".AsSpan())
            || span.SequenceEqual("partial".AsSpan())
            || span.SequenceEqual("required".AsSpan())
            || span.SequenceEqual("file".AsSpan())
        | _ -> false

    let private canSkipModifierPermutation (source: string) (formatted: string) =
        let struct (before, after) = lexPair source formatted

        if hasAmbiguousTrivia before || hasAmbiguousTrivia after then
            false
        else
            let mutable hasAdjacentPair = false
            let mutable prevModifier = false

            for idx = 0 to before.TokenCount - 1 do
                let isMod = isLexicalModifier source (before.Token idx)

                if prevModifier && isMod then
                    hasAdjacentPair <- true

                prevModifier <- isMod

            let mutable i = 0
            let mutable j = 0
            let mutable sameNonCommaTokens = true
            let mutable sameModifiersAndInterpolations = true

            while (not hasAdjacentPair || (sameNonCommaTokens && sameModifiersAndInterpolations))
                  && (i < before.TokenCount || j < after.TokenCount) do
                if i < before.TokenCount && (before.Token i).Kind = TokenKind.CommaToken then
                    i <- i + 1
                elif j < after.TokenCount && (after.Token j).Kind = TokenKind.CommaToken then
                    j <- j + 1
                elif i < before.TokenCount && j < after.TokenCount then
                    let left = before.Token i
                    let right = after.Token j

                    if left.Kind <> right.Kind then
                        sameNonCommaTokens <- false

                    if left.Kind = TokenKind.InterpolatedStringToken then
                        if
                            right.Kind <> TokenKind.InterpolatedStringToken
                            || left.Length <> right.Length
                            || not (
                                source
                                    .AsSpan(left.Start, left.Length)
                                    .SequenceEqual(formatted.AsSpan(right.Start, right.Length))
                            )
                        then
                            sameModifiersAndInterpolations <- false
                            hasAdjacentPair <- true
                    elif
                        (left.Kind <> right.Kind || left.Kind = TokenKind.IdentifierToken)
                        && (isLexicalModifier source left || isLexicalModifier formatted right)
                    then
                        if
                            left.Length <> right.Length
                            || not (
                                source
                                    .AsSpan(left.Start, left.Length)
                                    .SequenceEqual(formatted.AsSpan(right.Start, right.Length))
                            )
                        then
                            sameModifiersAndInterpolations <- false

                    i <- i + 1
                    j <- j + 1
                else
                    sameNonCommaTokens <- false

                    if i < before.TokenCount then
                        if (before.Token i).Kind = TokenKind.InterpolatedStringToken then
                            hasAdjacentPair <- true

                        i <- i + 1

                    if j < after.TokenCount then
                        if (after.Token j).Kind = TokenKind.InterpolatedStringToken then
                            hasAdjacentPair <- true

                        j <- j + 1

            not hasAdjacentPair || (sameNonCommaTokens && sameModifiersAndInterpolations)

    let inline internal isSortableDeclarationKind (kind: NodeKind) =
        match kind with
        | NodeKind.GlobalStatement
        | NodeKind.NamespaceDeclaration
        | NodeKind.FileScopedNamespaceDeclaration
        | NodeKind.ClassDeclaration
        | NodeKind.StructDeclaration
        | NodeKind.InterfaceDeclaration
        | NodeKind.EnumDeclaration
        | NodeKind.DelegateDeclaration
        | NodeKind.EnumMemberDeclaration
        | NodeKind.FieldDeclaration
        | NodeKind.EventFieldDeclaration
        | NodeKind.MethodDeclaration
        | NodeKind.OperatorDeclaration
        | NodeKind.ConversionOperatorDeclaration
        | NodeKind.ConstructorDeclaration
        | NodeKind.DestructorDeclaration
        | NodeKind.PropertyDeclaration
        | NodeKind.EventDeclaration
        | NodeKind.IndexerDeclaration
        | NodeKind.GetAccessorDeclaration
        | NodeKind.SetAccessorDeclaration
        | NodeKind.AddAccessorDeclaration
        | NodeKind.RemoveAccessorDeclaration
        | NodeKind.UnknownAccessorDeclaration
        | NodeKind.InitAccessorDeclaration
        | NodeKind.LocalFunctionStatement
        | NodeKind.IncompleteMember
        | NodeKind.RecordDeclaration
        | NodeKind.RecordStructDeclaration
        | NodeKind.ExtensionBlockDeclaration
        | NodeKind.UnionDeclaration -> true
        | _ -> false

    let internal isTypeDeclarationKind (kind: NodeKind) =
        match kind with
        | NodeKind.ClassDeclaration
        | NodeKind.StructDeclaration
        | NodeKind.InterfaceDeclaration
        | NodeKind.RecordDeclaration
        | NodeKind.RecordStructDeclaration
        | NodeKind.EnumDeclaration
        | NodeKind.DelegateDeclaration
        | NodeKind.UnionDeclaration -> true
        | _ -> false

    let internal isModifierTokenKind (kind: TokenKind) =
        match kind with
        | TokenKind.PublicKeyword
        | TokenKind.PrivateKeyword
        | TokenKind.ProtectedKeyword
        | TokenKind.InternalKeyword
        | TokenKind.StaticKeyword
        | TokenKind.ReadOnlyKeyword
        | TokenKind.VolatileKeyword
        | TokenKind.VirtualKeyword
        | TokenKind.SealedKeyword
        | TokenKind.OverrideKeyword
        | TokenKind.AbstractKeyword
        | TokenKind.ExternKeyword
        | TokenKind.AsyncKeyword
        | TokenKind.UnsafeKeyword
        | TokenKind.PartialKeyword
        | TokenKind.NewKeyword
        | TokenKind.RequiredKeyword
        | TokenKind.FileKeyword
        | TokenKind.FixedKeyword -> true
        | _ -> false

    let internal isPositionIndependentModifier (kind: TokenKind) =
        match kind with
        | TokenKind.PublicKeyword
        | TokenKind.PrivateKeyword
        | TokenKind.ProtectedKeyword
        | TokenKind.InternalKeyword
        | TokenKind.StaticKeyword
        | TokenKind.ReadOnlyKeyword
        | TokenKind.VolatileKeyword
        | TokenKind.VirtualKeyword
        | TokenKind.SealedKeyword
        | TokenKind.OverrideKeyword
        | TokenKind.AbstractKeyword
        | TokenKind.ExternKeyword
        | TokenKind.UnsafeKeyword
        | TokenKind.NewKeyword -> true
        | _ -> false

    let private collectSortableDeclarations
        (tree: SyntaxTree)
        (stack: Stack<int>)
        (result: ResizeArray<int>)
        =
        result.Clear()
        stack.Clear()

        if tree.RootIndex >= 0 then
            stack.Push tree.RootIndex

            while stack.Count > 0 do
                let nodeIndex = stack.Pop()
                let node = tree.Node nodeIndex

                if isSortableDeclarationKind node.Kind then
                    result.Add nodeIndex

                for slot = node.ChildCount - 1 downto 0 do
                    let child = tree.Child(node.ChildStart + slot)

                    if child >= 0 then
                        stack.Push child

    let internal leadingModifierSlice (tree: SyntaxTree) (node: Node) =
        let mutable slot = 0

        while slot < node.ChildCount
              && (let child = tree.Child(node.ChildStart + slot) in
                  child >= 0 && (tree.Node child).Kind = NodeKind.AttributeList) do
            slot <- slot + 1

        let startSlot = slot

        while slot < node.ChildCount
              && (let child = tree.Child(node.ChildStart + slot) in
                  child < 0 && isModifierTokenKind (tree.Token ~~~child).Kind) do
            slot <- slot + 1

        struct (node.ChildStart + startSlot, slot - startSlot)

    let private isLayoutTrivia (kind: TriviaKind) =
        kind = TriviaKind.WhitespaceTrivia || kind = TriviaKind.EndOfLineTrivia

    let private modifierPermutationFromTree
        (source: string)
        (before: SyntaxTree)
        (formatted: string)
        (after: SyntaxTree)
        =
        if
            not before.IsComplete
            || not after.IsComplete
            || hasMalformedTrivia before.LexerBuffer
            || hasMalformedTrivia after.LexerBuffer
        then
            source
        else
            let state = pairCache.Value
            let beforeDecls = state.BeforeDecls
            let afterDecls = state.AfterDecls
            collectSortableDeclarations before state.Stack beforeDecls
            collectSortableDeclarations after state.Stack afterDecls
            let mutable edits = Unchecked.defaultof<ResizeArray<int * int * string>>
            let mutable valid = beforeDecls.Count = afterDecls.Count
            let mutable declined = not valid
            let mutable index = 0

            let boundaryComments (left: Token) (right: Token) =
                let mutable i = left.TriviaStart
                let leftEnd = left.TriviaStart + left.LeadingCount
                let mutable j = right.TriviaStart
                let rightEnd = right.TriviaStart + right.LeadingCount
                let mutable ok = true

                while ok && (i < leftEnd || j < rightEnd) do
                    while i < leftEnd && isLayoutTrivia (before.Trivia i).Kind do
                        i <- i + 1

                    while j < rightEnd && isLayoutTrivia (after.Trivia j).Kind do
                        j <- j + 1

                    if i < leftEnd && j < rightEnd then
                        let leftTrivia = before.Trivia i
                        let rightTrivia = after.Trivia j

                        ok <-
                            leftTrivia.Kind = rightTrivia.Kind
                            && (leftTrivia.Kind = TriviaKind.SingleLineCommentTrivia
                                || leftTrivia.Kind = TriviaKind.MultiLineCommentTrivia
                                || leftTrivia.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                                || leftTrivia.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                            && CommentContent.equivalent source leftTrivia formatted rightTrivia

                        i <- i + 1
                        j <- j + 1
                    elif i < leftEnd || j < rightEnd then
                        ok <- false

                ok

            let interiorTrivia (kind: TriviaKind) =
                isLayoutTrivia kind
                || kind = TriviaKind.SingleLineCommentTrivia
                || kind = TriviaKind.MultiLineCommentTrivia

            let plainRemainder (tree: SyntaxTree) (childStart: int) (count: int) =
                let mutable ok = true
                let mutable slot = 0

                while ok && slot < count do
                    let token = tree.Token ~~~(tree.Child(childStart + slot))

                    if slot > 0 then
                        for t = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                            if not (interiorTrivia (tree.Trivia t).Kind) then
                                ok <- false

                    let trailingStart = token.TriviaStart + token.LeadingCount

                    for t = trailingStart to trailingStart + token.TrailingCount - 1 do
                        if not (interiorTrivia (tree.Trivia t).Kind) then
                            ok <- false

                    slot <- slot + 1

                ok

            while valid && not declined && index < beforeDecls.Count do
                let beforeNode = before.Node beforeDecls[index]
                let afterNode = after.Node afterDecls[index]
                let struct (beforeStart, beforeCount) = leadingModifierSlice before beforeNode
                let struct (afterStart, afterCount) = leadingModifierSlice after afterNode

                let unpromotedLocalModifier =
                    beforeNode.Kind = NodeKind.LocalFunctionStatement
                    && ((beforeStart + beforeCount < beforeNode.ChildStart + beforeNode.ChildCount
                         && before.Child(beforeStart + beforeCount) < 0)
                        || (afterStart + afterCount < afterNode.ChildStart + afterNode.ChildCount
                            && after.Child(afterStart + afterCount) < 0))

                if
                    beforeNode.Kind <> afterNode.Kind
                    || beforeCount <> afterCount
                    || unpromotedLocalModifier
                then
                    declined <- true
                    valid <- false

                if valid && beforeCount >= 2 then
                    let mutable allSame = true
                    let mutable slot = 0

                    while allSame && slot < beforeCount do
                        let left = before.Token ~~~(before.Child(beforeStart + slot))
                        let right = after.Token ~~~(after.Child(afterStart + slot))

                        allSame <-
                            left.Length = right.Length
                            && source
                                .AsSpan(left.Start, left.Length)
                                .SequenceEqual(formatted.AsSpan(right.Start, right.Length))

                        slot <- slot + 1

                    if not allSame then
                        let isLocal = beforeNode.Kind = NodeKind.LocalFunctionStatement

                        let parentKind =
                            if beforeNode.Parent >= 0 then
                                (before.Node beforeNode.Parent).Kind
                            else
                                NodeKind.None

                        if
                            isLocal
                            && parentKind <> NodeKind.Block
                            && parentKind <> NodeKind.GlobalStatement
                        then
                            declined <- true

                        let isTypeDecl = isTypeDeclarationKind beforeNode.Kind

                        let struct (runCarriesStationaryWord, runCarriesPartial) =
                            let plain (kind: TokenKind) =
                                isPositionIndependentModifier kind || kind = TokenKind.AsyncKeyword

                            let mutable found = false
                            let mutable partial = false

                            for t = 0 to beforeCount - 1 do
                                let bt = before.Token ~~~(before.Child(beforeStart + t))
                                let at = after.Token ~~~(after.Child(afterStart + t))

                                if not (plain bt.Kind) || not (plain at.Kind) then
                                    found <- true

                                if
                                    bt.Kind = TokenKind.PartialKeyword
                                    || at.Kind = TokenKind.PartialKeyword
                                then
                                    partial <- true

                            struct (found, partial)

                        for s = 0 to beforeCount - 1 do
                            let bTok = before.Token ~~~(before.Child(beforeStart + s))
                            let aTok = after.Token ~~~(after.Child(afterStart + s))

                            if
                                isTypeDecl
                                && (bTok.Kind = TokenKind.ExternKeyword
                                    || aTok.Kind = TokenKind.ExternKeyword)
                            then
                                declined <- true

                            if isLocal then
                                let permitted (kind: TokenKind) =
                                    kind = TokenKind.AsyncKeyword
                                    || kind = TokenKind.StaticKeyword
                                    || kind = TokenKind.UnsafeKeyword
                                    || kind = TokenKind.ExternKeyword

                                if not (permitted bTok.Kind && permitted aTok.Kind) then
                                    declined <- true
                            elif bTok.Kind = aTok.Kind && s = beforeCount - 1 then
                                ()
                            else
                                let asyncMovable =
                                    beforeNode.Kind = NodeKind.MethodDeclaration
                                    && not runCarriesStationaryWord

                                let fileMovable = isTypeDecl && not runCarriesPartial

                                let movable (kind: TokenKind) =
                                    isPositionIndependentModifier kind
                                    || (kind = TokenKind.AsyncKeyword && asyncMovable)
                                    || (kind = TokenKind.FileKeyword && fileMovable)

                                if not (movable bTok.Kind && movable aTok.Kind) then
                                    declined <- true

                        let keys (text: string) (tree: SyntaxTree) (childStart: int) =
                            let arr = Array.zeroCreate<struct (int * string)> beforeCount

                            for s = 0 to beforeCount - 1 do
                                let tok = tree.Token ~~~(tree.Child(childStart + s))

                                arr[s] <-
                                    struct (int tok.Kind, text.Substring(tok.Start, tok.Length))

                            Array.sortInPlace arr
                            arr

                        let firstBefore = before.Token ~~~(before.Child beforeStart)
                        let firstAfter = after.Token ~~~(after.Child afterStart)
                        let commentsOk = boundaryComments firstBefore firstAfter

                        if not declined then
                            valid <-
                                commentsOk
                                && keys source before beforeStart = keys formatted after afterStart
                                && plainRemainder before beforeStart beforeCount
                                && plainRemainder after afterStart afterCount

                            if valid then
                                if isNull (box edits) then
                                    edits <- ResizeArray<int * int * string>()

                                for s = 0 to beforeCount - 1 do
                                    let left = before.Token ~~~(before.Child(beforeStart + s))
                                    let right = after.Token ~~~(after.Child(afterStart + s))

                                    if
                                        left.Length <> right.Length
                                        || not (
                                            source
                                                .AsSpan(left.Start, left.Length)
                                                .SequenceEqual(
                                                    formatted.AsSpan(right.Start, right.Length)
                                                )
                                        )
                                    then
                                        edits.Add(
                                            left.Start,
                                            left.Length,
                                            formatted.Substring(right.Start, right.Length)
                                        )

                index <- index + 1

            if not declined && valid && not (isNull (box edits)) && edits.Count > 0 then
                edits.Sort(fun (a, _, _) (b, _, _) -> compare a b)
                rewrite source edits
            else
                source

    let private modifierPermutation (source: string) (formatted: string) =
        if canSkipModifierPermutation source formatted then
            source
        else
            let struct (before, after) = parsePair source formatted

            modifierPermutationFromTree source before formatted after

    let private validExpressionColonTarget
        (nodes: ReadOnlySpan<Node>, children: ReadOnlySpan<int32>, idx: int)
        =
        let mutable current = idx
        let mutable valid = false
        let mutable searching = current >= 0

        while searching do
            let n = &nodes[current]

            match n.Kind with
            | NodeKind.IdentifierName
            | NodeKind.GenericName ->
                valid <- true
                searching <- false
            | NodeKind.SimpleMemberAccessExpression when n.ChildCount >= 1 ->
                let first = children[n.ChildStart]

                if first >= 0 then current <- first else searching <- false
            | _ -> searching <- false

        valid

    let private addClosing
        (
            node: inref<Node>,
            children: ReadOnlySpan<int32>,
            tokens: ReadOnlySpan<Token>,
            nodes: ReadOnlySpan<Node>,
            closings: Dictionary<int, struct (int * bool * bool)>,
            openKind: TokenKind,
            closeKind: TokenKind,
            insert: bool,
            remove: bool,
            minClosingStart: int
        ) =
        let childStart = node.ChildStart
        let childCount = node.ChildCount
        let mutable closeSlot = -1
        let mutable s = childCount - 1

        while closeSlot < 0 && s >= 2 do
            let c = children[childStart + s]

            if c < 0 then
                let tok = &tokens[~~~c]

                if tok.Length > 0 && tok.Kind = closeKind then
                    closeSlot <- s

            s <- s - 1

        if closeSlot >= 2 then
            let closingToken = &tokens[~~~children[childStart + closeSlot]]

            if closingToken.Start >= minClosingStart then
                let mutable openSlot = -1
                let mutable s = 0

                while openSlot < 0 && s < closeSlot - 1 do
                    let c = children[childStart + s]

                    if c < 0 then
                        let tok = &tokens[~~~c]

                        if tok.Length > 0 && tok.Kind = openKind then
                            openSlot <- s

                    s <- s + 1

                if openSlot >= 0 then
                    let mutable valid = true
                    let mutable itemCount = 0
                    let mutable separatorCount = 0
                    let mutable lastItemNode = -1
                    let mutable expectNode = true
                    let mutable s = openSlot + 1

                    if
                        s < closeSlot
                        && (let c = children[childStart + s] in

                            c >= 0 && nodes[c].Kind = NodeKind.AttributeTargetSpecifier)
                    then
                        s <- s + 1

                    while valid && s < closeSlot do
                        let c = children[childStart + s]

                        if expectNode then
                            if c >= 0 then
                                itemCount <- itemCount + 1
                                lastItemNode <- c
                                expectNode <- false
                            else
                                valid <- false
                        else if c < 0 then
                            let tok = &tokens[~~~c]

                            if tok.Kind = TokenKind.CommaToken && tok.Length > 0 then
                                separatorCount <- separatorCount + 1
                                expectNode <- true
                            else
                                valid <- false
                        else
                            valid <- false

                        s <- s + 1

                    if
                        valid
                        && itemCount > 0
                        && (separatorCount = itemCount - 1 || separatorCount = itemCount)
                        && lastItemNode >= 0
                    then
                        let lastItem = &nodes[lastItemNode]

                        if lastItem.TokenCount > 0 then
                            let lastToken = &tokens[lastItem.TokenStart + lastItem.TokenCount - 1]

                            if lastToken.Length > 0 then
                                closings[closingToken.Start] <-
                                    struct (lastToken.End, insert, remove)

    let internal tryListClosingsFromTree
        (tree: SyntaxTree)
        (closings: Dictionary<int, struct (int * bool * bool)>)
        (minClosingStart: int)
        =
        if closings.Count > 0 then
            closings.Clear()

        let nodes = tree.NodeSpan()
        let children = tree.ChildSpan()
        let tokens = tree.TokenSpan()
        let mutable ok = true
        let mutable nodeIndex = 0

        while ok && nodeIndex < nodes.Length do
            let node = &nodes[nodeIndex]

            match node.Kind with
            | NodeKind.SimpleLambdaExpression
            | NodeKind.ParenthesizedLambdaExpression
            | NodeKind.AnonymousMethodExpression ->
                if
                    node.TokenStart > 0
                    && tokens[node.TokenStart - 1].Kind = TokenKind.GreaterThanToken
                then
                    ok <- false

                if ok then
                    let mutable statics = 0
                    let mutable asyncs = 0
                    let mutable s = 0

                    while ok && s < node.ChildCount do
                        let c = children[node.ChildStart + s]

                        if c < 0 then
                            match tokens[~~~c].Kind with
                            | TokenKind.StaticKeyword ->
                                statics <- statics + 1
                                ok <- statics = 1
                            | TokenKind.AsyncKeyword ->
                                asyncs <- asyncs + 1
                                ok <- asyncs = 1
                            | _ -> ()

                        s <- s + 1
            | NodeKind.ObjectInitializerExpression
            | NodeKind.CollectionInitializerExpression ->
                let parentIndex = node.Parent

                let parentKind =
                    if parentIndex >= 0 then
                        nodes[parentIndex].Kind
                    else
                        NodeKind.None

                match parentKind with
                | NodeKind.ObjectCreationExpression
                | NodeKind.ImplicitObjectCreationExpression -> ()
                | NodeKind.SimpleAssignmentExpression ->
                    let parentNode = &nodes[parentIndex]
                    let gpIndex = parentNode.Parent

                    let gpKind = if gpIndex >= 0 then nodes[gpIndex].Kind else NodeKind.None

                    let validLhs =
                        parentNode.ChildCount >= 1
                        && (let first = children[parentNode.ChildStart] in

                            first >= 0
                            && (let k = nodes[first].Kind in
                                k = NodeKind.IdentifierName || k = NodeKind.ImplicitElementAccess))

                    if gpKind <> NodeKind.ObjectInitializerExpression || not validLhs then
                        ok <- false
                | _ -> ok <- false

                if ok then
                    addClosing (
                        &node,
                        children,
                        tokens,
                        nodes,
                        closings,
                        TokenKind.OpenBraceToken,
                        TokenKind.CloseBraceToken,
                        true,
                        true,
                        minClosingStart
                    )
            | NodeKind.ArrayInitializerExpression ->
                let parentIndex = node.Parent

                let parentKind =
                    if parentIndex >= 0 then
                        nodes[parentIndex].Kind
                    else
                        NodeKind.None

                match parentKind with
                | NodeKind.ArrayCreationExpression
                | NodeKind.ImplicitArrayCreationExpression
                | NodeKind.StackAllocArrayCreationExpression
                | NodeKind.ImplicitStackAllocArrayCreationExpression
                | NodeKind.ArrayInitializerExpression -> ()
                | NodeKind.EqualsValueClause ->
                    let gpIndex = nodes[parentIndex].Parent

                    let gpKind = if gpIndex >= 0 then nodes[gpIndex].Kind else NodeKind.None

                    if
                        gpKind <> NodeKind.VariableDeclarator
                        && gpKind <> NodeKind.PropertyDeclaration
                    then
                        ok <- false
                | _ -> ok <- false

                if ok then
                    addClosing (
                        &node,
                        children,
                        tokens,
                        nodes,
                        closings,
                        TokenKind.OpenBraceToken,
                        TokenKind.CloseBraceToken,
                        true,
                        true,
                        minClosingStart
                    )
            | NodeKind.ComplexElementInitializerExpression ->
                let parentIndex = node.Parent

                let parentKind =
                    if parentIndex >= 0 then
                        nodes[parentIndex].Kind
                    else
                        NodeKind.None

                if
                    parentKind <> NodeKind.CollectionInitializerExpression
                    && parentKind <> NodeKind.ObjectInitializerExpression
                then
                    ok <- false
            | NodeKind.ExpressionColon ->
                if
                    node.ChildCount < 1
                    || (let first = children[node.ChildStart] in
                        first < 0 || not (validExpressionColonTarget (nodes, children, first)))
                then
                    ok <- false
            | NodeKind.ExpressionStatement ->
                if
                    node.TokenCount > 0 && tokens[node.TokenStart].Kind = TokenKind.OpenBracketToken
                then
                    ok <- false
            | NodeKind.CollectionExpression ->
                let parentIndex = node.Parent

                if
                    parentIndex >= 0
                    && nodes[parentIndex].TokenStart = node.TokenStart
                    && (let pk = nodes[parentIndex].Kind in

                        pk = NodeKind.SimpleAssignmentExpression
                        || pk = NodeKind.ExpressionStatement)
                then
                    ok <- false

                if ok then
                    addClosing (
                        &node,
                        children,
                        tokens,
                        nodes,
                        closings,
                        TokenKind.OpenBracketToken,
                        TokenKind.CloseBracketToken,
                        true,
                        true,
                        minClosingStart
                    )
            | NodeKind.Argument ->
                let parentIndex = node.Parent

                if parentIndex >= 0 && nodes[parentIndex].Kind = NodeKind.TupleExpression then
                    for s = 0 to node.ChildCount - 1 do
                        let c = children[node.ChildStart + s]

                        if c < 0 then
                            match tokens[~~~c].Kind with
                            | TokenKind.RefKeyword
                            | TokenKind.OutKeyword
                            | TokenKind.InKeyword -> ok <- false
                            | _ -> ()
            | NodeKind.WithInitializerExpression
            | NodeKind.AnonymousObjectCreationExpression
            | NodeKind.SwitchExpression ->
                addClosing (
                    &node,
                    children,
                    tokens,
                    nodes,
                    closings,
                    TokenKind.OpenBraceToken,
                    TokenKind.CloseBraceToken,
                    true,
                    true,
                    minClosingStart
                )
            | NodeKind.ListPattern ->
                addClosing (
                    &node,
                    children,
                    tokens,
                    nodes,
                    closings,
                    TokenKind.OpenBracketToken,
                    TokenKind.CloseBracketToken,
                    true,
                    true,
                    minClosingStart
                )
            | NodeKind.EnumDeclaration ->
                addClosing (
                    &node,
                    children,
                    tokens,
                    nodes,
                    closings,
                    TokenKind.OpenBraceToken,
                    TokenKind.CloseBraceToken,
                    true,
                    false,
                    minClosingStart
                )
            | NodeKind.PropertyPatternClause ->
                addClosing (
                    &node,
                    children,
                    tokens,
                    nodes,
                    closings,
                    TokenKind.OpenBraceToken,
                    TokenKind.CloseBraceToken,
                    false,
                    true,
                    minClosingStart
                )
            | NodeKind.AttributeList ->
                addClosing (
                    &node,
                    children,
                    tokens,
                    nodes,
                    closings,
                    TokenKind.OpenBracketToken,
                    TokenKind.CloseBracketToken,
                    false,
                    true,
                    minClosingStart
                )
            | _ -> ()

            nodeIndex <- nodeIndex + 1

        ok

    let inline internal hasBreakSpan (source: ReadOnlySpan<char>) start finish =
        source.Slice(start, finish - start).IndexOfAny('\r', '\n') >= 0

    let internal hasBreak (source: string) start finish =
        hasBreakSpan (source.AsSpan()) start finish

    let internal protectedTrivia (buffer: SyntaxTree) (token: Token) leading =
        let start = token.TriviaStart + (if leading then 0 else token.LeadingCount)
        let finish = start + (if leading then token.LeadingCount else token.TrailingCount)
        let mutable i = start
        let mutable found = false

        while not found && i < finish do
            match (buffer.Trivia i).Kind with
            | TriviaKind.WhitespaceTrivia
            | TriviaKind.EndOfLineTrivia -> i <- i + 1
            | _ -> found <- true

        found

    let private trailingSeparators (source: string) (formatted: string) =
        let state = pairCache.Value
        state.ProofSource <- null

        if not (source.Contains(',')) && not (formatted.Contains(',')) then
            source
        else
            let struct (before, after) = parsePair source formatted

            let mutable closings =
                Unchecked.defaultof<Dictionary<int, struct (int * bool * bool)>>

            let getClosings () =
                if isNull closings then
                    if state.Closings.EnsureCapacity 0 > 16384 then
                        state.Closings <- Dictionary<int, struct (int * bool * bool)>()

                    let dict = state.Closings

                    closings <-
                        if
                            before.IsComplete
                            && not (hasMalformedTrivia before.LexerBuffer)
                            && tryListClosingsFromTree before dict 0
                        then
                            state.ProofFromTree <- true
                            dict
                        else
                            if dict.Count > 0 then
                                dict.Clear()

                            dict

                closings

            let edits = state.ProofEdits
            edits.Clear()

            state.ProofFromTree <- false
            state.ProofDropped.Clear()
            state.ProofAdded.Clear()
            state.ProofClosings.Clear()
            let mutable matched = true
            let mutable i = 0
            let mutable j = 0
            let mutable aligned = true

            while aligned && i < before.TokenCount && j < after.TokenCount do
                let left = before.Token i
                let right = after.Token j

                if left.Kind = right.Kind then
                    if matched then
                        matched <-
                            left.Length = right.Length
                            && source
                                .AsSpan(left.Start, left.Length)
                                .SequenceEqual(formatted.AsSpan(right.Start, right.Length))

                    i <- i + 1
                    j <- j + 1
                elif
                    right.Kind = TokenKind.CommaToken && j + 1 < after.TokenCount && i > 0 && j > 0
                then
                    let closing = after.Token(j + 1)
                    let previousBefore = before.Token(i - 1)
                    let previousAfter = after.Token(j - 1)

                    if
                        closing.Kind = left.Kind
                        && (left.Kind = TokenKind.CloseBraceToken
                            || left.Kind = TokenKind.CloseBracketToken)
                    then
                        match (getClosings ()).TryGetValue left.Start with
                        | true, struct (lastEnd, true, _) when
                            previousBefore.End = lastEnd
                            && hasBreak formatted previousAfter.End closing.Start
                            && not (protectedTrivia before left true)
                            ->
                            edits.Add(left.Start, 0, ",")
                            state.ProofAdded.Add j
                            state.ProofClosings.Add i
                            j <- j + 1
                        | _ -> aligned <- false
                    else
                        aligned <- false
                elif
                    left.Kind = TokenKind.CommaToken && i + 1 < before.TokenCount && j > 0 && i > 0
                then
                    let closing = before.Token(i + 1)
                    let previousBefore = before.Token(i - 1)
                    let previousAfter = after.Token(j - 1)

                    if
                        closing.Kind = right.Kind
                        && (closing.Kind = TokenKind.CloseBraceToken
                            || closing.Kind = TokenKind.CloseBracketToken)
                    then
                        match (getClosings ()).TryGetValue closing.Start with
                        | true, struct (lastEnd, _, true) when
                            previousBefore.End = lastEnd
                            && not (hasBreak formatted previousAfter.End right.Start)
                            && not (protectedTrivia before left false)
                            && not (protectedTrivia before closing true)
                            ->
                            edits.Add(left.Start, left.Length, "")
                            state.ProofDropped.Add i
                            i <- i + 1
                        | _ -> aligned <- false
                    else
                        aligned <- false
                else
                    aligned <- false

            if
                matched
                && aligned
                && i = before.TokenCount
                && j = after.TokenCount
                && state.ProofFromTree
                && edits.Count > 0
            then
                state.ProofSource <- source

                if state.DeferSeparatorProof then
                    state.ProofRewrite <- deferredProofMarker
                    deferredProofMarker
                else
                    let result = rewrite source edits
                    state.ProofRewrite <- result
                    result
            else
                rewrite source edits

    let private lines (text: string) =
        let result = ResizeArray<struct (int * int * int)>()
        let mutable start = 0
        let mutable i = 0

        while i < text.Length do
            if text[i] = '\r' || text[i] = '\n' then
                let length =
                    if text[i] = '\r' && i + 1 < text.Length && text[i + 1] = '\n' then
                        2
                    else
                        1

                result.Add(struct (start, i - start, length))
                i <- i + length
                start <- i
            else
                i <- i + 1

        result.Add(struct (start, text.Length - start, 0))
        result.ToArray()

    let private newline (options: PrinterOptions) =
        if options.EndOfLine = EndOfLine.CrLf then "\r\n"
        elif options.EndOfLine = EndOfLine.Cr then "\r"
        else "\n"

    let private retainNewlines options (original: string) (changed: string) =
        let before = lines original
        let after = lines changed

        if before.Length <> after.Length then
            changed
        else
            let target = (newline options).AsSpan()
            let origSpan = original.AsSpan()
            let changedSpan = changed.AsSpan()
            let mutable valid = true
            let mutable allSame = true
            let mutable i = 0

            while valid && i < before.Length do
                let struct (sA, lA, eA) = before[i]
                let struct (sB, lB, eB) = after[i]
                let endA = origSpan.Slice(sA + lA, eA)
                let endB = changedSpan.Slice(sB + lB, eB)

                if endA.SequenceEqual(endB) then
                    ()
                elif eA > 0 && endB.SequenceEqual(target) then
                    allSame <- false
                else
                    valid <- false

                i <- i + 1

            if not valid || allSame then
                changed
            else
                let sb = StringBuilder(changed.Length + before.Length)

                for k = 0 to before.Length - 1 do
                    let struct (sA, lA, eA) = before[k]
                    let struct (sB, lB, _) = after[k]
                    sb.Append(changedSpan.Slice(sB, lB)) |> ignore

                    if eA > 0 then
                        sb.Append(origSpan.Slice(sA + lA, eA)) |> ignore

                sb.ToString()

    let private indentationOnly (original: string) (changed: string) =
        let before = lines original
        let after = lines changed

        if before.Length < 3 || before.Length <> after.Length then
            false
        else
            let origSpan = original.AsSpan()
            let changedSpan = changed.AsSpan()
            let struct (sA0, lA0, eA0) = before[0]
            let struct (sB0, lB0, eB0) = after[0]

            if
                not (
                    origSpan.Slice(sA0, lA0).SequenceEqual(changedSpan.Slice(sB0, lB0))
                    && origSpan
                        .Slice(sA0 + lA0, eA0)
                        .SequenceEqual(changedSpan.Slice(sB0 + lB0, eB0))
                )
            then
                false
            else
                let lastIdx = before.Length - 1
                let struct (sALast, lALast, eALast) = before[lastIdx]
                let struct (sBLast, lBLast, eBLast) = after[lastIdx]
                let closingBefore = origSpan.Slice(sALast, lALast)
                let closingAfter = changedSpan.Slice(sBLast, lBLast)
                let mutable widthBefore = 0

                while widthBefore < closingBefore.Length
                      && (closingBefore[widthBefore] = ' ' || closingBefore[widthBefore] = '\t') do
                    widthBefore <- widthBefore + 1

                let mutable widthAfter = 0

                while widthAfter < closingAfter.Length
                      && (closingAfter[widthAfter] = ' ' || closingAfter[widthAfter] = '\t') do
                    widthAfter <- widthAfter + 1

                let indentBefore = closingBefore.Slice(0, widthBefore)
                let indentAfter = closingAfter.Slice(0, widthAfter)

                if
                    widthBefore <= 0
                    || not (
                        closingBefore
                            .Slice(widthBefore)
                            .SequenceEqual(closingAfter.Slice(widthAfter))
                    )
                    || not (
                        origSpan
                            .Slice(sALast + lALast, eALast)
                            .SequenceEqual(changedSpan.Slice(sBLast + lBLast, eBLast))
                    )
                then
                    false
                else
                    let mutable ok = true
                    let mutable i = 1

                    while ok && i <= lastIdx - 1 do
                        let struct (sA, lA, eA) = before[i]
                        let struct (sB, lB, eB) = after[i]

                        if
                            not (
                                origSpan
                                    .Slice(sA + lA, eA)
                                    .SequenceEqual(changedSpan.Slice(sB + lB, eB))
                            )
                        then
                            ok <- false
                        else
                            let lineA = origSpan.Slice(sA, lA)
                            let lineB = changedSpan.Slice(sB, lB)
                            let mutable okA = false
                            let mutable contentA = ReadOnlySpan<char>.Empty

                            if lineA.StartsWith(indentBefore, StringComparison.Ordinal) then
                                okA <- true
                                contentA <- lineA.Slice(widthBefore)
                            elif indentBefore.StartsWith(lineA, StringComparison.Ordinal) then
                                okA <- true

                            let mutable okB = false
                            let mutable contentB = ReadOnlySpan<char>.Empty

                            if lineB.StartsWith(indentAfter, StringComparison.Ordinal) then
                                okB <- true
                                contentB <- lineB.Slice(widthAfter)
                            elif indentAfter.StartsWith(lineB, StringComparison.Ordinal) then
                                okB <- true

                            ok <- okA && okB && contentA.SequenceEqual(contentB)

                        i <- i + 1

                    ok

    let private maskHoles (text: string) (holes: ResizeArray<struct (int * int)>) =
        let result = StringBuilder(text.Length)
        let mutable i, j = 0, 0

        while i < text.Length do
            let struct (holeStart, holeLength) =
                if j < holes.Count then holes[j] else struct (-1, 0)

            if i = holeStart then
                result.Append("\u0000\u0001") |> ignore
                i <- i + holeLength
                j <- j + 1
            else
                let c = text[i]
                result.Append(c) |> ignore

                if c = '\u0000' then
                    result.Append(c) |> ignore

                i <- i + 1

        result.ToString()

    let private expandInterpolated
        (text: string)
        (token: Token)
        (holes: ResizeArray<struct (int * int)>)
        =
        let state = pairCache.Value

        if isNull (box state.HoleTree) then
            state.HoleTree <- SyntaxTree()
        else
            state.HoleTree.Reset()

        holes.Clear()
        let expanded = InterpolationLexer.expandWithHoles text token state.HoleTree holes

        let certain = state.HoleTree.RecoveredTokens = 0

        if not certain && Census.enabled then
            Census.bump &Census.uncertainSegmentations

        struct (expanded, certain)

    let private interpolationHoles
        (text: string)
        (token: Token)
        (holes: ResizeArray<struct (int * int)>)
        =
        if Census.enabled then
            Census.bump &Census.interpolationHoleScans

        let struct (expanded, certain) = expandInterpolated text token holes

        for index = 0 to holes.Count - 1 do
            let struct (holeStart, holeLength) = holes[index]
            holes[index] <- struct (holeStart - token.Start, holeLength)

        if certain then expanded[0].Kind else TokenKind.None

    let private reindentInterpolation
        options
        (source: string)
        (left: Token)
        (formatted: string)
        (right: Token)
        =
        if Census.enabled then
            Census.bump &Census.interpolationEntries

        let beforeHoles = ResizeArray<struct (int * int)>()
        let afterHoles = ResizeArray<struct (int * int)>()

        let multilineRaw =
            interpolationHoles source left beforeHoles =
                TokenKind.InterpolatedMultiLineRawStringStartToken
            && interpolationHoles formatted right afterHoles =
                TokenKind.InterpolatedMultiLineRawStringStartToken

        if not multilineRaw || beforeHoles.Count <> afterHoles.Count then
            None
        else
            let original = source.Substring(left.Start, left.Length)
            let changed = formatted.Substring(right.Start, right.Length)
            let maskedOriginal = maskHoles original beforeHoles

            if
                indentationOnly
                    maskedOriginal
                    (retainNewlines options maskedOriginal (maskHoles changed afterHoles))
            then
                let edits = ResizeArray<int * int * string>()

                for i = 0 to beforeHoles.Count - 1 do
                    let struct (leftStart, leftLength) = beforeHoles[i]
                    let struct (rightStart, rightLength) = afterHoles[i]

                    edits.Add(rightStart, rightLength, original.Substring(leftStart, leftLength))

                Some(retainNewlines options original (rewrite changed edits))
            else
                None

    let internal isValidRawStringReindentation
        options
        (source: string)
        (left: Token)
        (formatted: string)
        (right: Token)
        =
        let origSpan = source.AsSpan(left.Start, left.Length)
        let changedSpan = formatted.AsSpan(right.Start, right.Length)
        let lastNl1 = origSpan.LastIndexOfAny('\r', '\n')
        let lastNl2 = changedSpan.LastIndexOfAny('\r', '\n')

        if lastNl1 < 0 || lastNl2 < 0 then
            false
        else
            let closingBefore = origSpan.Slice(lastNl1 + 1)
            let closingAfter = changedSpan.Slice(lastNl2 + 1)
            let mutable widthBefore = 0

            while widthBefore < closingBefore.Length
                  && (closingBefore[widthBefore] = ' ' || closingBefore[widthBefore] = '\t') do
                widthBefore <- widthBefore + 1

            if widthBefore = 0 then
                false
            else
                let mutable widthAfter = 0

                while widthAfter < closingAfter.Length
                      && (closingAfter[widthAfter] = ' ' || closingAfter[widthAfter] = '\t') do
                    widthAfter <- widthAfter + 1

                if
                    not (
                        closingBefore
                            .Slice(widthBefore)
                            .SequenceEqual(closingAfter.Slice(widthAfter))
                    )
                then
                    false
                else
                    let indentBefore = closingBefore.Slice(0, widthBefore)
                    let indentAfter = closingAfter.Slice(0, widthAfter)
                    let target = (newline options).AsSpan()
                    let mutable pos1 = 0
                    let mutable pos2 = 0
                    let mutable lineIdx = 0
                    let mutable ok = true
                    let mutable doneLines = false

                    while ok && not doneLines do
                        let rem1 = origSpan.Slice(pos1)
                        let rel1 = rem1.IndexOfAny('\r', '\n')
                        let rem2 = changedSpan.Slice(pos2)
                        let rel2 = rem2.IndexOfAny('\r', '\n')

                        if (rel1 < 0) <> (rel2 < 0) then
                            ok <- false
                        elif rel1 < 0 then
                            doneLines <- true
                        else
                            let line1 = rem1.Slice(0, rel1)
                            let line2 = rem2.Slice(0, rel2)
                            let nlPos1 = pos1 + rel1
                            let nlPos2 = pos2 + rel2

                            let nlLen1 =
                                if
                                    origSpan[nlPos1] = '\r'
                                    && nlPos1 + 1 < origSpan.Length
                                    && origSpan[nlPos1 + 1] = '\n'
                                then
                                    2
                                else
                                    1

                            let nlLen2 =
                                if
                                    changedSpan[nlPos2] = '\r'
                                    && nlPos2 + 1 < changedSpan.Length
                                    && changedSpan[nlPos2 + 1] = '\n'
                                then
                                    2
                                else
                                    1

                            let end1 = origSpan.Slice(nlPos1, nlLen1)
                            let end2 = changedSpan.Slice(nlPos2, nlLen2)

                            if not (end1.SequenceEqual(end2) || end2.SequenceEqual(target)) then
                                ok <- false
                            elif lineIdx = 0 then
                                ok <- line1.SequenceEqual(line2)
                            else
                                let mutable ok1 = false
                                let mutable c1 = ReadOnlySpan<char>.Empty

                                if line1.StartsWith(indentBefore, StringComparison.Ordinal) then
                                    ok1 <- true
                                    c1 <- line1.Slice(widthBefore)
                                elif indentBefore.StartsWith(line1, StringComparison.Ordinal) then
                                    ok1 <- true

                                let mutable ok2 = false
                                let mutable c2 = ReadOnlySpan<char>.Empty

                                if line2.StartsWith(indentAfter, StringComparison.Ordinal) then
                                    ok2 <- true
                                    c2 <- line2.Slice(widthAfter)
                                elif indentAfter.StartsWith(line2, StringComparison.Ordinal) then
                                    ok2 <- true

                                ok <- ok1 && ok2 && c1.SequenceEqual(c2)

                            pos1 <- nlPos1 + nlLen1
                            pos2 <- nlPos2 + nlLen2
                            lineIdx <- lineIdx + 1

                    ok && lineIdx >= 2

    let internal tryReindentRawInterpolation
        options
        (source: string)
        (left: Token)
        (formatted: string)
        (right: Token)
        =
        if
            source
                .AsSpan(left.Start, left.Length)
                .Contains("\"\"\"".AsSpan(), StringComparison.Ordinal)
            && formatted
                .AsSpan(right.Start, right.Length)
                .Contains("\"\"\"".AsSpan(), StringComparison.Ordinal)
        then
            reindentInterpolation options source left formatted right
        else
            None

    let private rawStringIndentation options (source: string) (formatted: string) =
        if
            Object.ReferenceEquals(source, deferredProofMarker)
            || not (source.Contains("\"\"\"", StringComparison.Ordinal))
            || not (formatted.Contains("\"\"\"", StringComparison.Ordinal))
        then
            source
        else
            let struct (before, after) = lexPair source formatted
            let edits = ResizeArray<int * int * string>()

            let candidate kind =
                kind = TokenKind.MultiLineRawStringLiteralToken
                || kind = TokenKind.Utf8MultiLineRawStringLiteralToken
                || kind = TokenKind.InterpolatedStringToken

            let mutable i, j = 0, 0

            while i < before.TokenCount && j < after.TokenCount do
                if not (candidate (before.Token i).Kind) then
                    i <- i + 1
                elif not (candidate (after.Token j).Kind) then
                    j <- j + 1
                else
                    let left, right = before.Token i, after.Token j

                    if right.Kind = left.Kind then
                        let leftSpan = source.AsSpan(left.Start, left.Length)
                        let rightSpan = formatted.AsSpan(right.Start, right.Length)

                        if not (leftSpan.SequenceEqual rightSpan) then
                            if
                                left.Kind = TokenKind.MultiLineRawStringLiteralToken
                                || left.Kind = TokenKind.Utf8MultiLineRawStringLiteralToken
                            then
                                let original = leftSpan.ToString()
                                let changed = retainNewlines options original (rightSpan.ToString())

                                if indentationOnly original changed then
                                    edits.Add(left.Start, left.Length, changed)
                            elif
                                leftSpan.Contains("\"\"\"".AsSpan(), StringComparison.Ordinal)
                                && rightSpan.Contains("\"\"\"".AsSpan(), StringComparison.Ordinal)
                            then
                                match reindentInterpolation options source left formatted right with
                                | Some expected -> edits.Add(left.Start, left.Length, expected)
                                | None -> ()

                    i <- i + 1
                    j <- j + 1

            rewrite source edits

    [<Struct>]
    type private UsingEntry =
        {
            Frame: struct (int * int * string list)
            InsideConditional: bool
            SpanStart: int
            SpanLength: int
            IsGlobal: bool
            Key: string
        }

    let inline private isContextDirectiveKind (kind: TriviaKind) =
        kind = TriviaKind.DefineDirectiveTrivia
        || kind = TriviaKind.UndefDirectiveTrivia
        || kind = TriviaKind.NullableDirectiveTrivia
        || kind = TriviaKind.LineDirectiveTrivia
        || kind = TriviaKind.PragmaWarningDirectiveTrivia
        || kind = TriviaKind.PragmaChecksumDirectiveTrivia

    let inline private isContextPositionDirectiveKind (kind: TriviaKind) =
        isContextDirectiveKind kind || kind = TriviaKind.LineSpanDirectiveTrivia

    let private conditionalFramesCore
        (directiveCount: int)
        (getKind: int -> TriviaKind)
        (getStart: int -> int)
        (getText: int -> string)
        (usings: int[])
        =
        let holds = HashSet<int>()
        let stack = Stack<int>()
        let mutable next = 0

        for i = 0 to directiveCount - 1 do
            let spanStart = getStart i
            let kind = getKind i

            while next < usings.Length && usings[next] < spanStart do
                for frameStart in stack do
                    holds.Add frameStart |> ignore

                next <- next + 1

            if kind = TriviaKind.IfDirectiveTrivia then
                stack.Push spanStart
            elif kind = TriviaKind.EndIfDirectiveTrivia then
                if stack.Count > 0 then
                    stack.Pop() |> ignore

        while next < usings.Length do
            for frameStart in stack do
                holds.Add frameStart |> ignore

            next <- next + 1

        let positions = ResizeArray<int>()
        let snapshots = ResizeArray<string list>()
        let occurrences = Dictionary<string, int>(StringComparer.Ordinal)
        let contextPositions = ResizeArray<int>()
        let mutable frames = []
        let mutable context = 0

        for i = 0 to directiveCount - 1 do
            let kind = getKind i
            let spanStart = getStart i

            if isContextDirectiveKind kind then
                context <- context + 1

            let conditional =
                if kind = TriviaKind.IfDirectiveTrivia then
                    let condition = getText i

                    let identity =
                        if holds.Contains spanStart then
                            let key = $"{condition} @{context}"

                            let ordinal =
                                match occurrences.TryGetValue key with
                                | true, count -> count
                                | _ -> 0

                            occurrences[key] <- ordinal + 1
                            $"{key} #{ordinal}"
                        else
                            condition

                    frames <- identity :: frames
                    true
                elif
                    kind = TriviaKind.ElifDirectiveTrivia || kind = TriviaKind.ElseDirectiveTrivia
                then
                    if not frames.IsEmpty then
                        frames <- (getText i + " :: " + frames.Head) :: frames.Tail

                    true
                elif kind = TriviaKind.EndIfDirectiveTrivia then
                    if not frames.IsEmpty then
                        frames <- frames.Tail

                    true
                else
                    false

            if conditional then
                positions.Add spanStart
                snapshots.Add frames

            if isContextPositionDirectiveKind kind then
                contextPositions.Add spanStart

        let positions = positions.ToArray()
        let snapshots = snapshots.ToArray()
        let contextPositions = contextPositions.ToArray()

        let before (position: int) =
            let found = Array.BinarySearch(positions, position)
            if found >= 0 then found else ~~~found

        struct ((fun position ->
                    let count = before position
                    if count = 0 then [] else snapshots[count - 1]),
                (fun start finish -> before finish > before (start + 1)),
                (fun (position: int) ->
                    let found = Array.BinarySearch(contextPositions, position)
                    if found >= 0 then found else ~~~found))

    let private tryDirectiveConditionText (source: string) (item: Trivia) =
        let span = source.AsSpan(item.Start, item.Length)
        let mutable i = 0

        while i < span.Length && (span[i] = ' ' || span[i] = '\t') do
            i <- i + 1

        if i >= span.Length || span[i] <> '#' then
            ValueNone
        else
            let builder = StringBuilder(span.Length)
            builder.Append('#') |> ignore
            i <- i + 1
            let mutable valid = true
            let mutable doneLine = false

            while valid && not doneLine && i < span.Length do
                while i < span.Length && (span[i] = ' ' || span[i] = '\t') do
                    i <- i + 1

                if i >= span.Length || span[i] = '\r' || span[i] = '\n' then
                    doneLine <- true
                elif span[i] = '/' && i + 1 < span.Length && span[i + 1] = '/' then
                    doneLine <- true
                else
                    let ch = span[i]

                    if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch = '_' then
                        let start = i
                        i <- i + 1

                        while i < span.Length
                              && ((span[i] >= 'a' && span[i] <= 'z')
                                  || (span[i] >= 'A' && span[i] <= 'Z')
                                  || (span[i] >= '0' && span[i] <= '9')
                                  || span[i] = '_') do
                            i <- i + 1

                        builder.Append(' ').Append(span.Slice(start, i - start)) |> ignore
                    elif ch = '(' || ch = ')' then
                        builder.Append(' ').Append(ch) |> ignore
                        i <- i + 1
                    elif ch = '!' then
                        if i + 1 < span.Length && span[i + 1] = '=' then
                            builder.Append(" !=") |> ignore
                            i <- i + 2
                        else
                            builder.Append(" !") |> ignore
                            i <- i + 1
                    elif ch = '=' && i + 1 < span.Length && span[i + 1] = '=' then
                        builder.Append(" ==") |> ignore
                        i <- i + 2
                    elif ch = '&' && i + 1 < span.Length && span[i + 1] = '&' then
                        builder.Append(" &&") |> ignore
                        i <- i + 2
                    elif ch = '|' && i + 1 < span.Length && span[i + 1] = '|' then
                        builder.Append(" ||") |> ignore
                        i <- i + 2
                    else
                        valid <- false

            if valid && doneLine then
                builder.Append(' ').ToString() |> ValueSome
            else
                ValueNone

    let private isValidDirectiveConditionText (source: string) (item: Trivia) =
        let span = source.AsSpan(item.Start, item.Length)
        let mutable i = 0

        while i < span.Length && (span[i] = ' ' || span[i] = '\t') do
            i <- i + 1

        if i >= span.Length || span[i] <> '#' then
            false
        else
            i <- i + 1
            let mutable valid = true
            let mutable doneLine = false

            while valid && not doneLine && i < span.Length do
                while i < span.Length && (span[i] = ' ' || span[i] = '\t') do
                    i <- i + 1

                if i >= span.Length || span[i] = '\r' || span[i] = '\n' then
                    doneLine <- true
                elif span[i] = '/' && i + 1 < span.Length && span[i + 1] = '/' then
                    doneLine <- true
                else
                    let ch = span[i]

                    if (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || ch = '_' then
                        i <- i + 1

                        while i < span.Length
                              && ((span[i] >= 'a' && span[i] <= 'z')
                                  || (span[i] >= 'A' && span[i] <= 'Z')
                                  || (span[i] >= '0' && span[i] <= '9')
                                  || span[i] = '_') do
                            i <- i + 1
                    elif ch = '(' || ch = ')' then
                        i <- i + 1
                    elif ch = '!' then
                        if i + 1 < span.Length && span[i + 1] = '=' then
                            i <- i + 2
                        else
                            i <- i + 1
                    elif ch = '=' && i + 1 < span.Length && span[i + 1] = '=' then
                        i <- i + 2
                    elif ch = '&' && i + 1 < span.Length && span[i + 1] = '&' then
                        i <- i + 2
                    elif ch = '|' && i + 1 < span.Length && span[i + 1] = '|' then
                        i <- i + 2
                    else
                        valid <- false

            valid && doneLine

    let inline private isRelevantDirectiveTrivia (kind: TriviaKind) =
        kind = TriviaKind.IfDirectiveTrivia
        || kind = TriviaKind.ElifDirectiveTrivia
        || kind = TriviaKind.ElseDirectiveTrivia
        || kind = TriviaKind.EndIfDirectiveTrivia
        || isContextPositionDirectiveKind kind

    let rec private isValidUsingTypeNode (tree: SyntaxTree) (allowNonName: bool) (index: int) =
        let mutable current = index
        let mutable currentAllowNonName = allowNonName
        let mutable ok = true

        while ok && current >= 0 do
            let n = tree.Node current

            match n.Kind with
            | NodeKind.IdentifierName -> current <- -1
            | NodeKind.QualifiedName
            | NodeKind.AliasQualifiedName ->
                let mutable firstChild = -1
                let mutable slot = 0

                while ok && slot < n.ChildCount do
                    let sub = tree.Child(n.ChildStart + slot)

                    if sub >= 0 then
                        if firstChild < 0 then
                            firstChild <- sub
                        else
                            ok <- isValidUsingTypeNode tree false sub

                    slot <- slot + 1

                current <- firstChild
                currentAllowNonName <- false
            | NodeKind.GenericName ->
                let mutable slot = 0

                while ok && slot < n.ChildCount do
                    let sub = tree.Child(n.ChildStart + slot)

                    if sub >= 0 then
                        if (tree.Node sub).Kind = NodeKind.TypeArgumentList then
                            let argsNode = tree.Node sub
                            let mutable aSlot = 0

                            while ok && aSlot < argsNode.ChildCount do
                                let arg = tree.Child(argsNode.ChildStart + aSlot)

                                if arg >= 0 then
                                    ok <- isValidUsingTypeNode tree true arg

                                aSlot <- aSlot + 1
                        else
                            ok <- isValidUsingTypeNode tree false sub

                    slot <- slot + 1

                current <- -1
            | NodeKind.PredefinedType
            | NodeKind.ArrayType
            | NodeKind.NullableType
            | NodeKind.TupleType
            | NodeKind.TupleElement
            | NodeKind.PointerType
            | NodeKind.FunctionPointerType
            | NodeKind.FunctionPointerParameterList
            | NodeKind.FunctionPointerParameter
            | NodeKind.FunctionPointerCallingConvention
            | NodeKind.ArrayRankSpecifier when currentAllowNonName ->
                let mutable firstChild = -1
                let mutable slot = 0

                while ok && slot < n.ChildCount do
                    let sub = tree.Child(n.ChildStart + slot)

                    if sub >= 0 then
                        if firstChild < 0 then
                            firstChild <- sub
                        else
                            ok <- isValidUsingTypeNode tree true sub

                    slot <- slot + 1

                current <- firstChild
                currentAllowNonName <- true
            | NodeKind.OmittedArraySizeExpression when currentAllowNonName -> current <- -1
            | _ -> ok <- false

        ok

    let internal isValidUsingDirective (tree: SyntaxTree) (childNode: Node) =
        if childNode.TokenCount <= 0 then
            false
        else
            let firstTok = tree.Token childNode.TokenStart
            let lastTok = tree.Token(childNode.TokenStart + childNode.TokenCount - 1)
            let mutable hasStatic = false
            let mutable hasUnsafe = false
            let mutable hasAlias = false
            let mutable targetNode = -1

            for slot = 0 to childNode.ChildCount - 1 do
                let item = tree.Child(childNode.ChildStart + slot)

                if item < 0 then
                    match (tree.Token ~~~item).Kind with
                    | TokenKind.StaticKeyword -> hasStatic <- true
                    | TokenKind.UnsafeKeyword -> hasUnsafe <- true
                    | _ -> ()
                else
                    let itemNode = tree.Node item

                    if itemNode.Kind = NodeKind.NameEquals then
                        hasAlias <- true
                    else
                        targetNode <- item

            let mutable invalidToken = false

            for tokIdx = childNode.TokenStart to childNode.TokenStart + childNode.TokenCount - 1 do
                let tok = tree.Token tokIdx

                if
                    tok.Kind = TokenKind.BadToken
                    || tok.Kind = TokenKind.OmittedTypeArgumentToken
                    || tok.Kind = TokenKind.RefKeyword
                    || tok.Kind = TokenKind.ReadOnlyKeyword
                    || tok.Kind = TokenKind.ScopedKeyword
                    || (tok.Length <= 0 && tok.Kind <> TokenKind.OmittedArraySizeExpressionToken)
                then
                    invalidToken <- true

            firstTok.Length > 0
            && lastTok.Length > 0
            && not invalidToken
            && targetNode >= 0
            && not (hasAlias && hasStatic)
            && not (hasUnsafe && not hasAlias && not hasStatic)
            && isValidUsingTypeNode tree hasAlias targetNode

    let private usingScopesFromTree (source: string) (tree: SyntaxTree) =
        let triviaSpan = tree.TriviaSpan()

        if not tree.IsComplete || hasMalformedTriviaSpan triviaSpan then
            ValueNone
        else
            let rawScopes = ResizeArray<struct (int * int)[]>()
            let usingPositions = ResizeArray<int>()
            let mutable validTree = true
            let mutable maxUsingEnd = 0
            let stack = pairCache.Value.Stack
            stack.Clear()

            if tree.RootIndex >= 0 then
                stack.Push tree.RootIndex

            while validTree && stack.Count > 0 do
                let nodeIndex = stack.Pop()
                let node = tree.Node nodeIndex

                match node.Kind with
                | NodeKind.CompilationUnit
                | NodeKind.NamespaceDeclaration
                | NodeKind.FileScopedNamespaceDeclaration ->
                    let usings = ResizeArray<struct (int * int)>()

                    let declStart =
                        if node.Kind = NodeKind.CompilationUnit then
                            0
                        else
                            let mutable lead = 0

                            while lead < node.ChildCount
                                  && (let child = tree.Child(node.ChildStart + lead)
                                      child >= 0 && (tree.Node child).Kind = NodeKind.AttributeList) do
                                lead <- lead + 1

                            lead + 3

                    let mutable seenMemberOrAttr = false
                    let mutable externSegment = 0

                    for s = node.ChildCount - 1 downto 0 do
                        let c = tree.Child(node.ChildStart + s)

                        if c >= 0 then
                            let childKind = (tree.Node c).Kind

                            if
                                childKind = NodeKind.NamespaceDeclaration
                                || childKind = NodeKind.FileScopedNamespaceDeclaration
                            then
                                stack.Push c

                    for s = declStart to node.ChildCount - 1 do
                        let c = tree.Child(node.ChildStart + s)

                        if c >= 0 then
                            let childNode = tree.Node c

                            if childNode.Kind = NodeKind.UsingDirective then
                                if
                                    seenMemberOrAttr || not (isValidUsingDirective tree childNode)
                                then
                                    validTree <- false
                                else
                                    let firstTok = tree.Token childNode.TokenStart
                                    usings.Add(struct (c, externSegment))
                                    usingPositions.Add firstTok.Start
                                    let struct (spanStart, spanLength) = tree.SourceSpan c
                                    let spanEnd = spanStart + spanLength

                                    if spanEnd > maxUsingEnd then
                                        maxUsingEnd <- spanEnd
                            elif childNode.Kind = NodeKind.ExternAliasDirective then
                                externSegment <- externSegment + 1
                            else
                                seenMemberOrAttr <- true

                    if validTree && usings.Count > 0 then
                        rawScopes.Add(usings.ToArray())
                | _ -> ()

            if not validTree then
                ValueNone
            elif rawScopes.Count = 0 then
                ValueSome Array.empty
            else
                let directives = ResizeArray<Trivia>()
                let mutable hasConditionals = false
                let outerTriviaCount = tree.LexerBuffer.TriviaCount

                for i = 0 to triviaSpan.Length - 1 do
                    let item = triviaSpan[i]

                    if isRelevantDirectiveTrivia item.Kind then
                        if i >= outerTriviaCount then
                            validTree <- false
                        elif item.Start < maxUsingEnd then
                            directives.Add item

                            if
                                item.Kind = TriviaKind.IfDirectiveTrivia
                                || item.Kind = TriviaKind.ElifDirectiveTrivia
                                || item.Kind = TriviaKind.ElseDirectiveTrivia
                                || item.Kind = TriviaKind.EndIfDirectiveTrivia
                            then
                                hasConditionals <- true
                        elif
                            validTree
                            && (item.Kind = TriviaKind.IfDirectiveTrivia
                                || item.Kind = TriviaKind.ElifDirectiveTrivia
                                || item.Kind = TriviaKind.ElseDirectiveTrivia)
                        then
                            if not (isValidDirectiveConditionText source item) then
                                validTree <- false

                let directiveTexts =
                    if not validTree || not hasConditionals then
                        [||]
                    else
                        let texts = Array.zeroCreate<string> directives.Count

                        for i = 0 to directives.Count - 1 do
                            let item = directives[i]

                            if
                                validTree
                                && (item.Kind = TriviaKind.IfDirectiveTrivia
                                    || item.Kind = TriviaKind.ElifDirectiveTrivia
                                    || item.Kind = TriviaKind.ElseDirectiveTrivia)
                            then
                                match tryDirectiveConditionText source item with
                                | ValueSome t -> texts[i] <- t
                                | ValueNone -> validTree <- false

                        texts

                if not validTree then
                    ValueNone
                else
                    let struct (framesAt, containsConditional, contextAt) =
                        if directives.Count = 0 then
                            struct ((fun (_: int) -> ([]: string list)),
                                    (fun (_: int) (_: int) -> false),
                                    (fun (_: int) -> 0))
                        else
                            let sortedPositions = usingPositions.ToArray()
                            Array.sortInPlace sortedPositions

                            conditionalFramesCore
                                directives.Count
                                (fun i -> directives[i].Kind)
                                (fun i -> directives[i].Start)
                                (fun i -> directiveTexts[i])
                                sortedPositions

                    let keyBuilder = StringBuilder()

                    let buildKey (uNode: Node) =
                        keyBuilder.Clear() |> ignore

                        for t = uNode.TokenStart to uNode.TokenStart + uNode.TokenCount - 1 do
                            let tok = tree.Token t

                            keyBuilder
                                .Append(int tok.Kind)
                                .Append(' ')
                                .Append(tok.Length)
                                .Append(' ')
                                .Append(source, tok.Start, tok.Length)
                            |> ignore

                        keyBuilder.ToString()

                    let scopes = Array.zeroCreate<UsingEntry[]> rawScopes.Count

                    for i = 0 to rawScopes.Count - 1 do
                        let usings = rawScopes[i]
                        let entries = Array.zeroCreate<UsingEntry> usings.Length

                        for j = 0 to usings.Length - 1 do
                            let struct (uIndex, externSegment) = usings[j]
                            let uNode = tree.Node uIndex
                            let struct (spanStart, spanLength) = tree.SourceSpan uIndex
                            let spanEnd = spanStart + spanLength

                            let isGlobal =
                                uNode.TokenCount > 0
                                && (tree.Token uNode.TokenStart).Kind = TokenKind.GlobalKeyword

                            entries[j] <-
                                {
                                    Frame =
                                        struct (contextAt spanStart,
                                                externSegment,
                                                framesAt spanStart)
                                    InsideConditional = containsConditional spanStart spanEnd
                                    SpanStart = spanStart
                                    SpanLength = spanLength
                                    IsGlobal = isGlobal
                                    Key = buildKey uNode
                                }

                        scopes[i] <- entries

                    if scopes.Length > 1 then
                        Array.sortInPlaceBy (fun (scope: UsingEntry[]) -> scope[0].SpanStart) scopes

                    ValueSome scopes

    let inline private isGlobalToken (text: string) (buffer: TokenBuffer) (index: int) =
        if index < 0 || index >= buffer.TokenCount then
            false
        else
            let token = buffer.Token index

            token.Kind = TokenKind.IdentifierToken
            && token.Length = 6
            && text.AsSpan(token.Start, 6).SequenceEqual("global".AsSpan())

    let inline private hasInterpolatedUsing (text: string) (token: Token) =
        token.Kind = TokenKind.InterpolatedStringToken
        && text
            .AsSpan(token.Start, token.Length)
            .Contains("using".AsSpan(), StringComparison.Ordinal)

    let private canSkipUsingDirectivePermutation (source: string) (formatted: string) =
        if
            not (hasSubstringTwice source "using")
            || not (hasSubstringTwice formatted "using")
        then
            true
        else
            let struct (before, after) = lexPair source formatted

            if hasAmbiguousTrivia before || hasAmbiguousTrivia after then
                false
            else
                let mutable i = 0
                let mutable j = 0
                let mutable identical = true

                while identical && (i < before.TokenCount || j < after.TokenCount) do
                    while i < before.TokenCount && (before.Token i).Kind <> TokenKind.UsingKeyword do
                        if hasInterpolatedUsing source (before.Token i) then
                            identical <- false

                        i <- i + 1

                    while j < after.TokenCount && (after.Token j).Kind <> TokenKind.UsingKeyword do
                        if hasInterpolatedUsing formatted (after.Token j) then
                            identical <- false

                        j <- j + 1

                    if identical then
                        if i < before.TokenCount && j < after.TokenCount then
                            if
                                isGlobalToken source before (i - 1)
                                <> isGlobalToken formatted after (j - 1)
                            then
                                identical <- false
                            else
                                i <- i + 1
                                j <- j + 1
                                let mutable firstAfterUsing = true
                                let mutable doneClause = false

                                while identical
                                      && not doneClause
                                      && i < before.TokenCount
                                      && j < after.TokenCount do
                                    let left = before.Token i
                                    let right = after.Token j

                                    if
                                        left.Kind <> right.Kind
                                        || left.Length <> right.Length
                                        || not (
                                            source
                                                .AsSpan(left.Start, left.Length)
                                                .SequenceEqual(
                                                    formatted.AsSpan(right.Start, right.Length)
                                                )
                                        )
                                    then
                                        identical <- false
                                    else
                                        match left.Kind with
                                        | TokenKind.SemicolonToken ->
                                            i <- i + 1
                                            j <- j + 1
                                            doneClause <- true
                                        | TokenKind.OpenParenToken when firstAfterUsing ->
                                            i <- i + 1
                                            j <- j + 1
                                            doneClause <- true
                                        | TokenKind.UsingKeyword
                                        | TokenKind.OpenBraceToken
                                        | TokenKind.CloseBraceToken
                                        | TokenKind.InterpolatedStringToken
                                        | TokenKind.EndOfFileToken -> identical <- false
                                        | _ ->
                                            firstAfterUsing <- false
                                            i <- i + 1
                                            j <- j + 1

                                if not doneClause then
                                    identical <- false
                        elif i < before.TokenCount || j < after.TokenCount then
                            identical <- false

                if identical then
                    true
                else
                    let countUsings (text: string) (buffer: TokenBuffer) =
                        let mutable count = 0
                        let mutable idx = 0

                        while count < 2 && idx < buffer.TokenCount do
                            let tok = buffer.Token idx

                            if
                                tok.Kind = TokenKind.UsingKeyword
                                && (idx + 1 >= buffer.TokenCount
                                    || (buffer.Token(idx + 1)).Kind <> TokenKind.OpenParenToken)
                            then
                                count <- count + 1
                            elif hasInterpolatedUsing text tok then
                                count <- count + 2

                            idx <- idx + 1

                        count

                    countUsings source before < 2 || countUsings formatted after < 2

    let private usingDirectivePermutation (source: string) (formatted: string) =
        if canSkipUsingDirectivePermutation source formatted then
            source
        else
            let struct (beforeTree, afterTree) = parsePair source formatted

            let before, after =
                match
                    usingScopesFromTree source beforeTree, usingScopesFromTree formatted afterTree
                with
                | ValueSome left, ValueSome right -> left, right
                | _ -> [||], [||]

            let edits = ResizeArray<int * int * string>()

            if before.Length = after.Length then
                for i = 0 to before.Length - 1 do
                    let left = before[i]
                    let right = after[i]

                    if left.Length = right.Length && left.Length > 0 then
                        let mutable split = false
                        let mutable anyKeyDiff = false
                        let mutable framesMatch = true
                        let mutable singleFrame = true
                        let firstFrame = left[0].Frame

                        let mutable hasLastOrdinary = false

                        let mutable lastOrdinaryFrame =
                            Unchecked.defaultof<struct (int * int * string list)>

                        let mutable ordinarySeen
                            : ValueOption<HashSet<struct (int * int * string list)>> =
                            ValueNone

                        for k = 0 to left.Length - 1 do
                            let lEntry = left[k]
                            let rEntry = right[k]

                            if lEntry.InsideConditional || rEntry.InsideConditional then
                                split <- true

                            if
                                not (
                                    String.Equals(lEntry.Key, rEntry.Key, StringComparison.Ordinal)
                                )
                            then
                                anyKeyDiff <- true

                            if lEntry.Frame <> rEntry.Frame then
                                framesMatch <- false

                            if rEntry.IsGlobal then
                                if hasLastOrdinary then
                                    if rEntry.Frame = lastOrdinaryFrame then
                                        framesMatch <- false
                                    else
                                        match ordinarySeen with
                                        | ValueSome seen when seen.Contains rEntry.Frame ->
                                            framesMatch <- false
                                        | _ -> ()
                            elif not hasLastOrdinary then
                                hasLastOrdinary <- true
                                lastOrdinaryFrame <- rEntry.Frame
                            elif rEntry.Frame <> lastOrdinaryFrame then
                                match ordinarySeen with
                                | ValueSome seen -> seen.Add rEntry.Frame |> ignore
                                | ValueNone ->
                                    let seen = HashSet<struct (int * int * string list)>()
                                    seen.Add lastOrdinaryFrame |> ignore
                                    seen.Add rEntry.Frame |> ignore
                                    ordinarySeen <- ValueSome seen

                                lastOrdinaryFrame <- rEntry.Frame

                            if k > 0 && lEntry.Frame <> firstFrame then
                                singleFrame <- false

                        let populations (items: UsingEntry[]) =
                            items
                            |> Array.groupBy (fun entry -> entry.Frame)
                            |> Array.map (fun (frames, members) ->
                                frames,
                                (members
                                 |> Array.map (fun entry -> entry.Key)
                                 |> Array.sortWith compare))
                            |> Array.sortWith compare

                        if
                            not split
                            && anyKeyDiff
                            && framesMatch
                            && (singleFrame || populations left = populations right)
                        then
                            let available =
                                Dictionary<string, Queue<UsingEntry>>(StringComparer.Ordinal)

                            for slot = 0 to left.Length - 1 do
                                let directiveKey = left[slot].Key

                                let occurrences =
                                    match available.TryGetValue directiveKey with
                                    | true, occurrences -> occurrences
                                    | _ ->
                                        let occurrences = Queue<UsingEntry>()
                                        available.Add(directiveKey, occurrences)
                                        occurrences

                                occurrences.Enqueue left[slot]

                            let matched = Array.zeroCreate<UsingEntry> right.Length
                            let mutable slot = 0
                            let mutable same = true

                            while same && slot < right.Length do
                                match available.TryGetValue right[slot].Key with
                                | true, occurrences when occurrences.Count > 0 ->
                                    matched[slot] <- occurrences.Dequeue()
                                    slot <- slot + 1
                                | _ -> same <- false

                            if same then
                                for slot = 0 to matched.Length - 1 do
                                    let directive = matched[slot]
                                    let target = left[slot]

                                    edits.Add(
                                        target.SpanStart,
                                        target.SpanLength,
                                        source.Substring(directive.SpanStart, directive.SpanLength)
                                    )

            rewrite source edits

    let private hasMultilineLiteralCandidate (text: string) =
        text.Contains("@\"", StringComparison.Ordinal)
        || text.Contains("@$\"", StringComparison.Ordinal)
        || text.Contains("\"\"\"", StringComparison.Ordinal)

    let private hasConvertibleLineEnding (options: PrinterOptions) (source: string) =
        match options.EndOfLine with
        | EndOfLine.Lf -> source.Contains('\r')
        | EndOfLine.Cr -> source.Contains('\n')
        | EndOfLine.CrLf
        | _ -> source.Contains('\r') || source.Contains('\n')

    let private isMultilineLiteralTokenKind (kind: TokenKind) =
        match kind with
        | TokenKind.StringLiteralToken
        | TokenKind.Utf8StringLiteralToken
        | TokenKind.MultiLineRawStringLiteralToken
        | TokenKind.Utf8MultiLineRawStringLiteralToken
        | TokenKind.InterpolatedStringToken -> true
        | _ -> false

    let private canSkipMultilineLiteralLineEndings
        (options: PrinterOptions)
        (source: string)
        (formatted: string)
        =
        if
            Object.ReferenceEquals(source, deferredProofMarker)
            || not (hasMultilineLiteralCandidate source)
            || not (hasMultilineLiteralCandidate formatted)
            || not (hasConvertibleLineEnding options source)
        then
            true
        else
            let struct (before, after) = lexPair source formatted

            if hasAmbiguousTrivia before || hasAmbiguousTrivia after then
                false
            else
                let mutable i = 0
                let mutable j = 0
                let mutable canSkip = true

                while canSkip && (i < before.TokenCount || j < after.TokenCount) do
                    while i < before.TokenCount
                          && not (isMultilineLiteralTokenKind (before.Token i).Kind) do
                        i <- i + 1

                    while j < after.TokenCount
                          && not (isMultilineLiteralTokenKind (after.Token j).Kind) do
                        j <- j + 1

                    if i < before.TokenCount && j < after.TokenCount then
                        let left = before.Token i
                        let right = after.Token j

                        if left.Kind <> right.Kind then
                            canSkip <- false
                        elif hasBreak source left.Start left.End then
                            if
                                left.Length <> right.Length
                                || not (
                                    source
                                        .AsSpan(left.Start, left.Length)
                                        .SequenceEqual(formatted.AsSpan(right.Start, right.Length))
                                )
                            then
                                canSkip <- false

                        i <- i + 1
                        j <- j + 1
                    elif i < before.TokenCount || j < after.TokenCount then
                        canSkip <- false

                canSkip

    let rec private appendLiteralRuns (text: string) (token: Token) (runs: ResizeArray<Token>) =
        match token.Kind with
        | TokenKind.StringLiteralToken
        | TokenKind.Utf8StringLiteralToken ->
            if token.Length >= 2 && text[token.Start] = '@' && text[token.Start + 1] = '"' then
                runs.Add token

            true
        | TokenKind.MultiLineRawStringLiteralToken
        | TokenKind.Utf8MultiLineRawStringLiteralToken ->
            runs.Add token
            true
        | TokenKind.InterpolatedStringToken ->
            if Census.enabled then
                Census.bump &Census.lineEndingPieceScans

            let holes = ResizeArray<struct (int * int)>()
            let struct (expandedRuns, certain) = expandInterpolated text token holes
            let expanded = expandedRuns.ToArray()
            let mutable segmented = certain
            let startKind = expanded[0].Kind
            let multilineRaw = startKind = TokenKind.InterpolatedMultiLineRawStringStartToken

            let spansLineBreaks =
                multilineRaw || startKind = TokenKind.InterpolatedVerbatimStringStartToken

            let insideHole (start: int) =
                let mutable hit = false

                for index = 0 to holes.Count - 1 do
                    let struct (holeStart, holeLength) = holes[index]

                    if start >= holeStart && start < holeStart + holeLength then
                        hit <- true

                hit

            if multilineRaw then
                runs.Add expanded[0]

            for index = 1 to expanded.Length - 2 do
                let item = expanded[index]

                if item.Kind = TokenKind.InterpolatedStringTextToken then
                    if spansLineBreaks && not (insideHole item.Start) then
                        runs.Add item
                else
                    segmented <- appendLiteralRuns text item runs && segmented

            let last = expanded[expanded.Length - 1]

            if multilineRaw && last.Kind = TokenKind.InterpolatedRawStringEndToken then
                runs.Add last

            segmented
        | _ -> true

    let private multilineLiteralRuns
        (text: string)
        (buffer: TokenBuffer)
        (runs: ResizeArray<Token>)
        =
        runs.Clear()
        let mutable segmented = true

        for index = 0 to buffer.TokenCount - 1 do
            segmented <- appendLiteralRuns text (buffer.Token index) runs && segmented

        segmented

    let private linesMatchWithTargetNewline
        (origSpan: ReadOnlySpan<char>)
        (changedSpan: ReadOnlySpan<char>)
        (target: ReadOnlySpan<char>)
        =
        let mutable pos1 = 0
        let mutable pos2 = 0
        let mutable ok = true
        let mutable doneLines = false

        while ok && not doneLines do
            let rem1 = origSpan.Slice(pos1)
            let rel1 = rem1.IndexOfAny('\r', '\n')
            let rem2 = changedSpan.Slice(pos2)
            let rel2 = rem2.IndexOfAny('\r', '\n')

            if (rel1 < 0) <> (rel2 < 0) then
                ok <- false
            elif rel1 < 0 then
                ok <- rem1.SequenceEqual(rem2)
                doneLines <- true
            else if not (rem1.Slice(0, rel1).SequenceEqual(rem2.Slice(0, rel2))) then
                ok <- false
            else
                let nlPos1 = pos1 + rel1
                let nlPos2 = pos2 + rel2

                let nlLen1 =
                    if
                        origSpan[nlPos1] = '\r'
                        && nlPos1 + 1 < origSpan.Length
                        && origSpan[nlPos1 + 1] = '\n'
                    then
                        2
                    else
                        1

                let nlLen2 =
                    if
                        changedSpan[nlPos2] = '\r'
                        && nlPos2 + 1 < changedSpan.Length
                        && changedSpan[nlPos2 + 1] = '\n'
                    then
                        2
                    else
                        1

                let end1 = origSpan.Slice(nlPos1, nlLen1)
                let end2 = changedSpan.Slice(nlPos2, nlLen2)
                ok <- end1.SequenceEqual(end2) || end2.SequenceEqual(target)
                pos1 <- nlPos1 + nlLen1
                pos2 <- nlPos2 + nlLen2

        ok

    let internal isValidLiteralLineEndingChange
        (options: PrinterOptions)
        (source: string)
        (left: Token)
        (formatted: string)
        (right: Token)
        =
        let isCandidate =
            match left.Kind with
            | TokenKind.StringLiteralToken
            | TokenKind.Utf8StringLiteralToken ->
                left.Length >= 2 && source[left.Start] = '@' && source[left.Start + 1] = '"'
            | TokenKind.MultiLineRawStringLiteralToken
            | TokenKind.Utf8MultiLineRawStringLiteralToken -> true
            | _ -> false

        if
            not isCandidate
            || left.Kind <> right.Kind
            || not (hasBreak source left.Start left.End)
        then
            false
        else
            let target = (newline options).AsSpan()

            linesMatchWithTargetNewline
                (source.AsSpan(left.Start, left.Length))
                (formatted.AsSpan(right.Start, right.Length))
                target

    let private multilineLiteralLineEndings options (source: string) (formatted: string) =
        if Census.enabled then
            Census.bump &Census.lineEndingEntries

        if canSkipMultilineLiteralLineEndings options source formatted then
            source
        else
            let struct (before, after) = lexPair source formatted
            let beforeRuns = ResizeArray<Token>()
            let afterRuns = ResizeArray<Token>()
            let beforeSegmented = multilineLiteralRuns source before beforeRuns
            let afterSegmented = multilineLiteralRuns formatted after afterRuns
            let edits = ResizeArray<int * int * string>()
            let target = (newline options).AsSpan()

            if beforeSegmented && afterSegmented && beforeRuns.Count = afterRuns.Count then
                for i = 0 to beforeRuns.Count - 1 do
                    let left, right = beforeRuns[i], afterRuns[i]

                    if
                        left.Kind = right.Kind
                        && hasBreak source left.Start left.End
                        && not (
                            source
                                .AsSpan(left.Start, left.Length)
                                .SequenceEqual(formatted.AsSpan(right.Start, right.Length))
                        )
                        && linesMatchWithTargetNewline
                            (source.AsSpan(left.Start, left.Length))
                            (formatted.AsSpan(right.Start, right.Length))
                            target
                    then
                        edits.Add(
                            left.Start,
                            left.Length,
                            formatted.Substring(right.Start, right.Length)
                        )

            rewrite source edits

    let rules: Rule list =
        [
            {
                Name = "using directive permutation"
                Witnessed = fun witness -> witness.SortedUsings
                RewriteInput = fun _ -> usingDirectivePermutation
            }
            {
                Name = "declaration modifier permutation"
                Witnessed = fun witness -> witness.SortedModifiers
                RewriteInput = fun _ -> modifierPermutation
            }
            {
                Name = "separated-list trailing comma"
                Witnessed = fun witness -> witness.ChangedTrailingCommas
                RewriteInput = fun _ -> trailingSeparators
            }
            {
                Name = "multiline raw-string indentation"
                Witnessed = fun witness -> witness.ReindentedRawStrings
                RewriteInput = rawStringIndentation
            }
            {
                Name = "multiline literal line endings"
                Witnessed = fun _ -> true
                RewriteInput = multilineLiteralLineEndings
            }
        ]
