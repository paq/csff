namespace Csff.Parser

open System
open System.Collections.Generic
open System.Runtime.CompilerServices
open Csff.Lexer

[<Struct>]
type private ProbeState =
    {
        SavedPosition: int
        SavedOffset: int
        Mark: struct (int * int * int * int * int * int)
        SavedSpeculative: bool
        SavedAsync: bool
        SavedField: bool
        SavedQuery: bool
        SavedForce: bool
        ProbeMark: struct (int64 * int64)
    }

type private DeclarationParser() =
    [<DefaultValue; ThreadStatic>]
    static val mutable private cached: DeclarationParser

    let mutable source = ""
    let mutable tree: SyntaxTree = Unchecked.defaultof<_>
    let mutable input: TokenInput = Unchecked.defaultof<_>

    let mutable stackFloor = StackGuard.Unproven

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let ensureStack () =
        stackFloor <- StackGuard.proven stackFloor

    let mutable contextual: ResizeArray<int> = null
    let mutable contextualHint = 0

    let mutable position = 0
    let mutable current = TokenKind.None
    let mutable next = TokenKind.None
    let mutable asyncContext = false
    let mutable fieldContext = false
    let mutable queryContext = false
    let mutable whenKeyword = true
    let mutable forceConditionalAccess = false
    let mutable speculative = false
    let mutable lambdaDelimitersComplete = false
    let mutable parametersFound = 0
    let mutable parameterHint = 0
    let mutable localBalanceWork = 0
    let mutable globalDiscovery = false
    let mutable discoveryOffset = 0
    let mutable discoveryIndex = 0
    let mutable tupleSpineDepths: Dictionary<int, int> = null
    let mutable expressionHasColonFn: (int -> bool) = Unchecked.defaultof<_>
    let mutable queryKeywordAtFn: (int -> bool) = Unchecked.defaultof<_>

    let mutable expressionEnds
        : Dictionary<
              struct (int * int * bool * bool * bool * bool * bool),
              struct (int * int * NodeKind * bool)
           > =
        null

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let children () = tree.NewChildren()

    static member Acquire() =
        let current = DeclarationParser.cached

        if isNull (box current) then
            DeclarationParser()
        else
            DeclarationParser.cached <- Unchecked.defaultof<_>
            current

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrepareInput() =
        let prepareMark = ParseStats.enter ()
        let lexer = tree.LexerBuffer
        contextual <- lexer.ContextualOffsets

        tree.InputMayHoldIncomplete <- lexer.HasBadToken

        if not lexer.HasInterpolated then
            input.BorrowFrom(
                lexer.TokensStorage,
                lexer.TokenCount,
                lexer.LastArrowOffset,
                lexer.LastParenArrowOffset
            )
        else
            input.Clear()
            let merged = tree.ContextualOffsets
            merged.Clear()
            contextual <- merged
            let count = lexer.TokenCount

            let addHoleToken (token: Token) =
                if
                    token.Kind = TokenKind.IdentifierToken
                    && uint32 (token.Length - 3) <= 2u
                    && Lexer.isContextualWord source token.Start token.Length
                then
                    merged.Add token.Start

                if SyntaxTree.IsIncomplete token then
                    tree.InputMayHoldIncomplete <- true

                input.Add token

            input.EnsureCapacity(count + min 2048 (count >>> 2) + 128)

            let rec append (token: Token) =
                if token.Kind = TokenKind.InterpolatedStringToken then
                    ensureStack ()
                    let expanded = InterpolationLexer.expand source token tree
                    let mutable hasNested = false
                    let mutable j = 0

                    while not hasNested && j < expanded.Count do
                        hasNested <- expanded[j].Kind = TokenKind.InterpolatedStringToken
                        j <- j + 1

                    if hasNested then
                        let snapshot = expanded.ToArray()

                        for item in snapshot do
                            append item
                    else
                        for k = 0 to expanded.Count - 1 do
                            addHoleToken expanded[k]
                else
                    addHoleToken token

            let lexed = lexer.TokensStorage
            let mutable run = 0
            let mutable arrow = 0
            let words = lexer.ContextualOffsets
            let mutable word = 0

            let inline copyRun (run: int) (arrow0: int) (word0: int) (finish: int) =
                let shift = input.Count - run
                input.AddRange(ReadOnlySpan<Token>(lexed, run, finish - run))

                let limit =
                    if finish < lexer.TokenCount then
                        lexed[finish].Start
                    else
                        Int32.MaxValue

                let mutable w = word0

                while w < words.Count && words[w] < limit do
                    merged.Add words[w]
                    w <- w + 1

                let mutable a = arrow0

                while a < lexer.ParenArrowCount && lexer.ParenArrow a < finish do
                    let close = lexer.ParenArrow a
                    input.AddParenArrow(lexed[close].Start, close + shift)
                    a <- a + 1

                struct (a, w)

            for k = 0 to lexer.InterpolatedCount - 1 do
                let i = lexer.Interpolated k
                let struct (nextArrow, nextWord) = copyRun run arrow word i
                arrow <- nextArrow
                word <- nextWord
                append lexed[i]
                run <- i + 1

            let struct (nextArrow, nextWord) = copyRun run arrow word lexer.TokenCount
            arrow <- nextArrow
            word <- nextWord
            input.MergeArrows(lexer.LastArrowOffset, lexer.LastParenArrowOffset)

        ParseStats.lapse ParseStats.tPrepare prepareMark
        ParseStats.bump ParseStats.nInputTokens input.Count

    member private _.CursorAt(offset: int, hint: int) =
        if hint < input.Count && input[hint].Start = offset then
            hint
        else
            let mutable first, last = 0, input.Count - 1

            while first < last do
                let middle = first + (last - first) / 2

                if input[middle].Start < offset then
                    first <- middle + 1
                else
                    last <- middle

            first

    member private _.BeginProbe() =
        let savedPosition, savedOffset = position, input[position].Start
        let mark = tree.Checkpoint()
        let savedSpeculative = speculative
        ParseStats.event ParseStats.nProbes

        let probeMark =
            if savedSpeculative then
                struct (0L, 0L)
            else
                ParseStats.enter ()

        let state =
            {
                SavedPosition = savedPosition
                SavedOffset = savedOffset
                Mark = mark
                SavedSpeculative = savedSpeculative
                SavedAsync = asyncContext
                SavedField = fieldContext
                SavedQuery = queryContext
                SavedForce = forceConditionalAccess
                ProbeMark = probeMark
            }

        speculative <- true
        state

    member private this.EndProbe(state: ProbeState) =
        tree.Restore state.Mark
        this.MoveTo(this.CursorAt(state.SavedOffset, state.SavedPosition))
        speculative <- state.SavedSpeculative
        asyncContext <- state.SavedAsync
        fieldContext <- state.SavedField
        queryContext <- state.SavedQuery
        forceConditionalAccess <- state.SavedForce

        if not state.SavedSpeculative then
            ParseStats.lapse ParseStats.tProbe state.ProbeMark

    member private this.ExpressionHasColon(cursor: int) =
        let state = this.BeginProbe()

        try
            this.MoveTo(cursor)
            this.Expression() |> ignore
            this.At TokenKind.ColonToken
        finally
            this.EndProbe state

    member private this.QueryKeywordAt(cursor: int) = this.QueryKeyword(cursor - position)

    member private this.EnsureTypeCallbacks() =
        if isNull (box expressionHasColonFn) then
            expressionHasColonFn <- this.ExpressionHasColon
            queryKeywordAtFn <- this.QueryKeywordAt

    member private this.ScanType(start, mode) =
        ParseStats.event ParseStats.nScanTypes
        this.EnsureTypeCallbacks()

        ExpressionSyntax.scanType source input start mode expressionHasColonFn queryKeywordAtFn

    member private _.Kind = current

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.MoveTo(target: int) =
        position <- min target (input.Count - 1)
        current <- input.KindAt target
        next <- input.KindAt(target + 1)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.Advance() =
        position <- position + 1
        current <- next
        next <- input.KindAt(position + 1)

    member private _.Refresh() =
        current <- input.KindAt position
        next <- input.KindAt(position + 1)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.CurrentRef() : inref<Token> =
        &input.ItemRef(min position (input.Count - 1))

    member private _.Start = tree.TokenCount

    member private _.At(kind) = current = kind

    member private _.Peek(distance) = input.KindAt(position + distance)

    member private _.Next = next

    member private _.WordText(start: int, word: string) =
        source.AsSpan(start, word.Length).SequenceEqual(word.AsSpan())

    member private _.ContextualAtCursor(offset: int) =
        let list = contextual
        let mutable hint = contextualHint

        if hint > 0 && list[hint - 1] >= offset then
            list.BinarySearch offset >= 0
        else
            while hint < list.Count && list[hint] < offset do
                hint <- hint + 1

            contextualHint <- hint
            hint < list.Count && list[hint] = offset

    member private this.Word(distance, word: string) =
        let token = &input.ItemRef(min (position + distance) (input.Count - 1))

        token.Kind = TokenKind.IdentifierToken
        && token.Length = word.Length
        && source[token.Start] = word[0]
        && this.WordText(token.Start, word)

    member private _.ContainsKind(first: int, finish: int, kind: TokenKind) =
        let mutable cursor, found = first, false

        while cursor < finish && cursor < input.Count && not found do
            found <- input[cursor].Kind = kind
            cursor <- cursor + 1

        found

    member private this.QueryKeyword(distance: int) =
        queryContext
        && (this.Word(distance, "from")
            || this.Word(distance, "let")
            || this.Word(distance, "where")
            || this.Word(distance, "join")
            || this.Word(distance, "on")
            || this.Word(distance, "equals")
            || this.Word(distance, "into")
            || this.Word(distance, "orderby")
            || this.Word(distance, "ascending")
            || this.Word(distance, "descending")
            || this.Word(distance, "select")
            || this.Word(distance, "group")
            || this.Word(distance, "by"))

    member private this.Take(items: ChildList, promoted: TokenKind) =
        let last = input.Count - 1

        let index =
            if promoted = TokenKind.None then
                tree.AddTokenRef(&input.ItemRef(min position last))
            else
                tree.AddToken
                    { input[min position last] with
                        Kind = promoted
                    }

        items.Add(~~~index)

        if position < last then
            this.Advance()

    member private this.Take(items: ChildList) =
        let last = input.Count - 1
        items.Add(~~~(tree.AddTokenRef(&input.ItemRef(position))))

        if position < last then
            this.Advance()

    member private this.TakeChild() : int =
        let last = input.Count - 1
        let index = tree.AddTokenRef(&input.ItemRef(position))

        if position < last then
            this.Advance()

        ~~~index

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.Expect(items: ChildList, kind: TokenKind) =
        if this.At kind then
            this.Take items
        else
            this.ExpectMissing(items, kind)

    member private _.ExpectMissing(items: ChildList, kind: TokenKind) =
        let next = input[min position (input.Count - 1)]

        if kind = TokenKind.InterpolatedStringTextToken then
            tree.Recover()

        items.Add(
            ~~~(tree.AddToken
                    { next with
                        Kind = kind
                        Length = 0
                        LeadingCount = 0
                        TrailingCount = 0
                    })
        )

    member private this.ExpectWord(items: ChildList, word: string, kind: TokenKind) =
        if this.Word(0, word) then
            this.Take(items, kind)
        else
            this.Expect(items, kind)

    member private _.Make(kind: NodeKind, start: int, items: ChildList) : int =
        tree.MakeNode(kind, start, items)

    member private this.Single(kind: NodeKind) : int =
        let start = this.Start
        let last = input.Count - 1
        let child = ~~~(tree.AddTokenRef(&input.ItemRef(position)))

        if position < last then
            this.Advance()

        tree.AddLeaf(kind, start, child)

    member private this.CloseTypeArguments(items: ChildList) =
        let token = input[position]

        if token.Length > 1 && ExpressionSyntax.closing token.Kind then
            let struct (greaters, equals) = ExpressionSyntax.runShape token.Kind
            let rest = greaters - 1

            let joined =
                if equals || position + 1 >= input.Count then
                    TokenKind.None
                else
                    let next = input[position + 1]
                    let struct (nextGreaters, nextEquals) = ExpressionSyntax.runShape next.Kind

                    if
                        nextGreaters > 0
                        && next.Start = token.Start + token.Length
                        && next.LeadingCount = 0
                    then
                        ExpressionSyntax.runToken (rest + nextGreaters) nextEquals
                    else
                        TokenKind.None

            input[position] <-
                { token with
                    Kind = TokenKind.GreaterThanToken
                    Length = 1
                    TrailingCount = 0
                }

            if joined <> TokenKind.None then
                let next = input[position + 1]

                input[position + 1] <-
                    { next with
                        Kind = joined
                        Start = token.Start + 1
                        Length = next.Start + next.Length - token.Start - 1
                        TriviaStart = next.TriviaStart + next.LeadingCount
                        LeadingCount = 0
                    }
            else
                input.Insert(
                    position + 1,
                    { token with
                        Kind = ExpressionSyntax.residual token.Kind 1
                        Start = token.Start + 1
                        Length = token.Length - 1
                        TriviaStart = token.TriviaStart + token.LeadingCount
                        LeadingCount = 0
                    }
                )

            this.Refresh()

        this.Expect(items, TokenKind.GreaterThanToken)

    member private this.SimpleName() : int =
        if
            this.At TokenKind.IdentifierToken
            && (let next = this.Next in
                next <> TokenKind.LessThanToken && next <> TokenKind.ColonColonToken)
        then
            this.Single NodeKind.IdentifierName
        else
            let start, items = this.Start, children ()

            if this.Word(0, "global") && this.Next = TokenKind.ColonColonToken then
                this.Take(items, TokenKind.GlobalKeyword)
            else
                this.Expect(items, TokenKind.IdentifierToken)

            if this.At TokenKind.LessThanToken then
                let argStart, args = this.Start, children ()
                this.Take args
                let mutable more = true

                while more && not (this.At TokenKind.EndOfFileToken) do
                    let before = position

                    if
                        this.At TokenKind.CommaToken
                        || (input[position].Length > 0
                            && ExpressionSyntax.closing input[position].Kind)
                    then
                        let omittedStart, omitted = this.Start, children ()
                        this.Expect(omitted, TokenKind.OmittedTypeArgumentToken)
                        args.Add(this.Make(NodeKind.OmittedTypeArgument, omittedStart, omitted))
                    else
                        args.Add(this.Type())

                    if this.At TokenKind.CommaToken then
                        this.Take args
                    else
                        more <- false

                    if position = before then
                        more <- false

                this.CloseTypeArguments args
                items.Add(this.Make(NodeKind.TypeArgumentList, argStart, args))
                this.Make(NodeKind.GenericName, start, items)
            else
                this.Make(NodeKind.IdentifierName, start, items)

    member private this.Name() : int =
        let start = this.Start
        let mutable name = this.SimpleName()
        let mutable more = true

        while more do
            if this.At TokenKind.DotToken || this.At TokenKind.ColonColonToken then
                let kind =
                    if this.At TokenKind.ColonColonToken then
                        NodeKind.AliasQualifiedName
                    else
                        NodeKind.QualifiedName

                let separator = this.TakeChild()
                let before = position
                name <- tree.AddNode3(kind, start, name, separator, this.SimpleName())
                more <- position <> before
            else
                more <- false

        name

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.FunctionPointerType() : int =
        let start, items = this.Start, children ()
        this.Take items
        this.Expect(items, TokenKind.AsteriskToken)

        if this.Word(0, "managed") || this.Word(0, "unmanaged") then
            let conventionStart, convention = this.Start, children ()

            this.Take(
                convention,
                if this.Word(0, "managed") then
                    TokenKind.ManagedKeyword
                else
                    TokenKind.UnmanagedKeyword
            )

            if this.At TokenKind.OpenBracketToken then
                let listStart, list = this.Start, children ()
                this.Take list
                let mutable more = not (this.At TokenKind.CloseBracketToken)

                while more && not (this.At TokenKind.EndOfFileToken) do
                    let before, nameStart, name = position, this.Start, children ()
                    this.Expect(name, TokenKind.IdentifierToken)

                    list.Add(
                        this.Make(
                            NodeKind.FunctionPointerUnmanagedCallingConvention,
                            nameStart,
                            name
                        )
                    )

                    if this.At TokenKind.CommaToken then
                        this.Take list
                    else
                        more <- false

                    if position = before then
                        more <- false

                this.Expect(list, TokenKind.CloseBracketToken)

                convention.Add(
                    this.Make(
                        NodeKind.FunctionPointerUnmanagedCallingConventionList,
                        listStart,
                        list
                    )
                )

            items.Add(
                this.Make(NodeKind.FunctionPointerCallingConvention, conventionStart, convention)
            )

        let parameterStart, parameters = this.Start, children ()
        this.Expect(parameters, TokenKind.LessThanToken)
        let mutable more = true

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before, paramStart, param = position, this.Start, children ()
            this.Attributes param

            while this.At TokenKind.RefKeyword
                  || this.At TokenKind.InKeyword
                  || this.At TokenKind.OutKeyword
                  || this.At TokenKind.ReadOnlyKeyword do
                this.Take param

            param.Add(this.Type())
            parameters.Add(this.Make(NodeKind.FunctionPointerParameter, paramStart, param))

            if this.At TokenKind.CommaToken then
                this.Take parameters
            else
                more <- false

            if position = before then
                more <- false

        this.CloseTypeArguments parameters
        items.Add(this.Make(NodeKind.FunctionPointerParameterList, parameterStart, parameters))
        this.Make(NodeKind.FunctionPointerType, start, items)

    member private this.Type() : int = this.Type(false)

    member private this.Type(arraySizes: bool) : int = this.Type(arraySizes, input.Count)

    member private this.Type(arraySizes: bool, finish: int) : int =
        this.Type(arraySizes, finish, ExpressionSyntax.Normal)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.RefOrScopedType(start: int) : int =
        let items = children ()
        let scoped = this.Word(0, "scoped")

        if scoped then
            this.Take(items, TokenKind.ScopedKeyword)
        else
            this.Take items

        if this.At TokenKind.ReadOnlyKeyword then
            this.Take items

        items.Add(this.Type())
        this.Make((if scoped then NodeKind.ScopedType else NodeKind.RefType), start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TupleType(start: int) : int =
        let items = children ()
        this.Take items
        let mutable more = true

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before, elementStart, element = position, this.Start, children ()
            element.Add(this.Type())

            if this.At TokenKind.IdentifierToken then
                this.Take element

            items.Add(this.Make(NodeKind.TupleElement, elementStart, element))

            if this.At TokenKind.CommaToken then
                this.Take items
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, TokenKind.CloseParenToken)
        this.Make(NodeKind.TupleType, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ArrayType(start: int, baseType: int) : int =
        let items = children ()
        items.Add baseType

        while this.At TokenKind.OpenBracketToken do
            let rankStart, rank = this.Start, children ()
            this.Take rank
            let mutable moreRanks = true

            while moreRanks do
                if this.At TokenKind.CommaToken || this.At TokenKind.CloseBracketToken then
                    let omittedStart, omitted = this.Start, children ()
                    this.Expect(omitted, TokenKind.OmittedArraySizeExpressionToken)

                    rank.Add(this.Make(NodeKind.OmittedArraySizeExpression, omittedStart, omitted))
                else
                    rank.Add(this.Expression())

                if this.At TokenKind.CommaToken then
                    this.Take rank
                else
                    moreRanks <- false

            this.Expect(rank, TokenKind.CloseBracketToken)
            items.Add(this.Make(NodeKind.ArrayRankSpecifier, rankStart, rank))

        this.Make(NodeKind.ArrayType, start, items)

    member private this.Type(arraySizes: bool, finish: int, mode: ExpressionSyntax.TypeMode) : int =
        match next with
        | TokenKind.LessThanToken
        | TokenKind.DotToken
        | TokenKind.ColonColonToken
        | TokenKind.QuestionToken
        | TokenKind.AsteriskToken
        | TokenKind.OpenBracketToken -> this.TypeCore(arraySizes, finish, mode)
        | _ ->
            if current = TokenKind.IdentifierToken && not (this.Word(0, "scoped")) then
                this.Single NodeKind.IdentifierName
            elif ExpressionSyntax.predefined current then
                this.Single NodeKind.PredefinedType
            else
                this.TypeCore(arraySizes, finish, mode)

    member private this.TypeCore
        (arraySizes: bool, finish: int, mode: ExpressionSyntax.TypeMode)
        : int =
        ensureStack ()
        let start = this.Start

        let finish =
            if finish < input.Count then
                input[finish].Start
            else
                source.Length

        let mutable result =
            if
                int this.Kind >= int TokenKind.BoolKeyword
                && int this.Kind <= int TokenKind.ObjectKeyword
            then
                this.Single NodeKind.PredefinedType
            elif this.At TokenKind.RefKeyword || this.IsScopedType(position) then
                this.RefOrScopedType start
            elif this.At TokenKind.DelegateKeyword && this.Peek(1) = TokenKind.AsteriskToken then
                this.FunctionPointerType()
            elif this.At TokenKind.OpenParenToken then
                this.TupleType start
            else
                this.Name()

        let mutable more = true

        while more && input[position].Start < finish do
            if
                (this.At TokenKind.QuestionToken
                 && (tree.Node result).Kind <> NodeKind.NullableType
                 && (tree.Node result).Kind <> NodeKind.PointerType
                 && (mode = ExpressionSyntax.Normal
                     || (this.EnsureTypeCallbacks()

                         ExpressionSyntax.nullableQualifier
                             source
                             input
                             mode
                             position
                             expressionHasColonFn
                             queryKeywordAtFn)))
                || this.At TokenKind.AsteriskToken
            then
                let nullable = this.At TokenKind.QuestionToken
                let items = children ()
                items.Add result
                this.Take items

                result <-
                    this.Make(
                        (if nullable then
                             NodeKind.NullableType
                         else
                             NodeKind.PointerType),
                        start,
                        items
                    )
            elif
                this.At TokenKind.OpenBracketToken
                && (arraySizes
                    || this.Next = TokenKind.CloseBracketToken
                    || this.Next = TokenKind.CommaToken)
            then
                result <- this.ArrayType(start, result)
            else
                more <- false

        result

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.InterpolatedString() : int =
        let previousForce, previousQuery = forceConditionalAccess, queryContext
        forceConditionalAccess <- false
        queryContext <- false
        let start, items = this.Start, children ()
        this.Take items

        let inline isEnd () =
            this.At TokenKind.InterpolatedStringEndToken
            || this.At TokenKind.InterpolatedRawStringEndToken
            || this.At TokenKind.EndOfFileToken

        while not (isEnd ()) do
            let before = position

            if this.At TokenKind.InterpolatedStringTextToken then
                items.Add(this.Single NodeKind.InterpolatedStringText)
            elif this.At TokenKind.OpenBraceToken then
                let holeStart, hole = this.Start, children ()
                this.Take hole
                hole.Add(this.Expression())

                if this.At TokenKind.CommaToken then
                    let alignStart, alignment = this.Start, children ()
                    this.Take alignment
                    alignment.Add(this.Expression())

                    hole.Add(
                        this.Make(NodeKind.InterpolationAlignmentClause, alignStart, alignment)
                    )

                if this.At TokenKind.ColonToken then
                    let formatStart, format = this.Start, children ()
                    this.Take format
                    this.Expect(format, TokenKind.InterpolatedStringTextToken)
                    hole.Add(this.Make(NodeKind.InterpolationFormatClause, formatStart, format))

                this.SkipUntil(
                    hole,
                    struct (TokenKind.CloseBraceToken,
                            TokenKind.InterpolatedStringEndToken,
                            TokenKind.InterpolatedRawStringEndToken,
                            TokenKind.None,
                            TokenKind.None)
                )

                this.Expect(hole, TokenKind.CloseBraceToken)
                items.Add(this.Make(NodeKind.Interpolation, holeStart, hole))
            else
                this.Take items

            if position = before then
                this.Skip items

        if not (this.At TokenKind.EndOfFileToken) then
            this.Take items
        else
            this.Expect(items, TokenKind.InterpolatedStringEndToken)

        forceConditionalAccess <- previousForce
        queryContext <- previousQuery
        this.Make(NodeKind.InterpolatedStringExpression, start, items)

    member private this.ExpressionName() : int =
        if this.Next = TokenKind.LessThanToken then
            let struct (valid, cursor, offset, definite) =
                ExpressionSyntax.scan input (position + 1) true

            let follower =
                if offset = 0 then
                    input[min cursor (input.Count - 1)].Kind
                else
                    ExpressionSyntax.residual input[cursor].Kind offset

            if valid && (definite || ExpressionSyntax.genericFollower follower) then
                this.SimpleName()
            else
                this.Single NodeKind.IdentifierName
        else
            this.SimpleName()

    member private this.AliasExpression() : int =
        let start, alias = this.Start, children ()

        if this.Word(0, "global") then
            this.Take(alias, TokenKind.GlobalKeyword)
        else
            this.Expect(alias, TokenKind.IdentifierToken)

        let aliasNode = this.Make(NodeKind.IdentifierName, start, alias)
        let items = children ()
        items.Add aliasNode
        this.Expect(items, TokenKind.ColonColonToken)
        items.Add(this.ExpressionName())
        this.Make(NodeKind.AliasQualifiedName, start, items)

    member private this.BalanceFrom(cursor: int, endOffset: outref<int>, endHint: outref<int>) =
        let kind =
            if cursor < input.Count then
                input.KindOf cursor
            else
                TokenKind.None

        if kind <> TokenKind.OpenParenToken && kind <> TokenKind.OpenBracketToken then
            false
        else
            let parentheses, brackets = tree.LocalParentheses, tree.LocalBrackets
            parentheses.Clear()
            brackets.Clear()
            let mutable index = cursor
            let mutable found = false

            while not found && index < input.Count do
                let kind = input.KindOf index

                match kind with
                | TokenKind.OpenParenToken -> parentheses.Add index
                | TokenKind.OpenBracketToken -> brackets.Add index
                | _ ->
                    let stack =
                        if kind = TokenKind.CloseParenToken then
                            parentheses
                        else
                            brackets

                    if stack.Count > 0 then
                        let start = stack[stack.Count - 1]
                        stack.RemoveAt(stack.Count - 1)
                        let tokenStart = input.ItemRef(index).Start
                        input.SetEnd(start, tokenStart, index)

                        if start = cursor then
                            found <- true
                            endOffset <- tokenStart
                            endHint <- index

                index <- input.NextDelimiter(index + 1)

            tree.AddLambdaBalanceVisits(index - cursor)
            localBalanceWork <- localBalanceWork + (index - cursor)

            if not found then
                for waiting in parentheses do
                    input.SetEnd(waiting, -1, -1)

                for waiting in brackets do
                    input.SetEnd(waiting, -1, -1)

                endOffset <- -1

            if localBalanceWork > 4 * input.Count + 64 then
                globalDiscovery <- true

            true

    member private this.LambdaDelimiterEnd(cursor: int) =
        let mutable endOffset = 0
        let mutable endHint = 0
        let mutable recorded = input.TryEnd(cursor, &endOffset, &endHint)

        if not recorded && not globalDiscovery then
            recorded <- this.BalanceFrom(cursor, &endOffset, &endHint)

        if not recorded && not lambdaDelimitersComplete then
            let parentheses, brackets = tree.LambdaParentheses, tree.LambdaBrackets
            let opening = input.ItemRef(cursor).Start
            let first = this.CursorAt(discoveryOffset, discoveryIndex)
            let mutable index = input.NextDelimiter first

            while not recorded && index < input.Count do
                let kind = input.KindOf index

                match kind with
                | TokenKind.OpenParenToken ->
                    parentheses.Add(struct (input.ItemRef(index).Start, index))
                | TokenKind.OpenBracketToken ->
                    brackets.Add(struct (input.ItemRef(index).Start, index))
                | _ ->
                    let stack =
                        if kind = TokenKind.CloseParenToken then
                            parentheses
                        else
                            brackets

                    if stack.Count > 0 then
                        let struct (start, startIndex) = stack[stack.Count - 1]
                        stack.RemoveAt(stack.Count - 1)
                        let tokenStart = input.ItemRef(index).Start
                        input.SetEnd(this.CursorAt(start, startIndex), tokenStart, index)

                        if start = opening then
                            recorded <- true
                            endOffset <- tokenStart
                            endHint <- index

                index <- input.NextDelimiter(index + 1)

            tree.AddLambdaBalanceVisits(index - first)

            if index < input.Count then
                discoveryOffset <- input.ItemRef(index).Start
                discoveryIndex <- index
            else
                lambdaDelimitersComplete <- true

        if recorded && endOffset >= 0 then
            let closing = this.CursorAt(endOffset, endHint)

            if closing <> endHint then
                input.SetEnd(cursor, endOffset, closing)

            closing + 1
        else
            input.Count

    member private this.FindParameterLists() =
        let openings, tuples = tree.ParameterOpenings, tree.TupleOpenings
        openings.Clear()
        tuples.Clear()
        let mutable budget = 4 * input.Count + 64

        let inline back (budget0: int) (close: int) (openKind: TokenKind) (closeKind: TokenKind) =
            let mutable b = budget0
            let mutable depth = 1
            let mutable cursor = close - 1

            while cursor >= 0 && depth > 0 && b > 0 do
                let kind = input.KindOf cursor

                if kind = closeKind then
                    depth <- depth + 1
                elif kind = openKind then
                    depth <- depth - 1

                b <- b - 1

                if depth > 0 then
                    cursor <- cursor - 1

            struct ((if depth = 0 then cursor else -1), b)

        let inline find (budget0: int) (offset: int) (hint: int) =
            let struct (opening, b1) =
                back
                    budget0
                    (this.CursorAt(offset, hint))
                    TokenKind.OpenParenToken
                    TokenKind.CloseParenToken

            let mutable b = b1

            if opening >= 0 then
                openings.Add(input.ItemRef(opening).Start)
                let mutable last = opening - 1
                let mutable more = true

                while more && last >= 0 do
                    match input.KindOf last with
                    | TokenKind.QuestionToken
                    | TokenKind.AsteriskToken -> last <- last - 1
                    | TokenKind.CloseBracketToken ->
                        let struct (brk, b2) =
                            back b last TokenKind.OpenBracketToken TokenKind.CloseBracketToken

                        b <- b2
                        last <- brk - 1

                        if last < -1 then
                            more <- false
                    | _ -> more <- false

                if last >= 0 && input.KindOf last = TokenKind.CloseParenToken then
                    let struct (tuple, b3) =
                        back b last TokenKind.OpenParenToken TokenKind.CloseParenToken

                    b <- b3

                    if tuple >= 0 then
                        tuples.Add(input.ItemRef(tuple).Start)

            b

        let lexer = tree.LexerBuffer

        if lexer.HasInterpolated then
            let recorded = input.ParenArrows

            for i = 0 to recorded.Count - 1 do
                let struct (offset, hint) = recorded[i]
                budget <- find budget offset hint
        else
            for i = 0 to lexer.ParenArrowCount - 1 do
                let close = lexer.ParenArrow i
                budget <- find budget (lexer.Token(close).Start) close

        openings.Sort()
        tuples.Sort()
        parametersFound <- if budget > 0 then 1 else -1

    static member private Holds(sorted: ResizeArray<int>, offset: int) =
        let span = System.Runtime.InteropServices.CollectionsMarshal.AsSpan sorted
        let mutable low = 0
        let mutable high = span.Length - 1
        let mutable found = false

        while not found && low <= high do
            let middle = (low + high) >>> 1
            let value = span[middle]

            if value = offset then found <- true
            elif value < offset then low <- middle + 1
            else high <- middle - 1

        found

    member private this.ArrowFollowsClose(opening: int) =
        if opening >= input.Count || input.KindOf opening <> TokenKind.OpenParenToken then
            false
        else
            if parametersFound = 0 then
                this.FindParameterLists()

            if parametersFound > 0 then
                let openings = tree.ParameterOpenings
                let offset = input.ItemRef(opening).Start
                let mutable hint = parameterHint

                if hint > 0 && openings[hint - 1] >= offset then
                    DeclarationParser.Holds(openings, offset)
                else
                    while hint < openings.Count && openings[hint] < offset do
                        hint <- hint + 1

                    parameterHint <- hint
                    hint < openings.Count && openings[hint] = offset
            else
                let after = this.LambdaDelimiterEnd opening
                after < input.Count && input.KindOf after = TokenKind.EqualsGreaterThanToken

    member private this.MayOpenTupleReturnType(opening: int) =
        if parametersFound = 0 then
            this.FindParameterLists()

        parametersFound < 0
        || DeclarationParser.Holds(tree.TupleOpenings, input.ItemRef(opening).Start)

    member private this.SkipTypeSuffixes(start: int) =
        let mutable cursor = start
        let mutable more = true

        while more && cursor < input.Count do
            match input[cursor].Kind with
            | TokenKind.QuestionToken
            | TokenKind.AsteriskToken -> cursor <- cursor + 1
            | TokenKind.OpenBracketToken ->
                let afterBracket = this.LambdaDelimiterEnd cursor

                if
                    afterBracket > cursor + 1
                    && afterBracket <= input.Count
                    && input[afterBracket - 1].Kind = TokenKind.CloseBracketToken
                then
                    cursor <- afterBracket
                else
                    more <- false
            | _ -> more <- false

        cursor

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TupleSpineValid(start: int, afterParen: int) =
        if start + 1 >= input.Count || input[start + 1].Kind <> TokenKind.OpenParenToken then
            true
        else
            if isNull tupleSpineDepths then
                tupleSpineDepths <- tree.TupleSpineDepths

            let mutable stop = start
            let mutable stopDepth = -1

            while stopDepth < 0 do
                match tupleSpineDepths.TryGetValue(input[stop].Start) with
                | true, cached -> stopDepth <- cached
                | _ ->
                    if
                        stop + 1 >= input.Count || input[stop + 1].Kind <> TokenKind.OpenParenToken
                    then
                        stopDepth <- 0
                        tupleSpineDepths[input[stop].Start] <- 0
                    else
                        let outerEnd =
                            if stop = start then
                                afterParen
                            else
                                this.LambdaDelimiterEnd stop

                        let innerEnd = this.LambdaDelimiterEnd(stop + 1)

                        if
                            outerEnd <= stop + 4
                            || outerEnd > input.Count
                            || input[outerEnd - 1].Kind <> TokenKind.CloseParenToken
                            || innerEnd <= stop + 5
                            || innerEnd >= outerEnd
                            || input[innerEnd - 1].Kind <> TokenKind.CloseParenToken
                        then
                            stopDepth <- 129
                            tupleSpineDepths[input[stop].Start] <- 129
                        else
                            let mutable afterElem = this.SkipTypeSuffixes innerEnd

                            if
                                afterElem < outerEnd - 1
                                && input[afterElem].Kind = TokenKind.IdentifierToken
                            then
                                afterElem <- afterElem + 1

                            if
                                afterElem < outerEnd - 1
                                && input[afterElem].Kind = TokenKind.CommaToken
                            then
                                stop <- stop + 1
                            else
                                stopDepth <- 129
                                tupleSpineDepths[input[stop].Start] <- 129

            let mutable depth = stopDepth

            for i = stop - 1 downto start do
                depth <- min 129 (depth + 1)
                tupleSpineDepths[input[i].Start] <- depth

            depth < 128

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TupleTypeEnd(start: int, follower: TokenKind) =
        let afterParen = this.LambdaDelimiterEnd start

        if
            afterParen <= start + 4
            || afterParen > input.Count
            || input[afterParen - 1].Kind <> TokenKind.CloseParenToken
        then
            -1
        else
            let afterTuple = this.SkipTypeSuffixes afterParen

            if
                afterTuple < input.Count
                && input[afterTuple].Kind = follower
                && this.TupleSpineValid(start, afterParen)
            then
                afterTuple
            else
                -1

    member private this.SkipBalanced(cursor: byref<int>, openKind: TokenKind) =
        if cursor < input.Count && input.KindOf cursor = openKind then
            cursor <- this.LambdaDelimiterEnd cursor
            cursor < input.Count
        else
            false

    member private this.LambdaCursor() =
        ParseStats.event ParseStats.nLambdaCursors

        if input.ItemRef(position).Start >= input.LastArrowOffset then
            -1
        elif
            current = TokenKind.IdentifierToken
            && (next = TokenKind.OpenParenToken || next = TokenKind.DotToken)
            && not (
                input.ItemRef(position).Length = 5
                && this.ContextualAtCursor(input.ItemRef(position).Start)
                && this.Word(0, "async")
            )
        then
            if input.ItemRef(position).Start >= input.LastParenArrowOffset then
                -1
            else
                let mutable head = position + 1

                while input.KindAt head = TokenKind.DotToken
                      && input.KindAt(head + 1) = TokenKind.IdentifierToken
                      && head + 1 < input.Count do
                    head <- head + 2

                if head < input.Count && input.KindOf head = TokenKind.OpenParenToken then
                    if this.ArrowFollowsClose head then head else -1
                elif
                    head < input.Count
                    && (match input.KindOf head with
                        | TokenKind.LessThanToken
                        | TokenKind.OpenBracketToken
                        | TokenKind.QuestionToken
                        | TokenKind.AsteriskToken
                        | TokenKind.ColonColonToken -> true
                        | _ -> false)
                then
                    this.LambdaCursorFull()
                else
                    -1
        else
            this.LambdaCursorFull()

    member private this.LambdaCursorFull() =
        if input[position].Start >= input.LastArrowOffset then
            -1
        else

            let firstKind = input.KindAt position

            if
                firstKind = TokenKind.IdentifierToken
                && input.KindAt(position + 1) = TokenKind.EqualsGreaterThanToken
            then
                position
            elif
                firstKind <> TokenKind.IdentifierToken
                && firstKind <> TokenKind.OpenParenToken
                && firstKind <> TokenKind.OpenBracketToken
                && firstKind <> TokenKind.StaticKeyword
                && firstKind <> TokenKind.RefKeyword
                && firstKind <> TokenKind.DelegateKeyword
                && not (ExpressionSyntax.predefined firstKind)
            then
                -1
            elif
                firstKind = TokenKind.IdentifierToken
                && (input[position].Length <> 5 || source[input[position].Start] <> 'a')
                && (match input.KindAt(position + 1) with
                    | TokenKind.OpenParenToken
                    | TokenKind.DotToken
                    | TokenKind.LessThanToken
                    | TokenKind.OpenBracketToken
                    | TokenKind.QuestionToken
                    | TokenKind.AsteriskToken
                    | TokenKind.ColonColonToken -> false
                    | _ -> true)
            then
                -1
            else
                let mutable cursor = position

                while cursor < input.Count && input.KindOf cursor = TokenKind.OpenBracketToken do
                    this.SkipBalanced(&cursor, TokenKind.OpenBracketToken) |> ignore

                while cursor < input.Count
                      && (input.KindOf cursor = TokenKind.StaticKeyword
                          || (this.Word(cursor - position, "async")
                              && this.Peek(cursor - position + 1)
                                 <> TokenKind.EqualsGreaterThanToken)) do
                    cursor <- cursor + 1

                let mutable parameters = cursor
                let mutable valid = false

                if
                    cursor < input.Count
                    && input.KindOf cursor = TokenKind.IdentifierToken
                    && cursor + 1 < input.Count
                    && input.KindOf(cursor + 1) = TokenKind.EqualsGreaterThanToken
                then
                    valid <- true
                elif
                    parameters < input.Count && input[parameters].Start < input.LastParenArrowOffset
                then
                    valid <- this.ArrowFollowsClose cursor

                    if not valid then
                        let start = parameters

                        let canStartReturnType =
                            if start >= input.Count then
                                false
                            else
                                match input.KindOf start with
                                | TokenKind.IdentifierToken ->
                                    if start + 1 >= input.Count then
                                        false
                                    else
                                        match input.KindOf(start + 1) with
                                        | TokenKind.OpenParenToken ->
                                            cursor <- start + 1
                                            parameters <- start + 1
                                            valid <- this.ArrowFollowsClose(start + 1)
                                            false
                                        | TokenKind.DotToken ->
                                            let mutable d = start + 1

                                            while d + 1 < input.Count
                                                  && input.KindOf d = TokenKind.DotToken
                                                  && input.KindOf(d + 1) = TokenKind.IdentifierToken do
                                                d <- d + 2

                                            if
                                                d < input.Count
                                                && input.KindOf d = TokenKind.OpenParenToken
                                            then
                                                cursor <- d
                                                parameters <- d
                                                valid <- this.ArrowFollowsClose d
                                                false
                                            else
                                                d < input.Count
                                                && (match input.KindOf d with
                                                    | TokenKind.LessThanToken
                                                    | TokenKind.OpenBracketToken
                                                    | TokenKind.QuestionToken
                                                    | TokenKind.AsteriskToken
                                                    | TokenKind.ColonColonToken -> true
                                                    | _ -> false)
                                        | TokenKind.AsteriskToken ->
                                            start + 2 < input.Count
                                            && (match input.KindOf(start + 2) with
                                                | TokenKind.OpenParenToken
                                                | TokenKind.AsteriskToken
                                                | TokenKind.QuestionToken
                                                | TokenKind.OpenBracketToken -> true
                                                | _ -> false)
                                        | TokenKind.QuestionToken ->
                                            start + 2 < input.Count
                                            && (match input.KindOf(start + 2) with
                                                | TokenKind.OpenParenToken
                                                | TokenKind.OpenBracketToken -> true
                                                | _ -> false)
                                        | TokenKind.LessThanToken
                                        | TokenKind.OpenBracketToken
                                        | TokenKind.ColonColonToken -> true
                                        | _ -> false
                                | TokenKind.OpenParenToken ->
                                    this.MayOpenTupleReturnType start
                                    && this.TupleTypeEnd(start, TokenKind.OpenParenToken) >= 0
                                | TokenKind.RefKeyword
                                | TokenKind.DelegateKeyword -> true
                                | kind ->
                                    ExpressionSyntax.predefined kind
                                    && (start + 1 >= input.Count
                                        || (match input.KindOf(start + 1) with
                                            | TokenKind.OpenParenToken
                                            | TokenKind.QuestionToken
                                            | TokenKind.AsteriskToken
                                            | TokenKind.OpenBracketToken -> true
                                            | _ -> false))

                        if canStartReturnType then
                            ParseStats.event ParseStats.nLambdaHeadScans

                            let struct (isType, afterType, offset, _) =
                                ExpressionSyntax.scan input start false

                            cursor <- afterType
                            parameters <- afterType

                            valid <-
                                isType
                                && offset = 0
                                && this.SkipBalanced(&cursor, TokenKind.OpenParenToken)
                                && cursor < input.Count
                                && input.KindOf cursor = TokenKind.EqualsGreaterThanToken

                        let definite =
                            start > position
                            || (start < input.Count
                                && (input.KindOf start = TokenKind.RefKeyword
                                    || input.KindOf start = TokenKind.DelegateKeyword
                                    || ExpressionSyntax.predefined (input.KindOf start)))

                        if
                            valid
                            && not definite
                            && input.KindOf(parameters - 1) = TokenKind.QuestionToken
                        then
                            let lambdaStart = parameters
                            let state = this.BeginProbe()

                            valid <-
                                try
                                    this.Lambda(lambdaStart) |> ignore
                                    not (this.At TokenKind.ColonToken)
                                finally
                                    this.EndProbe state

                if valid then parameters else -1

    member private this.LambdaParameter() : int =
        let start, items = this.Start, children ()
        this.Attributes items
        let mutable more = true

        while more do
            match this.Kind with
            | TokenKind.RefKeyword
            | TokenKind.OutKeyword
            | TokenKind.InKeyword
            | TokenKind.ParamsKeyword
            | TokenKind.ReadOnlyKeyword -> this.Take items
            | _ when this.Word(0, "scoped") -> this.Take(items, TokenKind.ScopedKeyword)
            | _ -> more <- false

        if
            not (
                this.At TokenKind.IdentifierToken
                && (this.Next = TokenKind.CommaToken
                    || this.Next = TokenKind.CloseParenToken
                    || this.Next = TokenKind.EqualsToken
                    || this.Next = TokenKind.EqualsGreaterThanToken)
            )
        then
            items.Add(this.Type())

        this.Expect(items, TokenKind.IdentifierToken)

        if this.At TokenKind.EqualsToken then
            items.Add(this.Initializer())

        this.Make(NodeKind.Parameter, start, items)

    member private this.LambdaParameters() : int =
        let start, items = this.Start, children ()
        this.Expect(items, TokenKind.OpenParenToken)
        let mutable more = not (this.At TokenKind.CloseParenToken)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before = position
            items.Add(this.LambdaParameter())

            if this.At TokenKind.CommaToken then
                this.Take items
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, TokenKind.CloseParenToken)
        this.Make(NodeKind.ParameterList, start, items)

    member private this.ExpressionBlock() : int = this.Block()

    member private this.Lambda(parameters: int) : int =
        let previousForce = forceConditionalAccess
        forceConditionalAccess <- false
        let previousAsync = asyncContext
        let start, items = this.Start, children ()
        this.Attributes items

        let mutable sawStatic = false
        let mutable sawAsync = false

        while position < parameters
              && (this.At TokenKind.StaticKeyword || this.Word(0, "async")) do
            if this.Word(0, "async") then
                if sawAsync then
                    tree.Recover()

                sawAsync <- true
                asyncContext <- true
                this.Take(items, TokenKind.AsyncKeyword)
            else
                if sawStatic then
                    tree.Recover()

                sawStatic <- true
                this.Take items

        if position < parameters then
            items.Add(this.Type())

        let parenthesized = this.At TokenKind.OpenParenToken

        items.Add(
            if parenthesized then
                this.LambdaParameters()
            else
                this.LambdaParameter()
        )

        this.Expect(items, TokenKind.EqualsGreaterThanToken)

        items.Add(
            if this.At TokenKind.OpenBraceToken then
                this.ExpressionBlock()
            else
                this.Expression()
        )

        asyncContext <- previousAsync
        forceConditionalAccess <- previousForce

        this.Make(
            (if parenthesized then
                 NodeKind.ParenthesizedLambdaExpression
             else
                 NodeKind.SimpleLambdaExpression),
            start,
            items
        )

    member private this.Expression() : int = this.Expression(1)

    member private this.Expression(minimum: int) : int = this.Expression(minimum, true)

    member private this.MemoExpression
        (minimum: int, lambdaAllowed: bool, postfixExpression: int)
        : int =
        let inline run () =
            if postfixExpression >= 0 then
                this.ParsePostfix(postfixExpression)
            else
                this.ParseExpression(minimum, lambdaAllowed)

        if not speculative then
            run ()
        else
            let key =
                struct (input[position].Start,
                        minimum,
                        lambdaAllowed,
                        forceConditionalAccess,
                        asyncContext,
                        fieldContext,
                        queryContext)

            match expressionEnds.TryGetValue key with
            | true, struct (finish, hint, kind, collections) ->
                ParseStats.event ParseStats.nExpressionMemoHits
                this.MoveTo(this.CursorAt(finish, hint))
                let node = this.Make(kind, this.Start, children ())
                tree.CollectionConditionals[node] <- collections
                node
            | _ ->
                ParseStats.event ParseStats.nExpressionMemoMisses
                let node = run ()

                expressionEnds[key] <-
                    struct (input[position].Start,
                            position,
                            (tree.Node node).Kind,
                            tree.CollectionConditionals[node])

                node

    member private this.Expression(minimum: int, lambdaAllowed: bool) : int =
        if speculative then
            this.MemoExpression(minimum, lambdaAllowed, -1)
        else
            this.ParseExpression(minimum, lambdaAllowed)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.PlainName() =
        current = TokenKind.IdentifierToken
        && next <> TokenKind.LessThanToken
        && next <> TokenKind.ColonColonToken
        && (let token = &this.CurrentRef()
            let length = token.Length

            length < 3 || length > 5 || not (this.ContextualAtCursor token.Start))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.SimpleOperand() : NodeKind =
        let token = &this.CurrentRef()

        match token.Kind with
        | TokenKind.NumericLiteralToken -> NodeKind.NumericLiteralExpression
        | TokenKind.StringLiteralToken
        | TokenKind.SingleLineRawStringLiteralToken
        | TokenKind.MultiLineRawStringLiteralToken -> NodeKind.StringLiteralExpression
        | TokenKind.CharacterLiteralToken -> NodeKind.CharacterLiteralExpression
        | TokenKind.TrueKeyword -> NodeKind.TrueLiteralExpression
        | TokenKind.FalseKeyword -> NodeKind.FalseLiteralExpression
        | TokenKind.NullKeyword -> NodeKind.NullLiteralExpression
        | TokenKind.ThisKeyword -> NodeKind.ThisExpression
        | TokenKind.IdentifierToken ->
            match this.Next with
            | TokenKind.EqualsGreaterThanToken
            | TokenKind.OpenParenToken
            | TokenKind.DotToken
            | TokenKind.LessThanToken
            | TokenKind.OpenBracketToken
            | TokenKind.QuestionToken
            | TokenKind.AsteriskToken
            | TokenKind.ColonColonToken -> NodeKind.None
            | _ ->
                let length = token.Length

                if length < 3 || length > 5 || not (this.ContextualAtCursor token.Start) then
                    NodeKind.IdentifierName
                else
                    NodeKind.None
        | _ -> NodeKind.None

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.ContinuesExpression() =
        let kind = this.Kind
        let struct (precedence, _) = ExpressionSyntax.binary kind

        precedence > 0
        || kind = TokenKind.IdentifierToken
        || kind = TokenKind.SwitchKeyword
        || kind = TokenKind.QuestionToken

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.MayContinuePostfix() =
        match this.Kind with
        | TokenKind.DotToken
        | TokenKind.MinusGreaterThanToken
        | TokenKind.OpenParenToken
        | TokenKind.OpenBracketToken
        | TokenKind.PlusPlusToken
        | TokenKind.MinusMinusToken
        | TokenKind.ExclamationToken
        | TokenKind.QuestionToken -> true
        | _ -> false

    member private this.ParseExpression(minimum: int, lambdaAllowed: bool) : int =
        ensureStack ()
        let simple = this.SimpleOperand()

        if simple <> NodeKind.None then
            let leaf = this.Single simple

            let operand =
                if speculative || this.MayContinuePostfix() then
                    this.Postfix leaf
                else
                    leaf

            if this.ContinuesExpression() then
                this.ExpressionRest(operand, minimum)
            else
                operand
        else

            let lambda =
                if minimum <= 1 && lambdaAllowed then
                    this.LambdaCursor()
                else
                    -1

            let result =
                if lambda >= 0 then
                    this.Lambda(lambda)
                elif this.PlainName() then
                    this.Postfix(this.Single NodeKind.IdentifierName)
                else
                    this.UnaryExpression()

            if this.ContinuesExpression() then
                this.ExpressionRest(result, minimum)
            else
                result

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.AsOrIsExpression
        (start: int, result: int, currentKind: TokenKind, kind: NodeKind)
        : int =
        let items = children ()
        items.Add result
        this.Take items

        let struct (isType, cursor, offset, _) =
            if currentKind = TokenKind.AsKeyword then
                this.ScanType(position, ExpressionSyntax.AsExpression)
            else
                this.PatternTypeScan(ExpressionSyntax.AfterIs)

        let follower = input[min cursor (input.Count - 1)].Kind
        let struct (followerPrecedence, _) = ExpressionSyntax.binary follower

        if
            currentKind = TokenKind.AsKeyword
            || (isType
                && offset = 0
                && not (this.Word(0, "not"))
                && (not (this.At TokenKind.OpenParenToken) || this.TupleArrayType(cursor))
                && follower <> TokenKind.OpenParenToken
                && follower <> TokenKind.OpenBraceToken
                && follower <> TokenKind.DotToken
                && followerPrecedence <= 10
                && not (ExpressionSyntax.literalStart follower)
                && input[max position (cursor - 1)].Kind <> TokenKind.AsteriskToken
                && (follower <> TokenKind.IdentifierToken || this.QueryKeyword(cursor - position)))
        then
            items.Add(
                this.Type(
                    (currentKind = TokenKind.IsKeyword),
                    cursor,
                    if currentKind = TokenKind.AsKeyword then
                        ExpressionSyntax.AsExpression
                    else
                        ExpressionSyntax.AfterIs
                )
            )

            this.Make(kind, start, items)
        else
            let previousWhen = whenKeyword
            whenKeyword <- false

            try
                items.Add(this.Pattern(1, false, 11, ExpressionSyntax.AfterIs))
            finally
                whenKeyword <- previousWhen

            this.Make(NodeKind.IsPatternExpression, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ConditionalExpression(start: int, condition: int) : int =
        let items = children ()
        items.Add condition
        let collection = this.Peek(1) = TokenKind.OpenBracketToken
        this.Take items
        let armPosition, armOffset = position, input[position].Start
        let mark = tree.Checkpoint()
        let mutable whenTrue = this.Expression()

        if
            not (this.At TokenKind.ColonToken)
            && not forceConditionalAccess
            && tree.CollectionConditionals[whenTrue]
        then
            let state = this.BeginProbe()

            let recovered =
                try
                    this.MoveTo(this.CursorAt(armOffset, armPosition))
                    forceConditionalAccess <- true
                    this.Expression() |> ignore
                    this.At TokenKind.ColonToken
                finally
                    this.EndProbe state

            if recovered then
                tree.Restore mark
                this.MoveTo(this.CursorAt(armOffset, armPosition))
                forceConditionalAccess <- true
                whenTrue <- this.Expression()
                forceConditionalAccess <- false

        items.Add whenTrue
        this.Expect(items, TokenKind.ColonToken)
        items.Add(this.Expression())
        let result = this.Make(NodeKind.ConditionalExpression, start, items)

        tree.CollectionConditionals[result] <- tree.CollectionConditionals[result] || collection

        result

    member private this.ExpressionRest(expression: int, minimum: int) : int =
        let start = (tree.Node expression).TokenStart
        let mutable result = expression
        let mutable more = true

        while more do
            let currentKind = this.Kind
            let struct (precedence, kind) = ExpressionSyntax.binary currentKind

            if precedence > 0 then
                if precedence >= minimum then
                    if currentKind = TokenKind.AsKeyword || currentKind = TokenKind.IsKeyword then
                        result <- this.AsOrIsExpression(start, result, currentKind, kind)
                    else
                        let operatorToken = this.TakeChild()

                        if
                            kind <> NodeKind.RangeExpression
                            || ExpressionSyntax.expressionStart this.Kind
                        then
                            let right =
                                this.Expression(
                                    if precedence = 1 || precedence = 3 then
                                        precedence
                                    else
                                        precedence + 1
                                )

                            result <- tree.AddNode3(kind, start, result, operatorToken, right)
                        else
                            result <- tree.AddNode2(kind, start, result, operatorToken)
                else
                    more <- false
            elif currentKind = TokenKind.QuestionToken && minimum <= 2 then
                result <- this.ConditionalExpression(start, result)
            elif
                currentKind = TokenKind.IdentifierToken
                && minimum <= 14
                && input[position].Length = 4
                && this.Word(0, "with")
                && this.Peek(1) = TokenKind.OpenBraceToken
            then
                let items = children ()
                items.Add result
                this.Take(items, TokenKind.WithKeyword)
                items.Add(this.ExpressionInitializer(NodeKind.WithInitializerExpression))
                result <- this.Make(NodeKind.WithExpression, start, items)
            elif currentKind = TokenKind.SwitchKeyword && minimum <= 14 then
                result <- this.SwitchExpression(result)
            else
                more <- false

        result

    member private this.IsAwait() =
        let next = this.Next

        this.Word(0, "await")
        && (asyncContext
            || (ExpressionSyntax.expressionStart next
                && ExpressionSyntax.unary next = NodeKind.None
                && next <> TokenKind.OpenParenToken
                && next <> TokenKind.OpenBracketToken
                && next <> TokenKind.DotDotToken))

    member private this.UnaryExpression() : int =
        ensureStack ()
        let start = this.Start
        let currentKind = this.Kind
        let unary = ExpressionSyntax.unary currentKind

        if
            unary <> NodeKind.None
            || currentKind = TokenKind.ThrowKeyword
            || currentKind = TokenKind.RefKeyword
            || (currentKind = TokenKind.IdentifierToken
                && input[position].Length = 5
                && this.IsAwait())
        then
            let items = children ()

            let kind =
                if unary <> NodeKind.None then
                    unary
                elif currentKind = TokenKind.ThrowKeyword then
                    NodeKind.ThrowExpression
                elif currentKind = TokenKind.RefKeyword then
                    NodeKind.RefExpression
                else
                    NodeKind.AwaitExpression

            if kind = NodeKind.AwaitExpression then
                this.Take(items, TokenKind.AwaitKeyword)
            else
                this.Take items

            items.Add(
                if kind = NodeKind.ThrowExpression || kind = NodeKind.RefExpression then
                    this.Expression()
                else
                    this.UnaryExpression()
            )

            this.Make(kind, start, items)
        elif currentKind = TokenKind.DotDotToken then
            let items = children ()
            this.Take items

            if ExpressionSyntax.expressionStart this.Kind then
                items.Add(this.Expression(15))

            this.Make(NodeKind.RangeExpression, start, items)
        elif currentKind = TokenKind.OpenParenToken && this.IsCast() then
            let items = children ()
            this.Take items
            items.Add(this.Type())
            this.Expect(items, TokenKind.CloseParenToken)
            items.Add(this.UnaryExpression())
            this.Make(NodeKind.CastExpression, start, items)
        else
            this.Postfix(this.Primary())

    member private this.IsCast() =
        let start = position + 1

        let struct (valid, cursor, offset, definite) =
            if
                start < input.Count
                && input[start].Kind = TokenKind.OpenParenToken
                && this.TupleTypeEnd(start, TokenKind.CloseParenToken) < 0
            then
                struct (false, start, 0, false)
            else
                ExpressionSyntax.scan input start false

        if
            not valid
            || offset <> 0
            || cursor >= input.Count
            || input[cursor].Kind <> TokenKind.CloseParenToken
        then
            false
        else
            let next = input[min (cursor + 1) (input.Count - 1)].Kind

            not (this.QueryKeyword(cursor + 1 - position))
            && (definite
                || (ExpressionSyntax.expressionStart next
                    && next <> TokenKind.PlusToken
                    && next <> TokenKind.MinusToken
                    && next <> TokenKind.PlusPlusToken
                    && next <> TokenKind.MinusMinusToken
                    && next <> TokenKind.AmpersandToken
                    && next <> TokenKind.AsteriskToken
                    && (next <> TokenKind.OpenBracketToken
                        || this.ContainsKind(position + 1, cursor, TokenKind.LessThanToken))
                    && next <> TokenKind.DotDotToken
                    && next <> TokenKind.CaretToken))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrimaryCold(start: int, kind: TokenKind) : int =
        match kind with
        | TokenKind.Utf8StringLiteralToken
        | TokenKind.Utf8SingleLineRawStringLiteralToken
        | TokenKind.Utf8MultiLineRawStringLiteralToken ->
            this.Single NodeKind.Utf8StringLiteralExpression
        | TokenKind.DefaultKeyword when this.Peek(1) <> TokenKind.OpenParenToken ->
            this.Single NodeKind.DefaultLiteralExpression
        | TokenKind.InterpolatedStringToken
        | TokenKind.InterpolatedStringStartToken
        | TokenKind.InterpolatedVerbatimStringStartToken
        | TokenKind.InterpolatedSingleLineRawStringStartToken
        | TokenKind.InterpolatedMultiLineRawStringStartToken -> this.InterpolatedString()
        | TokenKind.TypeOfKeyword
        | TokenKind.SizeOfKeyword
        | TokenKind.DefaultKeyword ->
            let nodeKind =
                if this.At TokenKind.TypeOfKeyword then
                    NodeKind.TypeOfExpression
                elif this.At TokenKind.SizeOfKeyword then
                    NodeKind.SizeOfExpression
                else
                    NodeKind.DefaultExpression

            let items = children ()
            this.Take items
            this.Expect(items, TokenKind.OpenParenToken)
            items.Add(this.Type())
            this.Expect(items, TokenKind.CloseParenToken)
            this.Make(nodeKind, start, items)
        | TokenKind.CheckedKeyword
        | TokenKind.UncheckedKeyword ->
            let nodeKind =
                if this.At TokenKind.CheckedKeyword then
                    NodeKind.CheckedExpression
                else
                    NodeKind.UncheckedExpression

            let items = children ()
            this.Take items
            this.Expect(items, TokenKind.OpenParenToken)
            items.Add(this.Expression())
            this.Expect(items, TokenKind.CloseParenToken)
            this.Make(nodeKind, start, items)
        | TokenKind.UnsafeKeyword when this.Peek(1) = TokenKind.OpenParenToken ->
            let items = children ()
            this.Take items
            this.Take items
            items.Add(this.Expression())
            this.Expect(items, TokenKind.CloseParenToken)
            this.Make(NodeKind.UnsafeExpression, start, items)
        | TokenKind.ArgListKeyword -> this.Single NodeKind.ArgListExpression
        | TokenKind.MakeRefKeyword
        | TokenKind.RefTypeKeyword
        | TokenKind.RefValueKeyword ->
            let nodeKind =
                match kind with
                | TokenKind.MakeRefKeyword -> NodeKind.MakeRefExpression
                | TokenKind.RefTypeKeyword -> NodeKind.RefTypeExpression
                | _ -> NodeKind.RefValueExpression

            let items = children ()
            this.Take items
            this.Expect(items, TokenKind.OpenParenToken)
            items.Add(this.Expression())

            if nodeKind = NodeKind.RefValueExpression then
                this.Expect(items, TokenKind.CommaToken)
                items.Add(this.Type())

            this.Expect(items, TokenKind.CloseParenToken)
            this.Make(nodeKind, start, items)
        | TokenKind.OpenBracketToken -> this.Collection()
        | TokenKind.OpenBraceToken -> this.ExpressionInitializer(NodeKind.None)
        | TokenKind.DelegateKeyword -> this.AnonymousMethod()
        | TokenKind.StaticKeyword ->
            if this.AnonymousMethodModifiers() > 0 then
                this.AnonymousMethod()
            else
                let items = children ()
                this.Expect(items, TokenKind.IdentifierToken)
                this.Make(NodeKind.IdentifierName, start, items)
        | TokenKind.IdentifierToken ->
            if this.AnonymousMethodModifiers() > 0 then
                this.AnonymousMethod()
            elif this.IsQuery() then
                this.Query()
            elif fieldContext && this.Word(0, "field") then
                let items = children ()
                this.Take(items, TokenKind.FieldKeyword)
                this.Make(NodeKind.FieldExpression, start, items)
            elif this.IsDeconstruction() then
                this.DeclarationExpression()
            elif this.Peek(1) = TokenKind.ColonColonToken then
                this.AliasExpression()
            else
                this.ExpressionName()
        | _ ->
            let items = children ()
            this.Expect(items, TokenKind.IdentifierToken)
            this.Make(NodeKind.IdentifierName, start, items)

    member private this.Primary() : int =
        let start = this.Start
        let kind = this.Kind

        match kind with
        | TokenKind.IdentifierToken ->
            let tok = input[position]
            let firstChar = if tok.Length > 0 then source[tok.Start] else '\000'

            if
                (tok.Length = 4 && firstChar = 'f')
                || (tok.Length = 3 && firstChar = 'v')
                || (tok.Length = 5 && (firstChar = 'a' || firstChar = 'f'))
                || this.Peek(1) = TokenKind.ColonColonToken
            then
                this.PrimaryCold(start, kind)
            else
                this.ExpressionName()
        | TokenKind.NumericLiteralToken -> this.Single NodeKind.NumericLiteralExpression
        | TokenKind.StringLiteralToken
        | TokenKind.SingleLineRawStringLiteralToken
        | TokenKind.MultiLineRawStringLiteralToken -> this.Single NodeKind.StringLiteralExpression
        | TokenKind.CharacterLiteralToken -> this.Single NodeKind.CharacterLiteralExpression
        | TokenKind.TrueKeyword -> this.Single NodeKind.TrueLiteralExpression
        | TokenKind.FalseKeyword -> this.Single NodeKind.FalseLiteralExpression
        | TokenKind.NullKeyword -> this.Single NodeKind.NullLiteralExpression
        | TokenKind.ThisKeyword -> this.Single NodeKind.ThisExpression
        | TokenKind.BaseKeyword -> this.Single NodeKind.BaseExpression
        | TokenKind.OpenParenToken -> this.ParenthesizedOrTuple()
        | TokenKind.NewKeyword
        | TokenKind.StackAllocKeyword -> this.Creation()
        | _ when ExpressionSyntax.predefined kind -> this.Single NodeKind.PredefinedType
        | _ -> this.PrimaryCold(start, kind)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ConditionalElementAccess() =
        forceConditionalAccess
        || (let state = this.BeginProbe()

            try
                let bracketPosition, bracketOffset = position + 1, input[position + 1].Start
                this.MoveTo(bracketPosition)
                this.Expression() |> ignore

                if not (this.At TokenKind.ColonToken) then
                    true
                else
                    let colonOffset = input[position].Start
                    this.MoveTo(this.CursorAt(bracketOffset, bracketPosition))
                    let arguments = tree.Node(this.BracketedArguments())
                    let close = tree.Token(arguments.TokenStart + arguments.TokenCount - 1)
                    not (close.Length > 0 && input[position].Start <= colonOffset)
            finally
                this.EndProbe state)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.Postfix(expression: int) : int =
        if speculative then
            this.MemoExpression(
                -(int (tree.Node expression).Kind),
                tree.CollectionConditionals[expression],
                expression
            )
        else
            this.ParsePostfix(expression)

    member private this.ParsePostfix(expression: int) : int =
        ensureStack ()
        let start = (tree.Node expression).TokenStart
        let mutable result = expression
        let mutable more = true

        while more do
            let operator =
                match this.Kind with
                | TokenKind.DotToken
                | TokenKind.MinusGreaterThanToken
                | TokenKind.OpenParenToken
                | TokenKind.OpenBracketToken
                | TokenKind.PlusPlusToken
                | TokenKind.MinusMinusToken
                | TokenKind.ExclamationToken -> true
                | TokenKind.QuestionToken ->
                    this.Next = TokenKind.DotToken
                    || (this.Next = TokenKind.OpenBracketToken && this.ConditionalElementAccess())
                | _ -> false

            if not operator then
                more <- false
            elif this.At TokenKind.DotToken || this.At TokenKind.MinusGreaterThanToken then
                let kind =
                    if this.At TokenKind.DotToken then
                        NodeKind.SimpleMemberAccessExpression
                    else
                        NodeKind.PointerMemberAccessExpression

                let operatorToken = this.TakeChild()

                let name =
                    if
                        current = TokenKind.IdentifierToken
                        && next <> TokenKind.LessThanToken
                        && next <> TokenKind.ColonColonToken
                    then
                        this.Single NodeKind.IdentifierName
                    else
                        this.ExpressionName()

                result <- tree.AddNode3(kind, start, result, operatorToken, name)
            elif this.At TokenKind.OpenParenToken then
                let arguments = this.Arguments(false)
                result <- tree.AddNode2(NodeKind.InvocationExpression, start, result, arguments)
            else

                let items = children ()
                items.Add result

                if this.At TokenKind.OpenBracketToken then
                    items.Add(this.BracketedArguments())
                    result <- this.Make(NodeKind.ElementAccessExpression, start, items)
                elif this.At TokenKind.QuestionToken then
                    this.Take items
                    let bindStart, binding = this.Start, children ()
                    let dot = this.At TokenKind.DotToken

                    if dot then
                        this.Take binding
                        binding.Add(this.ExpressionName())
                    else
                        binding.Add(this.BracketedArguments())

                    let node =
                        this.Make(
                            (if dot then
                                 NodeKind.MemberBindingExpression
                             else
                                 NodeKind.ElementBindingExpression),
                            bindStart,
                            binding
                        )

                    let whenNotNull = this.Postfix(node)
                    let struct (precedence, _) = ExpressionSyntax.binary this.Kind

                    items.Add(
                        if precedence = 1 then
                            this.ExpressionRest(whenNotNull, 1)
                        else
                            whenNotNull
                    )

                    result <- this.Make(NodeKind.ConditionalAccessExpression, start, items)
                else
                    let kind =
                        if this.At TokenKind.PlusPlusToken then
                            NodeKind.PostIncrementExpression
                        elif this.At TokenKind.MinusMinusToken then
                            NodeKind.PostDecrementExpression
                        else
                            NodeKind.SuppressNullableWarningExpression

                    this.Take items
                    result <- this.Make(kind, start, items)

        result

    member private this.IsDeclarationType(tuple: bool, requireComma: bool) =
        let typeStart =
            if this.IsScopedType(position) then
                position + 1
            else
                position

        if
            typeStart < input.Count
            && input[typeStart].Kind = TokenKind.OpenParenToken
            && (let afterTuple = this.TupleTypeEnd(typeStart, TokenKind.IdentifierToken) in

                afterTuple < 0
                || (requireComma
                    && (afterTuple + 1 >= input.Count
                        || input[afterTuple + 1].Kind <> TokenKind.CommaToken)))
        then
            false
        else
            let struct (isType, cursor, offset, _) = ExpressionSyntax.scan input typeStart false

            isType
            && offset = 0
            && cursor < input.Count
            && input[cursor].Kind = TokenKind.IdentifierToken
            && (if requireComma then
                    cursor + 1 < input.Count && input[cursor + 1].Kind = TokenKind.CommaToken
                elif tuple then
                    cursor + 1 < input.Count
                    && (input[cursor + 1].Kind = TokenKind.CommaToken
                        || input[cursor + 1].Kind = TokenKind.CloseParenToken)
                else
                    true)

    member private this.Argument(attributes: bool) : int = this.Argument(attributes, false)

    member private this.Argument(attributes: bool, tuple: bool) : int =
        if
            attributes
            && not (
                current = TokenKind.IdentifierToken
                && (next = TokenKind.ColonToken || next = TokenKind.EqualsToken)
            )
        then
            let start = this.Start
            tree.AddNode1(NodeKind.AttributeArgument, start, this.Expression())
        elif
            not attributes
            && not tuple
            && current <> TokenKind.RefKeyword
            && current <> TokenKind.OutKeyword
            && current <> TokenKind.InKeyword
            && not (current = TokenKind.IdentifierToken && next = TokenKind.ColonToken)
        then
            let start = this.Start
            tree.AddNode1(NodeKind.Argument, start, this.Expression())
        else

            let start, items = this.Start, children ()

            if
                this.At TokenKind.IdentifierToken
                && (this.Next = TokenKind.ColonToken
                    || (attributes && this.Next = TokenKind.EqualsToken))
            then
                let nameStart = this.Start
                let identifier = this.Single NodeKind.IdentifierName

                let kind =
                    if this.At TokenKind.EqualsToken then
                        NodeKind.NameEquals
                    else
                        NodeKind.NameColon

                items.Add(tree.AddNode2(kind, nameStart, identifier, this.TakeChild()))

            let declarationAllowed = not attributes && (tuple || this.At TokenKind.OutKeyword)

            if
                not attributes
                && (this.At TokenKind.RefKeyword
                    || this.At TokenKind.OutKeyword
                    || this.At TokenKind.InKeyword)
            then
                this.Take items

            let canDeclare =
                declarationAllowed && not (tuple && asyncContext && this.Word(0, "await"))

            let isDeclaration =
                canDeclare
                && (this.IsDeconstruction(tuple) || this.IsDeclarationType(tuple, false))

            if isDeclaration then
                items.Add(this.DeclarationExpression())
            else
                items.Add(this.Expression())

            this.Make(
                (if attributes then
                     NodeKind.AttributeArgument
                 else
                     NodeKind.Argument),
                start,
                items
            )

    member private this.ArgumentList(attributes: bool, bracketed: bool) : int =
        let start, items = this.Start, children ()

        let close =
            if bracketed then
                TokenKind.CloseBracketToken
            else
                TokenKind.CloseParenToken

        this.Expect(
            items,
            if bracketed then
                TokenKind.OpenBracketToken
            else
                TokenKind.OpenParenToken
        )

        let mutable more = not (this.At close)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before = position

            let simple =
                if attributes || bracketed || speculative then
                    NodeKind.None
                else
                    match next with
                    | TokenKind.CommaToken
                    | TokenKind.CloseParenToken -> this.SimpleOperand()
                    | _ -> NodeKind.None

            if simple <> NodeKind.None then
                let start = this.Start
                items.Add(tree.AddNode1(NodeKind.Argument, start, this.Single simple))
            else
                items.Add(this.Argument(attributes))

            this.SkipUntil(
                items,
                struct (TokenKind.CommaToken,
                        close,
                        TokenKind.SemicolonToken,
                        TokenKind.CloseBraceToken,
                        TokenKind.None)
            )

            if this.At TokenKind.CommaToken then
                this.Take items
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, close)

        this.Make(
            (if attributes then NodeKind.AttributeArgumentList
             elif bracketed then NodeKind.BracketedArgumentList
             else NodeKind.ArgumentList),
            start,
            items
        )

    member private this.Arguments(attributes: bool) : int = this.ArgumentList(attributes, false)
    member private this.BracketedArguments() : int = this.ArgumentList(false, true)

    member private this.ParenthesizedOrTuple() : int =
        let start, items = this.Start, children ()
        this.Take items
        let argStart = this.Start

        let nameColon =
            if this.At TokenKind.IdentifierToken && this.Next = TokenKind.ColonToken then
                let nameStart = this.Start
                let identifier = this.Single NodeKind.IdentifierName
                tree.AddNode2(NodeKind.NameColon, nameStart, identifier, this.TakeChild())
            else
                -1

        let deconstructionEnd = this.DeconstructionEnd()

        let first =
            if
                (deconstructionEnd >= 0 && input[deconstructionEnd].Kind = TokenKind.CommaToken)
                || (not (asyncContext && this.Word(0, "await"))
                    && this.IsDeclarationType(true, true))
            then
                this.DeclarationExpression()
            else
                this.Expression()

        let tuple = this.At TokenKind.CommaToken || nameColon >= 0

        if tuple then
            let arg = children ()

            if nameColon >= 0 then
                arg.Add nameColon

            arg.Add first
            items.Add(this.Make(NodeKind.Argument, argStart, arg))

            while this.At TokenKind.CommaToken do
                this.Take items
                items.Add(this.Argument(false, true))
        else
            items.Add first

        this.Expect(items, TokenKind.CloseParenToken)

        this.Make(
            (if tuple then
                 NodeKind.TupleExpression
             else
                 NodeKind.ParenthesizedExpression),
            start,
            items
        )

    member private this.Collection() : int =
        let start, items = this.Start, children ()
        this.Take items
        let mutable more = not (this.At TokenKind.CloseBracketToken)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before, elementStart, element = position, this.Start, children ()
            let spread = this.At TokenKind.DotDotToken

            if spread then
                this.Take element

            element.Add(this.Expression())

            items.Add(
                this.Make(
                    (if spread then
                         NodeKind.SpreadElement
                     else
                         NodeKind.ExpressionElement),
                    elementStart,
                    element
                )
            )

            if this.At TokenKind.CommaToken then
                this.Take items
                more <- not (this.At TokenKind.CloseBracketToken)
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, TokenKind.CloseBracketToken)
        this.Make(NodeKind.CollectionExpression, start, items)

    member private this.ExpressionInitializer(requestedKind: NodeKind) : int =
        ensureStack ()
        let start, items = this.Start, children ()
        this.Expect(items, TokenKind.OpenBraceToken)
        let mutable kind = requestedKind

        if kind = NodeKind.None then
            kind <-
                if
                    (this.At TokenKind.IdentifierToken && this.Next = TokenKind.EqualsToken)
                    || this.At TokenKind.OpenBracketToken
                    || this.At TokenKind.CloseBraceToken
                then
                    NodeKind.ObjectInitializerExpression
                else
                    NodeKind.CollectionInitializerExpression

        let mutable more = not (this.At TokenKind.CloseBraceToken)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before = position

            if this.At TokenKind.OpenBraceToken then
                items.Add(
                    this.ExpressionInitializer(
                        if kind = NodeKind.ArrayInitializerExpression then
                            kind
                        else
                            NodeKind.ComplexElementInitializerExpression
                    )
                )
            elif
                this.At TokenKind.OpenBracketToken
                && kind = NodeKind.ObjectInitializerExpression
            then
                let assignmentStart, element = this.Start, children ()
                element.Add(this.BracketedArguments())

                let implicitElement =
                    this.Make(NodeKind.ImplicitElementAccess, assignmentStart, element)

                let assignment = children ()
                assignment.Add implicitElement
                this.Expect(assignment, TokenKind.EqualsToken)
                assignment.Add(this.Expression())

                items.Add(
                    this.Make(NodeKind.SimpleAssignmentExpression, assignmentStart, assignment)
                )
            else
                items.Add(this.Expression())

            if this.At TokenKind.CommaToken then
                this.Take items
                more <- not (this.At TokenKind.CloseBraceToken)
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, TokenKind.CloseBraceToken)
        this.Make(kind, start, items)

    member private this.IsTupleCreation() =
        let struct (valid, cursor, offset, _) = ExpressionSyntax.scanTypeHead input position

        let after =
            if cursor < input.Count && input[cursor].Kind = TokenKind.QuestionToken then
                cursor + 1
            else
                cursor

        valid
        && offset = 0
        && after < input.Count
        && (input[after].Kind = TokenKind.OpenBracketToken
            || input[after].Kind = TokenKind.OpenParenToken)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.AnonymousObjectOrImplicitArrayCreation
        (start: int, items: ChildList, stack: bool)
        : int =
        if this.At TokenKind.OpenBraceToken && not stack then
            this.Take items
            let mutable more = not (this.At TokenKind.CloseBraceToken)

            while more && not (this.At TokenKind.EndOfFileToken) do
                let before, memberStart, memberItems = position, this.Start, children ()

                if this.At TokenKind.IdentifierToken && this.Next = TokenKind.EqualsToken then
                    let nameStart, name = this.Start, children ()
                    name.Add(this.Single NodeKind.IdentifierName)
                    this.Take name
                    memberItems.Add(this.Make(NodeKind.NameEquals, nameStart, name))

                memberItems.Add(this.Expression())

                items.Add(
                    this.Make(NodeKind.AnonymousObjectMemberDeclarator, memberStart, memberItems)
                )

                if this.At TokenKind.CommaToken then
                    this.Take items
                    more <- not (this.At TokenKind.CloseBraceToken)
                else
                    more <- false

                if position = before then
                    more <- false

            this.Expect(items, TokenKind.CloseBraceToken)
            this.Make(NodeKind.AnonymousObjectCreationExpression, start, items)
        else
            this.Take items

            while this.At TokenKind.CommaToken do
                this.Take items

            this.Expect(items, TokenKind.CloseBracketToken)
            items.Add(this.ExpressionInitializer(NodeKind.ArrayInitializerExpression))

            this.Make(
                (if stack then
                     NodeKind.ImplicitStackAllocArrayCreationExpression
                 else
                     NodeKind.ImplicitArrayCreationExpression),
                start,
                items
            )

    member private this.Creation() : int =
        let start, items = this.Start, children ()
        let stack = this.At TokenKind.StackAllocKeyword
        this.Take items

        if
            (this.At TokenKind.OpenBraceToken && not stack)
            || this.At TokenKind.OpenBracketToken
        then
            this.AnonymousObjectOrImplicitArrayCreation(start, items, stack)
        elif this.At TokenKind.OpenParenToken && not stack && not (this.IsTupleCreation()) then
            items.Add(this.Arguments(false))

            if this.At TokenKind.OpenBraceToken then
                items.Add(this.ExpressionInitializer(NodeKind.None))

            this.Make(NodeKind.ImplicitObjectCreationExpression, start, items)
        else
            let typeNode =
                this.Type(
                    true,
                    input.Count,
                    if stack then
                        ExpressionSyntax.Normal
                    else
                        ExpressionSyntax.NewExpression
                )

            items.Add typeNode
            let array = (tree.Node typeNode).Kind = NodeKind.ArrayType

            if not array && this.At TokenKind.OpenParenToken then
                items.Add(this.Arguments(false))

            if this.At TokenKind.OpenBraceToken then
                items.Add(
                    this.ExpressionInitializer(
                        if array then
                            NodeKind.ArrayInitializerExpression
                        else
                            NodeKind.None
                    )
                )

            this.Make(
                (if stack then NodeKind.StackAllocArrayCreationExpression
                 elif array then NodeKind.ArrayCreationExpression
                 else NodeKind.ObjectCreationExpression),
                start,
                items
            )

    member private this.AnonymousMethodModifiers() =
        let mutable distance = 0

        while this.Peek(distance) = TokenKind.StaticKeyword || this.Word(distance, "async") do
            distance <- distance + 1

        if this.Peek(distance) = TokenKind.DelegateKeyword then
            distance
        else
            0

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.AnonymousMethod() : int =
        let previousForce = forceConditionalAccess
        forceConditionalAccess <- false
        let previousAsync = asyncContext
        let start, items = this.Start, children ()

        let mutable sawStatic = false
        let mutable sawAsync = false

        for _ in 1 .. this.AnonymousMethodModifiers() do
            if this.At TokenKind.StaticKeyword then
                if sawStatic then
                    tree.Recover()

                sawStatic <- true
                this.Take items
            else
                if sawAsync then
                    tree.Recover()

                sawAsync <- true
                asyncContext <- true
                this.Take(items, TokenKind.AsyncKeyword)

        this.Expect(items, TokenKind.DelegateKeyword)

        if this.At TokenKind.OpenParenToken then
            items.Add(this.Parameters(false))

        items.Add(this.ExpressionBlock())
        asyncContext <- previousAsync
        forceConditionalAccess <- previousForce
        this.Make(NodeKind.AnonymousMethodExpression, start, items)

    member private this.PatternTypeScan(mode) = this.ScanType(position, mode)

    member private this.TupleArrayType(cursor: int) =
        this.At TokenKind.OpenParenToken
        && cursor > position
        && cursor <= input.Count
        && input[cursor - 1].Kind = TokenKind.CloseBracketToken

    member private this.PatternOperator() =
        this.Word(0, "and") || this.Word(0, "or")

    member private this.CombinatorDesignation(distance: int) =
        match this.Peek(distance + 1) with
        | TokenKind.CloseBraceToken
        | TokenKind.CloseBracketToken
        | TokenKind.CloseParenToken
        | TokenKind.CommaToken
        | TokenKind.SemicolonToken
        | TokenKind.QuestionToken
        | TokenKind.ColonToken -> true
        | TokenKind.LessThanEqualsToken
        | TokenKind.LessThanToken
        | TokenKind.GreaterThanEqualsToken
        | TokenKind.GreaterThanToken
        | TokenKind.IdentifierToken
        | TokenKind.OpenBraceToken
        | TokenKind.OpenParenToken
        | TokenKind.OpenBracketToken -> false
        | next ->
            let struct (precedence, _) = ExpressionSyntax.binary next
            precedence > 0 || not (ExpressionSyntax.expressionStart next)

    member private this.PatternDesignation() =
        this.At TokenKind.IdentifierToken
        && not (
            (this.PatternOperator() && not (this.CombinatorDesignation 0))
            || (whenKeyword && this.Word(0, "when"))
            || this.QueryKeyword(0)
        )

    member private this.IsPatternNode(index: int) =
        match (tree.Node index).Kind with
        | NodeKind.ConstantPattern
        | NodeKind.DeclarationPattern
        | NodeKind.RecursivePattern
        | NodeKind.ListPattern
        | NodeKind.SlicePattern
        | NodeKind.RelationalPattern
        | NodeKind.AndPattern
        | NodeKind.OrPattern
        | NodeKind.NotPattern
        | NodeKind.VarPattern
        | NodeKind.TypePattern
        | NodeKind.DiscardPattern
        | NodeKind.ParenthesizedPattern -> true
        | _ -> false

    member private this.Wrap(kind: NodeKind, child: int) : int =
        let node = tree.Node child
        let items = children ()
        items.Add child
        let index = this.Make(kind, node.TokenStart, items)

        tree.SetNode(
            index,
            { tree.Node index with
                TokenCount = node.TokenCount
            }
        )

        index

    member private this.Pattern() : int = this.Pattern(1, false)

    member private this.Pattern(minimum: int, plainConstant: bool) : int =
        this.Pattern(minimum, plainConstant, 2)

    member private this.Pattern(minimum: int, plainConstant: bool, expressionMinimum: int) : int =
        this.Pattern(minimum, plainConstant, expressionMinimum, ExpressionSyntax.DefinitePattern)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Pattern
        (minimum: int, plainConstant: bool, expressionMinimum: int, mode: ExpressionSyntax.TypeMode)
        : int =
        ensureStack ()
        let start = this.Start
        let mutable result = this.PatternAtom(plainConstant, expressionMinimum, mode)
        let mutable more = true

        while more do
            let precedence =
                if this.Word(0, "or") then 1
                elif this.Word(0, "and") then 2
                else 0

            if precedence >= minimum && precedence > 0 then
                let items = children ()
                items.Add result

                this.Take(
                    items,
                    if precedence = 1 then
                        TokenKind.OrKeyword
                    else
                        TokenKind.AndKeyword
                )

                items.Add(this.Pattern(precedence + 1, false, expressionMinimum, mode))

                result <-
                    this.Make(
                        (if precedence = 1 then
                             NodeKind.OrPattern
                         else
                             NodeKind.AndPattern),
                        start,
                        items
                    )
            else
                more <- false

        result

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Subpattern(property: bool) : int =
        let start, items = this.Start, children ()

        if this.At TokenKind.IdentifierToken && this.Next = TokenKind.ColonToken then
            let nameStart = this.Start
            let identifier = this.Single NodeKind.IdentifierName
            items.Add(tree.AddNode2(NodeKind.NameColon, nameStart, identifier, this.TakeChild()))
        elif property && this.At TokenKind.IdentifierToken && this.Next = TokenKind.DotToken then
            let nameStart, name = this.Start, children ()
            name.Add(this.Postfix(this.ExpressionName()))
            this.Expect(name, TokenKind.ColonToken)
            items.Add(this.Make(NodeKind.ExpressionColon, nameStart, name))

        items.Add(this.Pattern())
        this.Make(NodeKind.Subpattern, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PatternClause(property: bool) : int =
        let start, items = this.Start, children ()

        let close =
            if property then
                TokenKind.CloseBraceToken
            else
                TokenKind.CloseParenToken

        this.Take items
        let mutable more = not (this.At close)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before = position
            items.Add(this.Subpattern(property))

            if this.At TokenKind.CommaToken then
                this.Take items
                more <- not (this.At close)
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, close)

        this.Make(
            (if property then
                 NodeKind.PropertyPatternClause
             else
                 NodeKind.PositionalPatternClause),
            start,
            items
        )

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.RecursivePattern(start: int, items: ChildList) : int =
        if this.At TokenKind.OpenParenToken then
            items.Add(this.PatternClause(false))

        if this.At TokenKind.OpenBraceToken then
            items.Add(this.PatternClause(true))

        if this.PatternDesignation() then
            items.Add(this.Designation())

        this.Make(NodeKind.RecursivePattern, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ParenthesizedPattern(plainConstant: bool, expressionMinimum: int) : int =
        let start, items = this.Start, children ()
        this.Take items
        let named = this.At TokenKind.IdentifierToken && this.Next = TokenKind.ColonToken
        let empty = this.At TokenKind.CloseParenToken

        let first =
            if empty then -1
            elif named then this.Subpattern(false)
            else this.Pattern()

        if
            first >= 0
            && (tree.Node first).Kind = NodeKind.ConstantPattern
            && this.At TokenKind.QuestionToken
        then
            let inner = tree.Node first
            let expression = this.ExpressionRest(tree.Child inner.ChildStart, 2)
            let childStart = tree.AddChild expression

            tree.SetNode(
                expression,
                { tree.Node expression with
                    Parent = first
                }
            )

            tree.SetNode(
                first,
                { inner with
                    ChildStart = childStart
                    ChildCount = 1
                    TokenCount = tree.TokenCount - inner.TokenStart
                }
            )

        let positional = empty || named || this.At TokenKind.CommaToken

        if first >= 0 then
            items.Add(
                if positional && not named then
                    this.Wrap(NodeKind.Subpattern, first)
                else
                    first
            )

        while this.At TokenKind.CommaToken do
            this.Take items

            if not (this.At TokenKind.CloseParenToken) then
                items.Add(this.Subpattern(false))

        this.Expect(items, TokenKind.CloseParenToken)

        if positional || this.At TokenKind.OpenBraceToken || this.PatternDesignation() then
            if not positional && first >= 0 then
                items.Set(1, this.Wrap(NodeKind.Subpattern, first))

            let clause = this.Make(NodeKind.PositionalPatternClause, start, items)
            let recursive = children ()
            recursive.Add clause
            this.RecursivePattern(start, recursive)
        elif (tree.Node first).Kind = NodeKind.ConstantPattern then
            let inner = tree.Node first
            items.Set(1, tree.Child inner.ChildStart)
            let childStart = tree.ChildCount
            let childCount = items.Count
            tree.AppendChildren(items, first) |> ignore

            tree.SetNode(
                first,
                { inner with
                    Kind = NodeKind.ParenthesizedExpression
                    ChildStart = childStart
                    ChildCount = childCount
                    TokenStart = start
                    TokenCount = tree.TokenCount - start
                }
            )

            let expression = this.ExpressionRest(first, expressionMinimum)

            if plainConstant && not (this.PatternOperator()) then
                expression
            else
                this.Wrap(NodeKind.ConstantPattern, expression)
        else
            this.Make(NodeKind.ParenthesizedPattern, start, items)

    member private this.IsPatternCast() =
        this.IsCast()
        && (let struct (valid, cursor, offset, _) =
                ExpressionSyntax.scan input (position + 1) false

            valid
            && offset = 0
            && cursor + 1 < input.Count
            && ExpressionSyntax.expressionStart input[cursor + 1].Kind)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PatternAtom
        (plainConstant: bool, expressionMinimum: int, mode: ExpressionSyntax.TypeMode)
        : int =
        ensureStack ()
        let start = this.Start

        if this.Word(0, "not") then
            let items = children ()
            this.Take(items, TokenKind.NotKeyword)
            items.Add(this.PatternAtom(false, expressionMinimum, mode))
            this.Make(NodeKind.NotPattern, start, items)
        elif
            this.Word(0, "var")
            && (this.Next = TokenKind.IdentifierToken || this.Next = TokenKind.OpenParenToken)
        then
            let items = children ()
            this.Take(items, TokenKind.VarKeyword)
            items.Add(this.Designation())
            this.Make(NodeKind.VarPattern, start, items)
        elif this.Word(0, "_") && not plainConstant then
            let items = children ()
            this.Take(items, TokenKind.UnderscoreToken)
            this.Make(NodeKind.DiscardPattern, start, items)
        elif
            this.At TokenKind.LessThanToken
            || this.At TokenKind.LessThanEqualsToken
            || this.At TokenKind.GreaterThanToken
            || this.At TokenKind.GreaterThanEqualsToken
        then
            let items = children ()
            this.Take items
            items.Add(this.Expression(11))
            this.Make(NodeKind.RelationalPattern, start, items)
        elif this.At TokenKind.OpenBracketToken then
            let items = children ()
            this.Take items
            let mutable more = not (this.At TokenKind.CloseBracketToken)

            while more && not (this.At TokenKind.EndOfFileToken) do
                let before = position

                if this.At TokenKind.DotDotToken then
                    let sliceStart, slice = this.Start, children ()
                    this.Take slice

                    if
                        not (this.At TokenKind.CommaToken || this.At TokenKind.CloseBracketToken)
                    then
                        slice.Add(this.Pattern())

                    items.Add(this.Make(NodeKind.SlicePattern, sliceStart, slice))
                else
                    items.Add(this.Pattern())

                if this.At TokenKind.CommaToken then
                    this.Take items
                    more <- not (this.At TokenKind.CloseBracketToken)
                else
                    more <- false

                if position = before then
                    more <- false

            this.Expect(items, TokenKind.CloseBracketToken)

            if this.PatternDesignation() then
                items.Add(this.Designation())

            this.Make(NodeKind.ListPattern, start, items)
        elif this.At TokenKind.OpenBraceToken then
            this.RecursivePattern(start, children ())
        elif
            this.At TokenKind.OpenParenToken
            && not (this.IsPatternCast())
            && not (
                let struct (valid, cursor, offset, _) = this.PatternTypeScan(mode)
                valid && offset = 0 && this.TupleArrayType(cursor)
            )
        then
            this.ParenthesizedPattern(plainConstant, expressionMinimum)
        else
            let struct (valid, cursor, offset, definite) = this.PatternTypeScan(mode)
            let follower = this.Peek(cursor - position)

            let pointer =
                valid && cursor > position && input[cursor - 1].Kind = TokenKind.AsteriskToken

            let designation =
                valid
                && offset = 0
                && not pointer
                && cursor < input.Count
                && follower = TokenKind.IdentifierToken
                && not (
                    ((this.Word(cursor - position, "and") || this.Word(cursor - position, "or"))
                     && not (this.CombinatorDesignation(cursor - position)))
                    || (whenKeyword && this.Word(cursor - position, "when"))
                    || this.QueryKeyword(cursor - position)
                )

            let recursive =
                valid
                && offset = 0
                && (follower = TokenKind.OpenParenToken || follower = TokenKind.OpenBraceToken)

            let generic = valid && this.ContainsKind(position, cursor, TokenKind.LessThanToken)

            let struct (followerPrecedence, _) = ExpressionSyntax.binary follower

            let expressionFollower =
                valid
                && (follower = TokenKind.DotToken
                    || ExpressionSyntax.literalStart follower
                    || (followerPrecedence > 0 && followerPrecedence >= expressionMinimum)
                    || pointer)

            let nameof = this.Word(0, "nameof") && this.Next = TokenKind.OpenParenToken

            if nameof then
                let expression = this.Expression(expressionMinimum)

                if plainConstant && not (this.PatternOperator()) then
                    expression
                else
                    this.Wrap(NodeKind.ConstantPattern, expression)
            elif
                designation
                || recursive
                || (valid
                    && (definite || generic)
                    && not expressionFollower
                    && not (this.At TokenKind.OpenParenToken && this.IsPatternCast()))
            then
                let items = children ()
                items.Add(this.Type(true, cursor, mode))

                if recursive then
                    this.RecursivePattern(start, items)
                elif designation then
                    items.Add(this.Designation())
                    this.Make(NodeKind.DeclarationPattern, start, items)
                else
                    this.Make(NodeKind.TypePattern, start, items)
            else
                let expression = this.Expression(expressionMinimum)

                if plainConstant && not (this.PatternOperator()) then
                    expression
                else
                    this.Wrap(NodeKind.ConstantPattern, expression)

    member private this.QueryVariable(items: ChildList) =
        if this.Next <> TokenKind.InKeyword then
            items.Add(this.Type())

        this.Expect(items, TokenKind.IdentifierToken)
        this.Expect(items, TokenKind.InKeyword)
        items.Add(this.Expression())

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.FromClause() : int =
        let start, items = this.Start, children ()
        this.Take(items, TokenKind.FromKeyword)
        this.QueryVariable items
        this.Make(NodeKind.FromClause, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.QueryBody() : int =
        let start, items = this.Start, children ()
        let mutable more = true

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before = position

            if this.Word(0, "from") then
                items.Add(this.FromClause())
            elif this.Word(0, "let") then
                let clauseStart, clause = this.Start, children ()
                this.Take(clause, TokenKind.LetKeyword)
                this.Expect(clause, TokenKind.IdentifierToken)
                this.Expect(clause, TokenKind.EqualsToken)
                clause.Add(this.Expression())
                items.Add(this.Make(NodeKind.LetClause, clauseStart, clause))
            elif this.Word(0, "where") then
                let clauseStart, clause = this.Start, children ()
                this.Take(clause, TokenKind.WhereKeyword)
                clause.Add(this.Expression())
                items.Add(this.Make(NodeKind.WhereClause, clauseStart, clause))
            elif this.Word(0, "join") then
                let clauseStart, clause = this.Start, children ()
                this.Take(clause, TokenKind.JoinKeyword)
                this.QueryVariable clause
                this.ExpectWord(clause, "on", TokenKind.OnKeyword)
                clause.Add(this.Expression())
                this.ExpectWord(clause, "equals", TokenKind.EqualsKeyword)
                clause.Add(this.Expression())

                if this.Word(0, "into") then
                    let intoStart, into = this.Start, children ()
                    this.Take(into, TokenKind.IntoKeyword)
                    this.Expect(into, TokenKind.IdentifierToken)
                    clause.Add(this.Make(NodeKind.JoinIntoClause, intoStart, into))

                items.Add(this.Make(NodeKind.JoinClause, clauseStart, clause))
            elif this.Word(0, "orderby") then
                let clauseStart, clause = this.Start, children ()
                this.Take(clause, TokenKind.OrderByKeyword)
                let mutable ordering = true

                while ordering && not (this.At TokenKind.EndOfFileToken) do
                    let orderBefore, orderStart, order = position, this.Start, children ()
                    order.Add(this.Expression())
                    let descending = this.Word(0, "descending")

                    if descending || this.Word(0, "ascending") then
                        this.Take(
                            order,
                            if descending then
                                TokenKind.DescendingKeyword
                            else
                                TokenKind.AscendingKeyword
                        )

                    clause.Add(
                        this.Make(
                            (if descending then
                                 NodeKind.DescendingOrdering
                             else
                                 NodeKind.AscendingOrdering),
                            orderStart,
                            order
                        )
                    )

                    if this.At TokenKind.CommaToken then
                        this.Take clause
                    else
                        ordering <- false

                    if position = orderBefore then
                        ordering <- false

                items.Add(this.Make(NodeKind.OrderByClause, clauseStart, clause))
            else
                more <- false

            if position = before then
                more <- false

        let clauseStart, clause = this.Start, children ()
        let group = this.Word(0, "group")

        if group || this.Word(0, "select") then
            this.Take(
                clause,
                if group then
                    TokenKind.GroupKeyword
                else
                    TokenKind.SelectKeyword
            )
        else
            this.Expect(clause, TokenKind.SelectKeyword)

        clause.Add(this.Expression())

        if group then
            this.ExpectWord(clause, "by", TokenKind.ByKeyword)
            clause.Add(this.Expression())

        items.Add(
            this.Make(
                (if group then
                     NodeKind.GroupClause
                 else
                     NodeKind.SelectClause),
                clauseStart,
                clause
            )
        )

        if this.Word(0, "into") then
            let intoStart, into = this.Start, children ()
            this.Take(into, TokenKind.IntoKeyword)
            this.Expect(into, TokenKind.IdentifierToken)
            into.Add(this.QueryBody())
            items.Add(this.Make(NodeKind.QueryContinuation, intoStart, into))

        this.Make(NodeKind.QueryBody, start, items)

    member private this.IsQuery() =
        if not (this.Word(0, "from")) then
            false
        elif this.Next = TokenKind.IdentifierToken && this.Peek(2) = TokenKind.InKeyword then
            true
        else
            let struct (valid, after, offset, _) =
                ExpressionSyntax.scan input (position + 1) false

            valid
            && offset = 0
            && after + 1 < input.Count
            && input[after].Kind = TokenKind.IdentifierToken
            && input[after + 1].Kind = TokenKind.InKeyword

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Query() : int =
        let previousQuery = queryContext
        queryContext <- true

        try
            let start, items = this.Start, children ()
            items.Add(this.FromClause())
            items.Add(this.QueryBody())
            this.Make(NodeKind.QueryExpression, start, items)
        finally
            queryContext <- previousQuery

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.SwitchExpression(expression: int) : int =
        let start, items = (tree.Node expression).TokenStart, children ()
        items.Add expression
        this.Take items
        this.Expect(items, TokenKind.OpenBraceToken)
        let mutable more = not (this.At TokenKind.CloseBraceToken)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before, armStart, arm = position, this.Start, children ()
            let previousWhen = whenKeyword
            whenKeyword <- true

            try
                arm.Add(this.Pattern())
            finally
                whenKeyword <- previousWhen

            if this.Word(0, "when") then
                let whenStart, clause = this.Start, children ()
                this.Take(clause, TokenKind.WhenKeyword)
                clause.Add(this.Expression(1, false))
                arm.Add(this.Make(NodeKind.WhenClause, whenStart, clause))

            this.Expect(arm, TokenKind.EqualsGreaterThanToken)
            arm.Add(this.Expression())

            this.SkipUntil(
                arm,
                struct (TokenKind.CommaToken,
                        TokenKind.CloseBraceToken,
                        TokenKind.None,
                        TokenKind.None,
                        TokenKind.None)
            )

            items.Add(this.Make(NodeKind.SwitchExpressionArm, armStart, arm))

            if this.At TokenKind.CommaToken then
                this.Take items
                more <- not (this.At TokenKind.CloseBraceToken)
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, TokenKind.CloseBraceToken)
        this.Make(NodeKind.SwitchExpression, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Attribute(items: ChildList) =
        let start, list = this.Start, children ()
        this.Take list

        if this.Next = TokenKind.ColonToken then
            let targetStart, target = this.Start, children ()

            let promoted =
                if this.Word(0, "assembly") then TokenKind.AssemblyKeyword
                elif this.Word(0, "module") then TokenKind.ModuleKeyword
                elif this.Word(0, "type") then TokenKind.TypeKeyword
                elif this.Word(0, "field") then TokenKind.FieldKeyword
                elif this.Word(0, "method") then TokenKind.MethodKeyword
                elif this.Word(0, "param") then TokenKind.ParamKeyword
                elif this.Word(0, "property") then TokenKind.PropertyKeyword
                elif this.Word(0, "typevar") then TokenKind.TypeVarKeyword
                else TokenKind.None

            this.Take(target, promoted)
            this.Take target
            list.Add(this.Make(NodeKind.AttributeTargetSpecifier, targetStart, target))

        let mutable more = true

        while more
              && not (this.At TokenKind.EndOfFileToken)
              && not (this.At TokenKind.CloseBracketToken) do
            let before, attrStart, attr = position, this.Start, children ()
            attr.Add(this.Name())

            if this.At TokenKind.OpenParenToken then
                attr.Add(this.Arguments(true))

            list.Add(this.Make(NodeKind.Attribute, attrStart, attr))

            if this.At TokenKind.CommaToken then
                this.Take list
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(list, TokenKind.CloseBracketToken)
        items.Add(this.Make(NodeKind.AttributeList, start, list))

    member private this.Attributes(items: ChildList) =
        while this.At TokenKind.OpenBracketToken do
            this.Attribute items

    member private this.RefStructModifier() =
        let mutable distance = 1

        while this.Word(distance, "partial") do
            distance <- distance + 1

        this.Peek(distance) = TokenKind.StructKeyword

    member private this.AsyncModifier() =
        let struct (valid, after, offset, _) =
            ExpressionSyntax.scan input (position + 1) false

        (valid
         && offset = 0
         && after < input.Count
         && (input[after].Kind = TokenKind.IdentifierToken
             || input[after].Kind = TokenKind.ThisKeyword
             || input[after].Kind = TokenKind.OperatorKeyword
             || (input[after].Kind >= TokenKind.BoolKeyword
                 && input[after].Kind <= TokenKind.ObjectKeyword)))
        || match this.Next with
           | TokenKind.PublicKeyword
           | TokenKind.PrivateKeyword
           | TokenKind.ProtectedKeyword
           | TokenKind.InternalKeyword
           | TokenKind.StaticKeyword
           | TokenKind.AbstractKeyword
           | TokenKind.SealedKeyword
           | TokenKind.VirtualKeyword
           | TokenKind.OverrideKeyword
           | TokenKind.NewKeyword
           | TokenKind.ReadOnlyKeyword
           | TokenKind.VolatileKeyword
           | TokenKind.UnsafeKeyword
           | TokenKind.ExternKeyword -> true
           | _ -> false

    member private this.ContextualModifier() =
        match this.Next with
        | TokenKind.ClassKeyword
        | TokenKind.StructKeyword
        | TokenKind.InterfaceKeyword
        | TokenKind.EnumKeyword
        | TokenKind.DelegateKeyword
        | TokenKind.EventKeyword
        | TokenKind.ConstKeyword
        | TokenKind.FixedKeyword -> true
        | TokenKind.IdentifierToken when
            this.Word(1, "partial")
            || this.Word(1, "record")
            || this.Word(1, "required")
            || this.Word(1, "file")
            || this.Word(1, "safe")
            || this.Word(1, "closed")
            ->
            true
        | _ -> this.AsyncModifier()

    member private this.Modifiers(items: ChildList) =
        let mutable more = true

        while more do
            match this.Kind with
            | TokenKind.PublicKeyword
            | TokenKind.PrivateKeyword
            | TokenKind.ProtectedKeyword
            | TokenKind.InternalKeyword
            | TokenKind.StaticKeyword
            | TokenKind.AbstractKeyword
            | TokenKind.SealedKeyword
            | TokenKind.VirtualKeyword
            | TokenKind.OverrideKeyword
            | TokenKind.NewKeyword
            | TokenKind.ReadOnlyKeyword
            | TokenKind.VolatileKeyword
            | TokenKind.UnsafeKeyword
            | TokenKind.ExternKeyword
            | TokenKind.ConstKeyword
            | TokenKind.FixedKeyword -> this.Take items
            | TokenKind.RefKeyword when this.RefStructModifier() -> this.Take items
            | TokenKind.IdentifierToken when
                this.Next <> TokenKind.SemicolonToken
                && this.Next <> TokenKind.OpenParenToken
                && this.Next <> TokenKind.EqualsToken
                ->
                let promoted =
                    if this.Word(0, "partial") then
                        if
                            this.Next = TokenKind.IdentifierToken
                            && (match this.Peek 2 with
                                | TokenKind.SemicolonToken
                                | TokenKind.EqualsToken
                                | TokenKind.CommaToken -> true
                                | _ -> false)
                        then
                            TokenKind.None
                        else
                            TokenKind.PartialKeyword
                    elif this.Word(0, "required") then
                        TokenKind.RequiredKeyword
                    elif this.Word(0, "file") then
                        TokenKind.FileKeyword
                    elif this.Word(0, "async") && this.AsyncModifier() then
                        TokenKind.AsyncKeyword
                    elif this.Word(0, "safe") && this.ContextualModifier() then
                        TokenKind.SafeKeyword
                    elif this.Word(0, "closed") && this.ContextualModifier() then
                        TokenKind.ClosedKeyword
                    else
                        TokenKind.None

                if promoted = TokenKind.None then
                    more <- false
                else
                    if promoted = TokenKind.AsyncKeyword then
                        asyncContext <- true

                    this.Take(items, promoted)
            | _ -> more <- false

    member private this.TypeParameters(items: ChildList) =
        if this.At TokenKind.LessThanToken then
            let start, list = this.Start, children ()
            this.Take list
            let mutable more = true

            while more && not (this.At TokenKind.EndOfFileToken) do
                let before, paramStart, param = position, this.Start, children ()
                this.Attributes param

                if this.At TokenKind.InKeyword || this.At TokenKind.OutKeyword then
                    this.Take param

                this.Expect(param, TokenKind.IdentifierToken)
                list.Add(this.Make(NodeKind.TypeParameter, paramStart, param))

                if this.At TokenKind.CommaToken then
                    this.Take list
                else
                    more <- false

                if position = before then
                    more <- false

            this.CloseTypeArguments list
            items.Add(this.Make(NodeKind.TypeParameterList, start, list))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Constraints(items: ChildList) =
        while this.Word(0, "where") do
            let start, clause = this.Start, children ()
            this.Take(clause, TokenKind.WhereKeyword)
            clause.Add(this.Single NodeKind.IdentifierName)
            this.Expect(clause, TokenKind.ColonToken)
            let mutable more = true

            while more && not (this.At TokenKind.EndOfFileToken) do
                let before, constraintStart, constraintItems = position, this.Start, children ()

                let kind =
                    match this.Kind with
                    | TokenKind.ClassKeyword
                    | TokenKind.StructKeyword
                    | TokenKind.DefaultKeyword ->
                        let kind =
                            match this.Kind with
                            | TokenKind.ClassKeyword -> NodeKind.ClassConstraint
                            | TokenKind.StructKeyword -> NodeKind.StructConstraint
                            | _ -> NodeKind.DefaultConstraint

                        this.Take constraintItems

                        if this.At TokenKind.QuestionToken then
                            this.Take constraintItems

                        kind
                    | TokenKind.NewKeyword ->
                        this.Take constraintItems
                        this.Expect(constraintItems, TokenKind.OpenParenToken)
                        this.Expect(constraintItems, TokenKind.CloseParenToken)
                        NodeKind.ConstructorConstraint
                    | _ when this.Word(0, "allows") ->
                        this.Take(constraintItems, TokenKind.AllowsKeyword)
                        let refStart, refItems = this.Start, children ()
                        this.Expect(refItems, TokenKind.RefKeyword)
                        this.Expect(refItems, TokenKind.StructKeyword)

                        constraintItems.Add(
                            this.Make(NodeKind.RefStructConstraint, refStart, refItems)
                        )

                        NodeKind.AllowsConstraintClause
                    | _ ->
                        constraintItems.Add(this.Type())
                        NodeKind.TypeConstraint

                clause.Add(this.Make(kind, constraintStart, constraintItems))

                if this.At TokenKind.CommaToken then
                    this.Take clause
                else
                    more <- false

                if position = before then
                    more <- false

            items.Add(this.Make(NodeKind.TypeParameterConstraintClause, start, clause))

    member private this.Parameter(optionalNames: bool) : int =
        let paramStart, param = this.Start, children ()
        this.Attributes param
        let mutable modifiers = true

        while modifiers do
            match this.Kind with
            | TokenKind.RefKeyword
            | TokenKind.OutKeyword
            | TokenKind.InKeyword
            | TokenKind.ParamsKeyword
            | TokenKind.ThisKeyword
            | TokenKind.ReadOnlyKeyword -> this.Take param
            | _ when this.Word(0, "scoped") -> this.Take(param, TokenKind.ScopedKeyword)
            | _ -> modifiers <- false

        if this.At TokenKind.ArgListKeyword then
            this.Take param
        else
            param.Add(this.Type())

            if not optionalNames || this.At TokenKind.IdentifierToken then
                this.Expect(param, TokenKind.IdentifierToken)

        if this.At TokenKind.EqualsToken then
            param.Add(this.Initializer())

        this.Make(NodeKind.Parameter, paramStart, param)

    member private this.Parameters(bracketed: bool) : int = this.Parameters(bracketed, false)

    member private this.Parameters(bracketed: bool, optionalNames: bool) : int =
        let start, items = this.Start, children ()

        let close =
            if bracketed then
                TokenKind.CloseBracketToken
            else
                TokenKind.CloseParenToken

        this.Expect(
            items,
            if bracketed then
                TokenKind.OpenBracketToken
            else
                TokenKind.OpenParenToken
        )

        let mutable more = not (this.At close)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before = position

            let plain =
                match current with
                | TokenKind.OpenBracketToken
                | TokenKind.RefKeyword
                | TokenKind.OutKeyword
                | TokenKind.InKeyword
                | TokenKind.ParamsKeyword
                | TokenKind.ThisKeyword
                | TokenKind.ReadOnlyKeyword
                | TokenKind.ArgListKeyword -> false
                | _ -> not (this.Word(0, "scoped"))

            let parameter =
                if not plain then
                    this.Parameter(optionalNames)
                else
                    let paramStart = this.Start
                    let parameterType = this.Type()

                    if this.At TokenKind.IdentifierToken && this.Next <> TokenKind.EqualsToken then
                        let name = this.TakeChild()
                        tree.AddNode2(NodeKind.Parameter, paramStart, parameterType, name)
                    else
                        let param = children ()
                        param.Add parameterType

                        if not optionalNames || this.At TokenKind.IdentifierToken then
                            this.Expect(param, TokenKind.IdentifierToken)

                        if this.At TokenKind.EqualsToken then
                            param.Add(this.Initializer())

                        this.Make(NodeKind.Parameter, paramStart, param)

            items.Add parameter

            if this.At TokenKind.CommaToken then
                this.Take items
            else
                more <- false

            if position = before then
                more <- false

        this.Expect(items, close)

        this.Make(
            (if bracketed then
                 NodeKind.BracketedParameterList
             else
                 NodeKind.ParameterList),
            start,
            items
        )

    member private this.Initializer() : int =
        let start = this.Start
        let equals = this.TakeChild()

        let value =
            if this.At TokenKind.OpenBraceToken then
                this.ExpressionInitializer(NodeKind.ArrayInitializerExpression)
            else
                this.Expression()

        match current with
        | TokenKind.CommaToken
        | TokenKind.SemicolonToken
        | TokenKind.CloseParenToken
        | TokenKind.CloseBracketToken
        | TokenKind.CloseBraceToken
        | TokenKind.EndOfFileToken ->
            tree.AddNode2(NodeKind.EqualsValueClause, start, equals, value)
        | _ ->

            let items = children ()
            items.Add equals
            items.Add value

            this.SkipUntil(
                items,
                struct (TokenKind.CommaToken,
                        TokenKind.SemicolonToken,
                        TokenKind.CloseParenToken,
                        TokenKind.CloseBracketToken,
                        TokenKind.CloseBraceToken)
            )

            this.Make(NodeKind.EqualsValueClause, start, items)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.SkipUntil
        (items: ChildList, stops: struct (TokenKind * TokenKind * TokenKind * TokenKind * TokenKind)) =
        let struct (a, b, c, d, e) = stops

        if
            not (
                current = a
                || current = b
                || current = c
                || current = d
                || current = e
                || current = TokenKind.EndOfFileToken
            )
        then
            this.SkipUntilCore(items, stops)

    member private this.SkipUntilCore
        (items: ChildList, stops: struct (TokenKind * TokenKind * TokenKind * TokenKind * TokenKind)) =
        let struct (a, b, c, d, e) = stops
        let mutable parens, brackets, braces = 0, 0, 0
        let mutable more = true

        while more && not (this.At TokenKind.EndOfFileToken) do
            let kind = this.Kind

            if
                parens = 0
                && brackets = 0
                && braces = 0
                && (kind = a || kind = b || kind = c || kind = d || kind = e)
            then
                more <- false
            else
                match this.Kind with
                | TokenKind.OpenParenToken -> parens <- parens + 1
                | TokenKind.CloseParenToken -> parens <- max 0 (parens - 1)
                | TokenKind.OpenBracketToken -> brackets <- brackets + 1
                | TokenKind.CloseBracketToken -> brackets <- max 0 (brackets - 1)
                | TokenKind.OpenBraceToken -> braces <- braces + 1
                | TokenKind.CloseBraceToken -> braces <- max 0 (braces - 1)
                | _ -> ()

                this.Skip items

    member private this.Skip(items: ChildList) =
        tree.Recover()
        this.Take items

    member private this.Body(items: ChildList) =
        if this.At TokenKind.OpenBraceToken then
            items.Add(this.Block())
        elif this.At TokenKind.EqualsGreaterThanToken then
            let start, arrow = this.Start, children ()
            this.Take arrow
            arrow.Add(this.Expression())

            this.SkipUntil(
                arrow,
                struct (TokenKind.SemicolonToken,
                        TokenKind.CloseBraceToken,
                        TokenKind.None,
                        TokenKind.None,
                        TokenKind.None)
            )

            items.Add(this.Make(NodeKind.ArrowExpressionClause, start, arrow))
            this.Expect(items, TokenKind.SemicolonToken)
        else
            this.Expect(items, TokenKind.SemicolonToken)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Accessors() : int =
        let start, items = this.Start, children ()
        this.Take items

        while not (this.At TokenKind.CloseBraceToken)
              && not (this.At TokenKind.EndOfFileToken) do
            let before, accessorStart, accessor = position, this.Start, children ()
            this.Attributes accessor
            this.Modifiers accessor

            let struct (tokenKind, kind) =
                if this.Word(0, "get") then
                    struct (TokenKind.GetKeyword, NodeKind.GetAccessorDeclaration)
                elif this.Word(0, "set") then
                    struct (TokenKind.SetKeyword, NodeKind.SetAccessorDeclaration)
                elif this.Word(0, "init") then
                    struct (TokenKind.InitKeyword, NodeKind.InitAccessorDeclaration)
                elif this.Word(0, "add") then
                    struct (TokenKind.AddKeyword, NodeKind.AddAccessorDeclaration)
                elif this.Word(0, "remove") then
                    struct (TokenKind.RemoveKeyword, NodeKind.RemoveAccessorDeclaration)
                else
                    struct (TokenKind.None, NodeKind.UnknownAccessorDeclaration)

            this.Take(accessor, tokenKind)
            this.Body accessor
            items.Add(this.Make(kind, accessorStart, accessor))

            if position = before then
                this.Skip items

        this.Expect(items, TokenKind.CloseBraceToken)
        this.Make(NodeKind.AccessorList, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.FixedSize() : int =
        let start, items = this.Start, children ()
        this.Take items
        let argStart, arg = this.Start, children ()
        arg.Add(this.Expression())

        this.SkipUntil(
            arg,
            struct (TokenKind.CloseBracketToken,
                    TokenKind.None,
                    TokenKind.None,
                    TokenKind.None,
                    TokenKind.None)
        )

        items.Add(this.Make(NodeKind.Argument, argStart, arg))
        this.Expect(items, TokenKind.CloseBracketToken)
        this.Make(NodeKind.BracketedArgumentList, start, items)

    member private this.Declarator() : int =
        if current = TokenKind.IdentifierToken && next <> TokenKind.OpenBracketToken then
            let start = this.Start
            let name = this.TakeChild()

            if current = TokenKind.EqualsToken then
                tree.AddNode2(NodeKind.VariableDeclarator, start, name, this.Initializer())
            else
                tree.AddNode1(NodeKind.VariableDeclarator, start, name)
        else
            this.Variable(this.Start, children ())

    member private this.Variable(start: int, items: ChildList) : int =
        this.Expect(items, TokenKind.IdentifierToken)

        if this.At TokenKind.OpenBracketToken then
            items.Add(this.FixedSize())

        if this.At TokenKind.EqualsToken then
            items.Add(this.Initializer())

        this.Make(NodeKind.VariableDeclarator, start, items)

    member private this.IsScopedType(cursor: int) =
        if
            cursor >= input.Count
            || input[cursor].Length <> 6
            || not (this.Word(cursor - position, "scoped"))
        then
            false
        else
            let struct (valid, after, offset, _) =
                ExpressionSyntax.scan input (cursor + 1) false

            valid
            && offset = 0
            && after < input.Count
            && input.KindOf after = TokenKind.IdentifierToken

    member private this.ScanStatementType(cursor: int) =
        let start = if this.IsScopedType(cursor) then cursor + 1 else cursor

        if start >= input.Count then
            struct (false, start, 0, false)
        else
            match input.KindOf start with
            | TokenKind.IdentifierToken ->
                if
                    start + 1 < input.Count
                    && (match input.KindOf(start + 1) with
                        | TokenKind.IdentifierToken
                        | TokenKind.LessThanToken
                        | TokenKind.DotToken
                        | TokenKind.ColonColonToken
                        | TokenKind.QuestionToken
                        | TokenKind.AsteriskToken
                        | TokenKind.OpenBracketToken -> true
                        | _ -> false)
                then
                    ExpressionSyntax.scan input start false
                else
                    struct (false, start, 0, false)
            | TokenKind.OpenParenToken ->
                if this.TupleTypeEnd(start, TokenKind.IdentifierToken) < 0 then
                    struct (false, start, 0, false)
                else
                    ExpressionSyntax.scan input start false
            | TokenKind.RefKeyword
            | TokenKind.DelegateKeyword -> ExpressionSyntax.scan input start false
            | kind when ExpressionSyntax.predefined kind -> ExpressionSyntax.scan input start false
            | _ -> struct (false, start, 0, false)

    member private this.IsLocalDeclaration(afterOut: outref<int>) =
        let struct (valid, after, offset, _) = this.ScanStatementType(position)
        afterOut <- after

        valid
        && offset = 0
        && after < input.Count
        && input.KindOf after = TokenKind.IdentifierToken
        && not (
            input[position].Length = 5
            && this.Word(0, "await")
            && (asyncContext
                || (match this.Peek(after - position + 1) with
                    | TokenKind.SemicolonToken
                    | TokenKind.CommaToken
                    | TokenKind.EqualsToken -> false
                    | _ -> true))
        )
        && this.Peek(after - position + 1) <> TokenKind.OpenParenToken
        && this.Peek(after - position + 1) <> TokenKind.LessThanToken

    member private this.IsLocalDeclaration() =
        let mutable after = 0
        this.IsLocalDeclaration(&after)

    member private this.IsUsingDeclaration() =
        let mutable after = 0

        if not (this.IsLocalDeclaration(&after)) then
            false
        elif after <= position || input[after - 1].Kind <> TokenKind.QuestionToken then
            true
        else
            match this.Peek(after - position + 1) with
            | TokenKind.CommaToken
            | TokenKind.CloseParenToken -> true
            | TokenKind.EqualsToken ->
                this.Kind <> TokenKind.IdentifierToken || not (this.ExpressionHasColon(after))
            | _ -> false

    member private this.DeclarationPrefix() =
        let mutable cursor = position

        while cursor < input.Count && input.KindOf cursor = TokenKind.OpenBracketToken do
            let mutable depth = 1
            cursor <- cursor + 1

            while cursor < input.Count && depth > 0 do
                if input.KindOf cursor = TokenKind.OpenBracketToken then
                    depth <- depth + 1
                elif input.KindOf cursor = TokenKind.CloseBracketToken then
                    depth <- depth - 1

                cursor <- cursor + 1

        let afterAttributes = cursor
        let mutable more = true

        while more && cursor < input.Count do
            match input.KindOf cursor with
            | TokenKind.PublicKeyword
            | TokenKind.PrivateKeyword
            | TokenKind.ProtectedKeyword
            | TokenKind.InternalKeyword
            | TokenKind.StaticKeyword
            | TokenKind.AbstractKeyword
            | TokenKind.SealedKeyword
            | TokenKind.VirtualKeyword
            | TokenKind.OverrideKeyword
            | TokenKind.NewKeyword
            | TokenKind.ReadOnlyKeyword
            | TokenKind.VolatileKeyword
            | TokenKind.UnsafeKeyword
            | TokenKind.ExternKeyword -> cursor <- cursor + 1
            | TokenKind.IdentifierToken when
                (let len = input[cursor].Length in len >= 4 && len <= 7)
                && (this.Word(cursor - position, "async")
                    || this.Word(cursor - position, "partial")
                    || this.Word(cursor - position, "file"))
                ->
                cursor <- cursor + 1
            | TokenKind.IdentifierToken when
                (let len = input[cursor].Length in len = 4 || len = 6)
                && (this.Word(cursor - position, "closed") || this.Word(cursor - position, "safe"))
                && (let next = this.Peek(cursor - position + 1)

                    next = TokenKind.IdentifierToken
                    || (int next >= int TokenKind.BoolKeyword
                        && int next < int TokenKind.ElifKeyword))
                ->
                cursor <- cursor + 1
            | TokenKind.RefKeyword ->
                let mutable after = cursor + 1

                while this.Word(after - position, "partial") do
                    after <- after + 1

                if this.Peek(after - position) = TokenKind.StructKeyword then
                    cursor <- cursor + 1
                else
                    more <- false
            | _ -> more <- false

        struct (afterAttributes, cursor)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.LocalFunctionCandidate(cursor: int) =
        let struct (valid, after, offset, _) =
            if cursor >= input.Count then
                struct (false, cursor, 0, false)
            else
                match input.KindOf cursor with
                | TokenKind.IdentifierToken ->
                    if
                        cursor + 1 < input.Count
                        && (match input.KindOf(cursor + 1) with
                            | TokenKind.IdentifierToken
                            | TokenKind.LessThanToken
                            | TokenKind.DotToken
                            | TokenKind.ColonColonToken
                            | TokenKind.QuestionToken
                            | TokenKind.AsteriskToken
                            | TokenKind.OpenBracketToken -> true
                            | _ -> false)
                    then
                        ExpressionSyntax.scan input cursor false
                    else
                        struct (false, cursor, 0, false)
                | TokenKind.OpenParenToken ->
                    if this.TupleTypeEnd(cursor, TokenKind.IdentifierToken) < 0 then
                        struct (false, cursor, 0, false)
                    else
                        ExpressionSyntax.scan input cursor false
                | TokenKind.RefKeyword
                | TokenKind.DelegateKeyword -> ExpressionSyntax.scan input cursor false
                | kind when ExpressionSyntax.predefined kind ->
                    ExpressionSyntax.scan input cursor false
                | _ -> struct (false, cursor, 0, false)

        let parameters =
            if
                not valid
                || offset <> 0
                || after + 1 >= input.Count
                || input.KindOf after <> TokenKind.IdentifierToken
            then
                -1
            elif input.KindOf(after + 1) = TokenKind.OpenParenToken then
                after + 1
            elif input.KindOf(after + 1) = TokenKind.LessThanToken then
                let mutable last, depth = after + 2, 1

                while last < input.Count && depth > 0 do
                    match input.KindOf last with
                    | TokenKind.OpenBracketToken ->
                        let mutable brackets = 1
                        last <- last + 1

                        while last < input.Count && brackets > 0 do
                            match input.KindOf last with
                            | TokenKind.OpenBracketToken -> brackets <- brackets + 1
                            | TokenKind.CloseBracketToken -> brackets <- brackets - 1
                            | _ -> ()

                            if brackets > 0 then
                                last <- last + 1
                    | TokenKind.LessThanToken -> depth <- depth + 1
                    | kind -> depth <- depth - ExpressionSyntax.closers kind

                    last <- last + 1

                if
                    depth = 0 && last < input.Count && input.KindOf last = TokenKind.OpenParenToken
                then
                    last
                else
                    -1
            else
                -1

        if parameters < 0 then
            false
        elif not (this.Word(0, "await")) then
            true
        else
            let mutable last, depth = parameters + 1, 1

            while last < input.Count && depth > 0 do
                if input.KindOf last = TokenKind.OpenParenToken then
                    depth <- depth + 1
                elif input.KindOf last = TokenKind.CloseParenToken then
                    depth <- depth - 1

                last <- last + 1

            depth = 0
            && last < input.Count
            && (input.KindOf last = TokenKind.OpenBraceToken
                || input.KindOf last = TokenKind.EqualsGreaterThanToken
                || this.Word(last - position, "where"))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.LocalFunctionCursor() =
        match this.Kind with
        | TokenKind.IdentifierToken
        | TokenKind.OpenBracketToken
        | TokenKind.OpenParenToken
        | TokenKind.RefKeyword
        | TokenKind.DelegateKeyword
        | TokenKind.PublicKeyword
        | TokenKind.PrivateKeyword
        | TokenKind.ProtectedKeyword
        | TokenKind.InternalKeyword
        | TokenKind.StaticKeyword
        | TokenKind.AbstractKeyword
        | TokenKind.SealedKeyword
        | TokenKind.VirtualKeyword
        | TokenKind.OverrideKeyword
        | TokenKind.NewKeyword
        | TokenKind.ReadOnlyKeyword
        | TokenKind.VolatileKeyword
        | TokenKind.UnsafeKeyword
        | TokenKind.ExternKeyword ->
            let struct (afterAttributes, afterModifiers) = this.DeclarationPrefix()

            if asyncContext && input[position].Length = 5 && this.Word(0, "await") then
                -1
            else
                let mutable cursor, result = afterAttributes, -1

                while result < 0 && cursor <= afterModifiers do
                    if this.LocalFunctionCandidate cursor then
                        result <- cursor

                    cursor <- cursor + 1

                result
        | kind when ExpressionSyntax.predefined kind ->
            if this.LocalFunctionCandidate position then
                position
            else
                -1
        | _ -> -1

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Designation() : int =
        ensureStack ()
        let start, items = this.Start, children ()

        if this.At TokenKind.OpenParenToken then
            this.Take items
            let mutable more = true

            while more && not (this.At TokenKind.EndOfFileToken) do
                let before = position
                items.Add(this.Designation())

                if this.At TokenKind.CommaToken then
                    this.Take items
                else
                    more <- false

                if position = before then
                    more <- false

            this.Expect(items, TokenKind.CloseParenToken)
            this.Make(NodeKind.ParenthesizedVariableDesignation, start, items)
        else
            let discard = this.Word(0, "_")

            if discard then
                this.Take(items, TokenKind.UnderscoreToken)
            else
                this.Expect(items, TokenKind.IdentifierToken)

            this.Make(
                (if discard then
                     NodeKind.DiscardDesignation
                 else
                     NodeKind.SingleVariableDesignation),
                start,
                items
            )

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.DeclarationExpression() : int =
        let start, items = this.Start, children ()
        items.Add(this.Type())
        items.Add(this.Designation())
        this.Make(NodeKind.DeclarationExpression, start, items)

    member private this.DeconstructionEnd() =
        if not (this.Word(0, "var")) || this.Next <> TokenKind.OpenParenToken then
            -1
        else
            let mutable cursor, depth = position + 2, 1
            let mutable valid, comma = true, false

            while valid && cursor < input.Count && depth > 0 do
                match input[cursor].Kind with
                | TokenKind.IdentifierToken -> ()
                | TokenKind.CommaToken -> comma <- true
                | TokenKind.OpenParenToken -> depth <- depth + 1
                | TokenKind.CloseParenToken -> depth <- depth - 1
                | _ -> valid <- false

                cursor <- cursor + 1

            if valid && comma && depth = 0 && cursor < input.Count then
                cursor
            else
                -1

    member private this.IsDeconstruction() = this.IsDeconstruction(false)

    member private this.IsDeconstruction(tuple: bool) =
        let after = this.DeconstructionEnd()

        after >= 0
        && (input[after].Kind = TokenKind.EqualsToken
            || input[after].Kind = TokenKind.InKeyword
            || (tuple
                && (input[after].Kind = TokenKind.CommaToken
                    || input[after].Kind = TokenKind.CloseParenToken)))

    member private this.VariableDeclaration() : int =
        let start, items = this.Start, children ()
        items.Add(this.Type())
        items.Add(this.Declarator())

        while this.At TokenKind.CommaToken do
            this.Take items
            items.Add(this.Declarator())

        this.Make(NodeKind.VariableDeclaration, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.LocalFunction(typeCursor: int) : int =
        let previousAsync = asyncContext
        asyncContext <- false
        let start, items = this.Start, children ()

        try
            this.Attributes items

            while position < typeCursor do
                if this.Word(0, "async") then
                    asyncContext <- true
                    this.Take(items, TokenKind.AsyncKeyword)
                else
                    this.Take items

            items.Add(this.Type())
            this.Expect(items, TokenKind.IdentifierToken)
            this.TypeParameters items
            items.Add(this.Parameters(false))
            this.Constraints items
            this.Body items
            this.Make(NodeKind.LocalFunctionStatement, start, items)
        finally
            asyncContext <- previousAsync

    member private this.Block() : int =
        let start, items = this.Start, children ()
        this.Expect(items, TokenKind.OpenBraceToken)

        while not (this.At TokenKind.CloseBraceToken)
              && not (this.At TokenKind.EndOfFileToken) do
            let before = position
            items.Add(this.Statement())

            if position = before then
                this.Skip items

        this.Expect(items, TokenKind.CloseBraceToken)
        this.Make(NodeKind.Block, start, items)

    member private this.Condition(items: ChildList) =
        this.Expect(items, TokenKind.OpenParenToken)
        items.Add(this.Expression())

        this.SkipUntil(
            items,
            struct (TokenKind.CloseParenToken,
                    TokenKind.SemicolonToken,
                    TokenKind.None,
                    TokenKind.None,
                    TokenKind.None)
        )

        this.Expect(items, TokenKind.CloseParenToken)

    member private this.ExpressionList(items: ChildList, close: TokenKind) =
        let mutable more = not (this.At close)

        while more && not (this.At TokenKind.EndOfFileToken) do
            let before = position
            items.Add(this.Expression())

            this.SkipUntil(
                items,
                struct (TokenKind.CommaToken,
                        close,
                        TokenKind.CloseBraceToken,
                        TokenKind.None,
                        TokenKind.None)
            )

            if this.At TokenKind.CommaToken then
                this.Take items
            else
                more <- false

            if position = before then
                more <- false

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ForStatement() : int =
        let start, items = this.Start, children ()
        this.Take items
        this.Expect(items, TokenKind.OpenParenToken)

        if this.IsLocalDeclaration() then
            items.Add(this.VariableDeclaration())
        else
            this.ExpressionList(items, TokenKind.SemicolonToken)

        this.Expect(items, TokenKind.SemicolonToken)

        if not (this.At TokenKind.SemicolonToken) then
            items.Add(this.Expression())

        this.SkipUntil(
            items,
            struct (TokenKind.SemicolonToken,
                    TokenKind.CloseParenToken,
                    TokenKind.CloseBraceToken,
                    TokenKind.None,
                    TokenKind.None)
        )

        this.Expect(items, TokenKind.SemicolonToken)
        this.ExpressionList(items, TokenKind.CloseParenToken)
        this.Expect(items, TokenKind.CloseParenToken)
        items.Add(this.Statement())
        this.Make(NodeKind.ForStatement, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ForEachStatement() : int =
        let start, items = this.Start, children ()

        if this.Word(0, "await") then
            this.Take(items, TokenKind.AwaitKeyword)

        this.Expect(items, TokenKind.ForEachKeyword)
        this.Expect(items, TokenKind.OpenParenToken)
        let variable = not (this.IsLocalDeclaration())

        if variable then
            items.Add(this.Expression())
        else
            items.Add(this.Type())
            this.Expect(items, TokenKind.IdentifierToken)

        this.SkipUntil(
            items,
            struct (TokenKind.InKeyword,
                    TokenKind.CloseParenToken,
                    TokenKind.CloseBraceToken,
                    TokenKind.None,
                    TokenKind.None)
        )

        this.Expect(items, TokenKind.InKeyword)
        items.Add(this.Expression())

        this.SkipUntil(
            items,
            struct (TokenKind.CloseParenToken,
                    TokenKind.CloseBraceToken,
                    TokenKind.None,
                    TokenKind.None,
                    TokenKind.None)
        )

        this.Expect(items, TokenKind.CloseParenToken)
        items.Add(this.Statement())

        this.Make(
            (if variable then
                 NodeKind.ForEachVariableStatement
             else
                 NodeKind.ForEachStatement),
            start,
            items
        )

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TryStatement() : int =
        let start, items = this.Start, children ()
        this.Take items
        items.Add(this.Block())

        while this.At TokenKind.CatchKeyword do
            let catchStart, clause = this.Start, children ()
            this.Take clause

            if this.At TokenKind.OpenParenToken then
                let declarationStart, declaration = this.Start, children ()
                this.Take declaration
                declaration.Add(this.Type())

                if this.At TokenKind.IdentifierToken then
                    this.Take declaration

                this.Expect(declaration, TokenKind.CloseParenToken)
                clause.Add(this.Make(NodeKind.CatchDeclaration, declarationStart, declaration))

            if this.Word(0, "when") then
                let filterStart, filter = this.Start, children ()
                this.Take(filter, TokenKind.WhenKeyword)
                this.Condition filter
                clause.Add(this.Make(NodeKind.CatchFilterClause, filterStart, filter))

            clause.Add(this.Block())
            items.Add(this.Make(NodeKind.CatchClause, catchStart, clause))

        if this.At TokenKind.FinallyKeyword then
            let finallyStart, clause = this.Start, children ()
            this.Take clause
            clause.Add(this.Block())
            items.Add(this.Make(NodeKind.FinallyClause, finallyStart, clause))

        this.Make(NodeKind.TryStatement, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.SwitchLabel() : int =
        let start, items = this.Start, children ()
        let isDefault = this.At TokenKind.DefaultKeyword
        this.Take items

        let mutable kind =
            if isDefault then
                NodeKind.DefaultSwitchLabel
            else
                NodeKind.CaseSwitchLabel

        if not isDefault then
            let previousWhen = whenKeyword
            whenKeyword <- true

            let value =
                try
                    this.Pattern(1, true)
                finally
                    whenKeyword <- previousWhen

            let pattern = this.IsPatternNode(value)

            if pattern || this.Word(0, "when") then
                kind <- NodeKind.CasePatternSwitchLabel

                items.Add(
                    if pattern then
                        value
                    else
                        this.Wrap(NodeKind.ConstantPattern, value)
                )

                if this.Word(0, "when") then
                    let whenStart, clause = this.Start, children ()
                    this.Take(clause, TokenKind.WhenKeyword)
                    clause.Add(this.Expression(1, false))
                    items.Add(this.Make(NodeKind.WhenClause, whenStart, clause))
            else
                items.Add value

        this.SkipUntil(
            items,
            struct (TokenKind.ColonToken,
                    TokenKind.CloseBraceToken,
                    TokenKind.None,
                    TokenKind.None,
                    TokenKind.None)
        )

        this.Expect(items, TokenKind.ColonToken)
        this.Make(kind, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.SwitchTuple() =
        let mutable cursor, depth = position + 1, 0
        let mutable comma, more = false, this.At TokenKind.OpenParenToken

        while more && cursor < input.Count do
            let kind = input[cursor].Kind

            if depth = 0 && kind = TokenKind.CommaToken then
                comma <- true
                more <- false
            elif depth = 0 && kind = TokenKind.CloseParenToken then
                more <- false
            elif kind = TokenKind.LessThanToken then
                let struct (valid, after, offset, _) = ExpressionSyntax.scan input cursor true

                if valid && offset = 0 then
                    cursor <- after - 1
            else
                match kind with
                | TokenKind.OpenParenToken
                | TokenKind.OpenBracketToken
                | TokenKind.OpenBraceToken -> depth <- depth + 1
                | TokenKind.CloseParenToken
                | TokenKind.CloseBracketToken
                | TokenKind.CloseBraceToken -> depth <- depth - 1
                | _ -> ()

            cursor <- cursor + 1

        comma

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.SwitchStatement() : int =
        let start, items = this.Start, children ()
        this.Take items

        if this.SwitchTuple() then
            items.Add(this.ParenthesizedOrTuple())
        else
            this.Condition items

        this.Expect(items, TokenKind.OpenBraceToken)

        while not (this.At TokenKind.CloseBraceToken)
              && not (this.At TokenKind.EndOfFileToken) do
            let before, sectionStart, section = position, this.Start, children ()

            while this.At TokenKind.CaseKeyword || this.At TokenKind.DefaultKeyword do
                section.Add(this.SwitchLabel())

            while not (this.At TokenKind.CaseKeyword)
                  && not (this.At TokenKind.DefaultKeyword)
                  && not (this.At TokenKind.CloseBraceToken)
                  && not (this.At TokenKind.EndOfFileToken) do
                let statementBefore = position
                section.Add(this.Statement())

                if position = statementBefore then
                    this.Take section

            items.Add(this.Make(NodeKind.SwitchSection, sectionStart, section))

            if position = before then
                this.Skip items

        this.Expect(items, TokenKind.CloseBraceToken)
        this.Make(NodeKind.SwitchStatement, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.UsingStatement() : int =
        let start, items = this.Start, children ()

        if this.Word(0, "await") then
            this.Take(items, TokenKind.AwaitKeyword)

        this.Expect(items, TokenKind.UsingKeyword)

        if this.At TokenKind.OpenParenToken then
            this.Take items

            if this.IsUsingDeclaration() then
                items.Add(this.VariableDeclaration())
            else
                items.Add(this.Expression())

            this.SkipUntil(
                items,
                struct (TokenKind.CloseParenToken,
                        TokenKind.CloseBraceToken,
                        TokenKind.None,
                        TokenKind.None,
                        TokenKind.None)
            )

            this.Expect(items, TokenKind.CloseParenToken)
            items.Add(this.Statement())
            this.Make(NodeKind.UsingStatement, start, items)
        else
            items.Add(this.VariableDeclaration())
            this.Expect(items, TokenKind.SemicolonToken)
            this.Make(NodeKind.LocalDeclarationStatement, start, items)

    member private this.Statement() : int =
        ensureStack ()
        let start = this.Start

        match this.Kind with
        | TokenKind.IdentifierToken when this.PlainExpressionStatement() ->
            this.ExpressionStatement start
        | _ when this.PlainLocalDeclaration() ->
            let declaration = this.VariableDeclaration()

            if current = TokenKind.SemicolonToken then
                tree.AddNode2(
                    NodeKind.LocalDeclarationStatement,
                    start,
                    declaration,
                    this.TakeChild()
                )
            else
                let items = children ()
                items.Add declaration
                this.Expect(items, TokenKind.SemicolonToken)
                this.Make(NodeKind.LocalDeclarationStatement, start, items)
        | TokenKind.OpenBraceToken -> this.Block()
        | TokenKind.SemicolonToken -> this.Single NodeKind.EmptyStatement
        | TokenKind.IfKeyword ->
            let items = children ()
            this.Take items
            this.Condition items
            items.Add(this.Statement())

            if this.At TokenKind.ElseKeyword then
                let elseStart, clause = this.Start, children ()
                this.Take clause
                clause.Add(this.Statement())
                items.Add(this.Make(NodeKind.ElseClause, elseStart, clause))

            this.Make(NodeKind.IfStatement, start, items)
        | TokenKind.ReturnKeyword
        | TokenKind.ThrowKeyword
        | TokenKind.BreakKeyword
        | TokenKind.ContinueKeyword ->
            let kind =
                match this.Kind with
                | TokenKind.ReturnKeyword -> NodeKind.ReturnStatement
                | TokenKind.ThrowKeyword -> NodeKind.ThrowStatement
                | TokenKind.BreakKeyword -> NodeKind.BreakStatement
                | _ -> NodeKind.ContinueStatement

            let keyword = this.TakeChild()

            let operand =
                if
                    (kind = NodeKind.ReturnStatement || kind = NodeKind.ThrowStatement)
                    && not (this.At TokenKind.SemicolonToken)
                then
                    this.Expression()
                elif
                    (kind = NodeKind.BreakStatement || kind = NodeKind.ContinueStatement)
                    && this.At TokenKind.IdentifierToken
                then
                    this.Single NodeKind.IdentifierName
                else
                    -1

            if this.At TokenKind.SemicolonToken then
                if operand >= 0 then
                    tree.AddNode3(kind, start, keyword, operand, this.TakeChild())
                else
                    tree.AddNode2(kind, start, keyword, this.TakeChild())
            else
                let items = children ()
                items.Add keyword

                if operand >= 0 then
                    items.Add operand

                this.SkipUntil(
                    items,
                    struct (TokenKind.SemicolonToken,
                            TokenKind.CloseBraceToken,
                            TokenKind.None,
                            TokenKind.None,
                            TokenKind.None)
                )

                this.Expect(items, TokenKind.SemicolonToken)
                this.Make(kind, start, items)
        | _ -> this.StatementCold start

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.StatementCold(start: int) : int =
        match this.Kind with
        | TokenKind.SwitchKeyword -> this.SwitchStatement()
        | TokenKind.ForKeyword -> this.ForStatement()
        | TokenKind.ForEachKeyword -> this.ForEachStatement()
        | TokenKind.WhileKeyword
        | TokenKind.LockKeyword ->
            let items = children ()

            let kind =
                if this.At TokenKind.WhileKeyword then
                    NodeKind.WhileStatement
                else
                    NodeKind.LockStatement

            this.Take items
            this.Condition items
            items.Add(this.Statement())
            this.Make(kind, start, items)
        | TokenKind.DoKeyword ->
            let items = children ()
            this.Take items
            items.Add(this.Statement())
            this.Expect(items, TokenKind.WhileKeyword)
            this.Condition items
            this.Expect(items, TokenKind.SemicolonToken)
            this.Make(NodeKind.DoStatement, start, items)
        | TokenKind.TryKeyword -> this.TryStatement()
        | TokenKind.UsingKeyword -> this.UsingStatement()
        | TokenKind.FixedKeyword ->
            let items = children ()
            this.Take items
            this.Expect(items, TokenKind.OpenParenToken)
            items.Add(this.VariableDeclaration())
            this.Expect(items, TokenKind.CloseParenToken)
            items.Add(this.Statement())
            this.Make(NodeKind.FixedStatement, start, items)
        | TokenKind.CheckedKeyword
        | TokenKind.UncheckedKeyword when this.Next = TokenKind.OpenBraceToken ->
            let items = children ()

            let kind =
                if this.At TokenKind.CheckedKeyword then
                    NodeKind.CheckedStatement
                else
                    NodeKind.UncheckedStatement

            this.Take items
            items.Add(this.Block())
            this.Make(kind, start, items)
        | TokenKind.GotoKeyword ->
            let items = children ()
            this.Take items

            let kind =
                if this.At TokenKind.CaseKeyword then
                    NodeKind.GotoCaseStatement
                elif this.At TokenKind.DefaultKeyword then
                    NodeKind.GotoDefaultStatement
                else
                    NodeKind.GotoStatement

            if kind <> NodeKind.GotoStatement then
                this.Take items

            if kind <> NodeKind.GotoDefaultStatement then
                items.Add(this.Expression())

            this.Expect(items, TokenKind.SemicolonToken)
            this.Make(kind, start, items)
        | TokenKind.ConstKeyword ->
            let items = children ()
            this.Take items
            items.Add(this.VariableDeclaration())
            this.Expect(items, TokenKind.SemicolonToken)
            this.Make(NodeKind.LocalDeclarationStatement, start, items)
        | _ ->
            let localFunction = this.LocalFunctionCursor()

            if localFunction >= 0 then
                this.LocalFunction(localFunction)
            else
                match this.Kind with
                | TokenKind.IdentifierToken when
                    input[position].Length = 5
                    && this.Word(0, "await")
                    && this.Next = TokenKind.UsingKeyword
                    ->
                    this.UsingStatement()
                | TokenKind.IdentifierToken when
                    input[position].Length = 5
                    && this.Word(0, "await")
                    && this.Next = TokenKind.ForEachKeyword
                    ->
                    this.ForEachStatement()
                | TokenKind.UnsafeKeyword when this.Next = TokenKind.OpenBraceToken ->
                    let items = children ()
                    this.Take items
                    items.Add(this.Block())
                    this.Make(NodeKind.UnsafeStatement, start, items)
                | TokenKind.IdentifierToken when
                    input[position].Length = 5
                    && this.Word(0, "yield")
                    && (this.Next = TokenKind.ReturnKeyword || this.Next = TokenKind.BreakKeyword)
                    ->
                    let items = children ()
                    this.Take(items, TokenKind.YieldKeyword)

                    let kind =
                        if this.At TokenKind.ReturnKeyword then
                            NodeKind.YieldReturnStatement
                        else
                            NodeKind.YieldBreakStatement

                    this.Take items

                    if kind = NodeKind.YieldReturnStatement then
                        items.Add(this.Expression())

                    this.Expect(items, TokenKind.SemicolonToken)
                    this.Make(kind, start, items)
                | TokenKind.IdentifierToken when this.Next = TokenKind.ColonToken ->
                    let items = children ()
                    this.Take items
                    this.Take items
                    items.Add(this.Statement())
                    this.Make(NodeKind.LabeledStatement, start, items)
                | _ when this.IsLocalDeclaration() && not (this.IsQuery()) ->
                    let items = children ()
                    items.Add(this.VariableDeclaration())
                    this.Expect(items, TokenKind.SemicolonToken)
                    this.Make(NodeKind.LocalDeclarationStatement, start, items)
                | _ -> this.ExpressionStatement start

    member private this.ExpressionStatement(start: int) : int =
        let expression = this.Expression()

        if current = TokenKind.SemicolonToken then
            tree.AddNode2(NodeKind.ExpressionStatement, start, expression, this.TakeChild())
        else

            let items = children ()
            items.Add expression

            this.SkipUntil(
                items,
                struct (TokenKind.SemicolonToken,
                        TokenKind.CloseBraceToken,
                        TokenKind.None,
                        TokenKind.None,
                        TokenKind.None)
            )

            this.Expect(items, TokenKind.SemicolonToken)
            this.Make(NodeKind.ExpressionStatement, start, items)

    member private this.PlainExpressionStatement() =
        let token = &this.CurrentRef()

        token.Kind = TokenKind.IdentifierToken
        && (let mutable cursor = position + 1

            while input.KindAt cursor = TokenKind.DotToken
                  && input.KindAt(cursor + 1) = TokenKind.IdentifierToken do
                cursor <- cursor + 2

            match input.KindAt cursor with
            | TokenKind.IdentifierToken
            | TokenKind.LessThanToken
            | TokenKind.DotToken
            | TokenKind.ColonColonToken
            | TokenKind.QuestionToken
            | TokenKind.AsteriskToken
            | TokenKind.OpenBracketToken -> false
            | TokenKind.ColonToken -> cursor > position + 1
            | _ -> true)
        && (match next with
            | TokenKind.DotToken
            | TokenKind.EqualsToken
            | TokenKind.PlusEqualsToken
            | TokenKind.MinusEqualsToken
            | TokenKind.QuestionQuestionEqualsToken
            | TokenKind.PlusPlusToken
            | TokenKind.MinusMinusToken
            | TokenKind.SemicolonToken -> true
            | _ -> this.NotStatementWord())

    member private this.PlainLocalDeclaration() =
        next = TokenKind.IdentifierToken
        && (match input.KindAt(position + 2) with
            | TokenKind.EqualsToken
            | TokenKind.SemicolonToken
            | TokenKind.CommaToken -> true
            | _ -> false)
        && (if current = TokenKind.IdentifierToken then
                not (this.CurrentRef().Length = 5 && this.Word(0, "await"))
            else
                ExpressionSyntax.predefined current)

    member private this.NotStatementWord() =
        let token = &this.CurrentRef()
        let length = token.Length

        length < 4
        || length > 7
        || (match length, source[token.Start] with
            | 4, 'f' -> not (this.Word(0, "file"))
            | 4, 's' -> not (this.Word(0, "safe"))
            | 5, 'a' -> not (this.Word(0, "async") || this.Word(0, "await"))
            | 5, 'y' -> not (this.Word(0, "yield"))
            | 6, 'c' -> not (this.Word(0, "closed"))
            | 6, 's' -> not (this.Word(0, "scoped"))
            | 7, 'p' -> not (this.Word(0, "partial"))
            | _ -> true)

    member private _.NameHasSeparator(distance: int) =
        let mutable cursor = min (position + distance) (input.Count - 1)

        if input[cursor].Kind <> TokenKind.IdentifierToken then
            false
        else
            cursor <- cursor + 1

            if cursor < input.Count && input[cursor].Kind = TokenKind.LessThanToken then
                let mutable depth = 1
                cursor <- cursor + 1

                while cursor < input.Count && depth > 0 do
                    let token = input[cursor]

                    if token.Kind = TokenKind.LessThanToken then
                        depth <- depth + 1
                    elif token.Length > 0 && source[token.Start] = '>' then
                        let mutable width = 0

                        while width < token.Length && source[token.Start + width] = '>' do
                            width <- width + 1

                        depth <- depth - width

                    cursor <- cursor + 1

            cursor < input.Count
            && (input[cursor].Kind = TokenKind.DotToken
                || input[cursor].Kind = TokenKind.ColonColonToken)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ExplicitInterface() : int =
        let specStart, spec = this.Start, children ()
        let nameStart = this.Start
        let mutable name = this.SimpleName()

        while (this.At TokenKind.DotToken || this.At TokenKind.ColonColonToken)
              && this.NameHasSeparator(1) do
            let parts = children ()
            let alias = this.At TokenKind.ColonColonToken
            parts.Add name
            this.Take parts
            parts.Add(this.SimpleName())

            name <-
                this.Make(
                    (if alias then
                         NodeKind.AliasQualifiedName
                     else
                         NodeKind.QualifiedName),
                    nameStart,
                    parts
                )

        spec.Add name
        this.Expect(spec, TokenKind.DotToken)

        this.Make(NodeKind.ExplicitInterfaceSpecifier, specStart, spec)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Operator(start: int, items: ChildList) : int =
        this.Take items

        if this.At TokenKind.CheckedKeyword then
            this.Take items

        this.Take items
        items.Add(this.Parameters(false))
        this.Body items
        this.Make(NodeKind.OperatorDeclaration, start, items)

    member private this.Member() : int =
        ensureStack ()
        let previousAsync, previousField = asyncContext, fieldContext
        asyncContext <- false
        fieldContext <- false

        try
            this.MemberCore()
        finally
            asyncContext <- previousAsync
            fieldContext <- previousField

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ExtensionOrConversionOrDestructor(start: int, items: ChildList) : int =
        if
            this.Word(0, "extension")
            && (this.Next = TokenKind.OpenParenToken || this.Next = TokenKind.LessThanToken)
        then
            this.Take(items, TokenKind.ExtensionKeyword)
            this.TypeParameters items
            items.Add(this.Parameters(false, true))
            this.Constraints items
            this.Expect(items, TokenKind.OpenBraceToken)

            while not (this.At TokenKind.CloseBraceToken || this.At TokenKind.EndOfFileToken) do
                let before = position
                items.Add(this.Member())

                if position = before then
                    this.Skip items

            this.Expect(items, TokenKind.CloseBraceToken)
            this.Make(NodeKind.ExtensionBlockDeclaration, start, items)
        elif this.At TokenKind.TildeToken then
            this.Take items
            this.Expect(items, TokenKind.IdentifierToken)
            items.Add(this.Parameters(false))
            this.Body items
            this.Make(NodeKind.DestructorDeclaration, start, items)
        else
            this.Take items

            if this.NameHasSeparator(0) then
                items.Add(this.ExplicitInterface())

            this.Expect(items, TokenKind.OperatorKeyword)

            if this.At TokenKind.CheckedKeyword then
                this.Take items

            items.Add(this.Type())
            items.Add(this.Parameters(false))
            this.Body items
            this.Make(NodeKind.ConversionOperatorDeclaration, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ConstructorDeclaration(start: int, items: ChildList) : int =
        this.Take items
        items.Add(this.Parameters(false))

        if this.At TokenKind.ColonToken then
            let initStart, init = this.Start, children ()
            this.Take init
            let baseCall = this.At TokenKind.BaseKeyword
            this.Take init
            init.Add(this.Arguments(false))

            items.Add(
                this.Make(
                    (if baseCall then
                         NodeKind.BaseConstructorInitializer
                     else
                         NodeKind.ThisConstructorInitializer),
                    initStart,
                    init
                )
            )

        this.Body items
        this.Make(NodeKind.ConstructorDeclaration, start, items)

    member private this.MemberCore() : int =
        let start, items = this.Start, children ()
        this.Attributes items
        this.Modifiers items

        if this.IsTypeDeclaration() then
            this.TypeDeclaration(start, items)
        elif
            this.At TokenKind.TildeToken
            || this.At TokenKind.ImplicitKeyword
            || this.At TokenKind.ExplicitKeyword
            || (this.Word(0, "extension")
                && (this.Peek(1) = TokenKind.OpenParenToken
                    || this.Peek(1) = TokenKind.LessThanToken))
        then
            this.ExtensionOrConversionOrDestructor(start, items)
        elif this.At TokenKind.IdentifierToken && this.Peek(1) = TokenKind.OpenParenToken then
            this.ConstructorDeclaration(start, items)
        else
            let event = this.At TokenKind.EventKeyword

            if event then
                this.Take items

            let typeStart = this.Start
            let typeNode = this.Type()

            if this.At TokenKind.OperatorKeyword then
                items.Add typeNode
                this.Operator(start, items)
            else
                let mutable explicitInterface = -1

                if this.NameHasSeparator(0) then
                    explicitInterface <- this.ExplicitInterface()

                if this.At TokenKind.OperatorKeyword then
                    items.Add typeNode

                    if explicitInterface >= 0 then
                        items.Add explicitInterface

                    this.Operator(start, items)
                else
                    let nameStart = this.Start
                    let indexer = this.At TokenKind.ThisKeyword

                    let nameToken =
                        let last = input.Count - 1

                        if indexer || this.At TokenKind.IdentifierToken then
                            let t = ~~~(tree.AddToken input[min position last])

                            if position < last then
                                this.Advance()

                            t
                        else
                            let next = input[min position last]

                            ~~~(tree.AddToken
                                    { next with
                                        Kind = TokenKind.IdentifierToken
                                        Length = 0
                                        LeadingCount = 0
                                        TrailingCount = 0
                                    })

                    if
                        indexer
                        || explicitInterface >= 0
                        || this.At TokenKind.OpenBraceToken
                        || this.At TokenKind.EqualsGreaterThanToken
                        || this.At TokenKind.OpenParenToken
                        || this.At TokenKind.LessThanToken
                    then
                        items.Add typeNode

                        if explicitInterface >= 0 then
                            items.Add explicitInterface

                        items.Add nameToken

                        this.TypeParameters items

                        if this.At TokenKind.OpenParenToken then
                            items.Add(this.Parameters(false))
                            this.Constraints items
                            this.Body items
                            this.Make(NodeKind.MethodDeclaration, start, items)
                        elif indexer then
                            items.Add(this.Parameters(true))

                            if this.At TokenKind.OpenBraceToken then
                                items.Add(this.Accessors())
                            else
                                this.Body items

                            this.Make(NodeKind.IndexerDeclaration, start, items)
                        else
                            fieldContext <- not event

                            if this.At TokenKind.OpenBraceToken then
                                items.Add(this.Accessors())

                                if this.At TokenKind.EqualsToken then
                                    fieldContext <- false
                                    items.Add(this.Initializer())
                                    this.Expect(items, TokenKind.SemicolonToken)
                            else
                                this.Body items

                            this.Make(
                                (if event then
                                     NodeKind.EventDeclaration
                                 else
                                     NodeKind.PropertyDeclaration),
                                start,
                                items
                            )
                    else
                        let name = children ()
                        name.Add nameToken

                        if this.At TokenKind.OpenBracketToken then
                            name.Add(this.FixedSize())

                        if this.At TokenKind.EqualsToken then
                            name.Add(this.Initializer())

                        let firstVariable = this.Make(NodeKind.VariableDeclarator, nameStart, name)
                        let variables = children ()
                        variables.Add typeNode
                        variables.Add firstVariable

                        while this.At TokenKind.CommaToken do
                            this.Take variables
                            variables.Add(this.Variable(this.Start, children ()))

                        items.Add(this.Make(NodeKind.VariableDeclaration, typeStart, variables))
                        this.Expect(items, TokenKind.SemicolonToken)

                        this.Make(
                            (if event then
                                 NodeKind.EventFieldDeclaration
                             else
                                 NodeKind.FieldDeclaration),
                            start,
                            items
                        )

    member private this.IsTypeDeclaration() =
        match this.Kind with
        | TokenKind.ClassKeyword
        | TokenKind.StructKeyword
        | TokenKind.InterfaceKeyword
        | TokenKind.EnumKeyword -> true
        | TokenKind.DelegateKeyword -> this.Next <> TokenKind.AsteriskToken
        | _ ->
            this.Word(0, "record")
            || (this.Word(0, "union") && this.Next = TokenKind.IdentifierToken)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TypeDeclaration(start: int, items: ChildList) : int =
        let kind =
            match this.Kind with
            | TokenKind.ClassKeyword -> NodeKind.ClassDeclaration
            | TokenKind.StructKeyword -> NodeKind.StructDeclaration
            | TokenKind.InterfaceKeyword -> NodeKind.InterfaceDeclaration
            | TokenKind.EnumKeyword -> NodeKind.EnumDeclaration
            | TokenKind.DelegateKeyword -> NodeKind.DelegateDeclaration
            | _ when this.Word(0, "union") -> NodeKind.UnionDeclaration
            | _ when this.Next = TokenKind.StructKeyword -> NodeKind.RecordStructDeclaration
            | _ -> NodeKind.RecordDeclaration

        if this.Word(0, "record") then
            this.Take(items, TokenKind.RecordKeyword)
        elif this.Word(0, "union") then
            this.Take(items, TokenKind.UnionKeyword)
        else
            this.Take items

        if kind = NodeKind.RecordDeclaration || kind = NodeKind.RecordStructDeclaration then
            if this.At TokenKind.ClassKeyword || this.At TokenKind.StructKeyword then
                this.Take items

        if kind = NodeKind.DelegateDeclaration then
            items.Add(this.Type())

        this.Expect(items, TokenKind.IdentifierToken)
        this.TypeParameters items

        if this.At TokenKind.OpenParenToken then
            items.Add(this.Parameters(false, (kind = NodeKind.UnionDeclaration)))

        if this.At TokenKind.ColonToken then
            let baseStart, bases = this.Start, children ()
            this.Take bases
            let mutable more = true

            while more && not (this.At TokenKind.EndOfFileToken) do
                let before, entryStart, entry = position, this.Start, children ()
                entry.Add(this.Type())
                let primary = this.At TokenKind.OpenParenToken

                if primary then
                    entry.Add(this.Arguments(false))

                bases.Add(
                    this.Make(
                        (if primary then
                             NodeKind.PrimaryConstructorBaseType
                         else
                             NodeKind.SimpleBaseType),
                        entryStart,
                        entry
                    )
                )

                if this.At TokenKind.CommaToken then
                    this.Take bases
                else
                    more <- false

                if position = before then
                    more <- false

            items.Add(this.Make(NodeKind.BaseList, baseStart, bases))

        this.Constraints items

        if kind = NodeKind.DelegateDeclaration then
            this.Expect(items, TokenKind.SemicolonToken)
        elif this.At TokenKind.SemicolonToken then
            this.Take items
        else
            this.Expect(items, TokenKind.OpenBraceToken)

            while not (this.At TokenKind.CloseBraceToken)
                  && not (this.At TokenKind.EndOfFileToken) do
                let before = position

                if kind = NodeKind.EnumDeclaration then
                    let enumStart, memberItems = this.Start, children ()
                    this.Attributes memberItems
                    this.Expect(memberItems, TokenKind.IdentifierToken)

                    if this.At TokenKind.EqualsToken then
                        memberItems.Add(this.Initializer())

                    items.Add(this.Make(NodeKind.EnumMemberDeclaration, enumStart, memberItems))

                    if this.At TokenKind.CommaToken then
                        this.Take items
                else
                    items.Add(this.Member())

                if position = before then
                    this.Skip items

            this.Expect(items, TokenKind.CloseBraceToken)

            if this.At TokenKind.SemicolonToken then
                this.Take items

        this.Make(kind, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.Using() : int =
        let start, items = this.Start, children ()

        if this.Word(0, "global") then
            this.Take(items, TokenKind.GlobalKeyword)

        this.Expect(items, TokenKind.UsingKeyword)

        if this.At TokenKind.StaticKeyword then
            this.Take items

        if this.At TokenKind.UnsafeKeyword then
            this.Take items

        if this.At TokenKind.IdentifierToken && this.Next = TokenKind.EqualsToken then
            let aliasStart, alias = this.Start, children ()
            alias.Add(this.Single NodeKind.IdentifierName)
            this.Take alias
            items.Add(this.Make(NodeKind.NameEquals, aliasStart, alias))

        items.Add(this.Type())
        this.Expect(items, TokenKind.SemicolonToken)
        this.Make(NodeKind.UsingDirective, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ExternAlias() : int =
        let start, items = this.Start, children ()
        this.Take items

        if this.Word(0, "alias") then
            this.Take(items, TokenKind.AliasKeyword)
        else
            this.Expect(items, TokenKind.AliasKeyword)

        this.Expect(items, TokenKind.IdentifierToken)
        this.Expect(items, TokenKind.SemicolonToken)
        this.Make(NodeKind.ExternAliasDirective, start, items)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.AttributedNamespace() =
        this.At TokenKind.OpenBracketToken
        && (let struct (afterAttributes, _) = this.DeclarationPrefix()
            input.KindAt afterAttributes = TokenKind.NamespaceKeyword)

    member private this.Namespace() : int =
        let start, items = this.Start, children ()

        if this.At TokenKind.OpenBracketToken then
            let previousAsync, previousField = asyncContext, fieldContext
            asyncContext <- false
            fieldContext <- false

            try
                this.Attributes items
            finally
                asyncContext <- previousAsync
                fieldContext <- previousField

        this.Take items
        items.Add(this.Name())
        let fileScoped = this.At TokenKind.SemicolonToken

        if fileScoped then
            this.Take items
        else
            this.Expect(items, TokenKind.OpenBraceToken)

        this.Declarations(items, not fileScoped, false)

        if not fileScoped then
            this.Expect(items, TokenKind.CloseBraceToken)

            if this.At TokenKind.SemicolonToken then
                this.Take items

        this.Make(
            (if fileScoped then
                 NodeKind.FileScopedNamespaceDeclaration
             else
                 NodeKind.NamespaceDeclaration),
            start,
            items
        )

    member private _.DottedNameBeforeDirectiveEnd(start: int) =
        let mutable cursor = start

        if input.KindAt cursor = TokenKind.IdentifierToken then
            cursor <- cursor + 1

            while input.KindAt cursor = TokenKind.DotToken
                  && input.KindAt(cursor + 1) = TokenKind.IdentifierToken do
                cursor <- cursor + 2

            match input.KindAt cursor with
            | TokenKind.SemicolonToken
            | TokenKind.EqualsToken -> cursor < input.Count
            | _ -> false
        else
            false

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IsUsingDirective() =
        if this.Word(0, "global") then
            true
        elif this.Next = TokenKind.OpenParenToken then
            false
        elif this.DottedNameBeforeDirectiveEnd(position + 1) then
            true
        else
            let struct (valid, after, offset, _) =
                ExpressionSyntax.scan input (position + 1) false

            not (
                valid
                && offset = 0
                && after < input.Count
                && input[after].Kind = TokenKind.IdentifierToken
            )

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IsNamespaceMember() =
        let struct (_, cursor) = this.DeclarationPrefix()

        match this.Peek(cursor - position) with
        | TokenKind.ClassKeyword
        | TokenKind.StructKeyword
        | TokenKind.InterfaceKeyword
        | TokenKind.EnumKeyword -> true
        | TokenKind.DelegateKeyword ->
            match this.Peek(cursor - position + 1) with
            | TokenKind.OpenBraceToken -> false
            | TokenKind.OpenParenToken ->
                let struct (valid, after, offset, _) =
                    ExpressionSyntax.scan input (cursor + 1) false

                valid
                && offset = 0
                && after > cursor + 1
                && after < input.Count
                && input[after].Kind = TokenKind.IdentifierToken
                && input[after - 1].Kind = TokenKind.CloseParenToken
            | _ -> true
        | TokenKind.RefKeyword -> this.RefStructModifier()
        | _ ->
            (this.Word(cursor - position, "record")
             && (this.Peek(cursor - position + 1) = TokenKind.IdentifierToken
                 || this.Peek(cursor - position + 1) = TokenKind.ClassKeyword
                 || this.Peek(cursor - position + 1) = TokenKind.StructKeyword))
            || (this.Word(cursor - position, "union")
                && this.Peek(cursor - position + 1) = TokenKind.IdentifierToken)

    member private this.Declarations(items: ChildList, stopAtBrace: bool, globals: bool) =
        ensureStack ()

        while not (this.At TokenKind.EndOfFileToken)
              && not (stopAtBrace && this.At TokenKind.CloseBraceToken) do
            let before = position

            if
                (this.At TokenKind.UsingKeyword && (not globals || this.IsUsingDirective()))
                || (this.Word(0, "global") && this.Next = TokenKind.UsingKeyword)
            then
                items.Add(this.Using())
            elif this.At TokenKind.ExternKeyword && this.Word(1, "alias") then
                items.Add(this.ExternAlias())
            elif this.At TokenKind.NamespaceKeyword then
                items.Add(this.Namespace())
            elif
                this.At TokenKind.OpenBracketToken
                && (this.Word(1, "assembly") || this.Word(1, "module"))
                && this.Peek(2) = TokenKind.ColonToken
            then
                this.Attribute items
            elif globals && this.AttributedNamespace() then
                items.Add(this.Namespace())
            elif not globals || this.IsNamespaceMember() then
                items.Add(this.Member())
            else
                let start, statement = this.Start, children ()
                statement.Add(this.Statement())
                items.Add(this.Make(NodeKind.GlobalStatement, start, statement))

            if position = before then
                this.Skip items

    member this.Parse(newSource: string, newTree: SyntaxTree) =
        source <- newSource
        tree <- newTree
        input <- newTree.InputTokens
        expressionEnds <- newTree.ExpressionEnds
        stackFloor <- StackGuard.entry ()

        try
            this.PrepareInput()

            asyncContext <- false
            fieldContext <- false
            queryContext <- false
            whenKeyword <- true
            forceConditionalAccess <- false
            speculative <- false
            contextualHint <- 0
            parameterHint <- 0
            parametersFound <- 0
            localBalanceWork <- 0
            globalDiscovery <- false
            discoveryIndex <- 0
            lambdaDelimitersComplete <- false
            tupleSpineDepths <- null

            let walkMark = ParseStats.enter ()
            tree.PrepareForParse input.Count

            let root =
                tree.AddNode
                    {
                        Kind = NodeKind.CompilationUnit
                        Parent = -1
                        ChildStart = 0
                        ChildCount = 0
                        TokenStart = 0
                        TokenCount = 0
                    }

            if input.Count > 0 then
                this.MoveTo 0
                discoveryOffset <- input[0].Start
                let items = children ()
                asyncContext <- true
                this.Declarations(items, false, true)
                this.Take items
                let childStart = tree.ChildCount
                let childCount = items.Count
                tree.AppendChildren(items, root) |> ignore

                tree.SetNode(
                    root,
                    { tree.Node root with
                        ChildStart = childStart
                        ChildCount = childCount
                        TokenCount = tree.TokenCount
                    }
                )
            else
                discoveryOffset <- 0

            ParseStats.lapse ParseStats.tDeclarations walkMark
        finally
            source <- ""
            tree <- Unchecked.defaultof<_>
            input <- Unchecked.defaultof<_>
            expressionEnds <- null
            tupleSpineDepths <- null
            DeclarationParser.cached <- this

module Parser =
    let internal parseLexed (source: string) (tree: SyntaxTree) : unit =
        tree.ResetParsed()

        if tree.LexerBuffer.IsVerifyOnly then
            let tokHint = tree.LexerBuffer.TokenCount + 32
            let trivHint = (tree.LexerBuffer.TokenCount <<< 1) + 64
            Lexer.lexHinted tokHint trivHint source tree.LexerBuffer
        elif tree.LexerBuffer.TokenCount = 0 then
            Lexer.lex source tree.LexerBuffer

        let mark = ParseStats.enter ()
        tree.CopyLexicalTrivia()
        let parser = DeclarationParser.Acquire()
        parser.Parse(source, tree)
        ParseStats.lapse ParseStats.tParse mark

        if ParseStats.enabled then
            ParseStats.event ParseStats.nParses
            ParseStats.bump ParseStats.nNodesKept tree.NodeCount
            ParseStats.bump ParseStats.nChildrenKept tree.ChildCount
            ParseStats.bump ParseStats.nTokensKept tree.TokenCount
            let struct (arenaLists, arenaEntries) = tree.ArenaCounts
            ParseStats.bump ParseStats.nArenaListsKept arenaLists
            ParseStats.bump ParseStats.nArenaEntriesKept arenaEntries

    let private parseCore (symbols: string array) (source: string) (tree: SyntaxTree) : unit =
        tree.Reset()

        try
            if isNull symbols then
                Lexer.lex source tree.LexerBuffer
            else
                Lexer.lexWith symbols source tree.LexerBuffer

            parseLexed source tree
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let parse (source: string) (tree: SyntaxTree) : unit = parseCore null source tree

    let lexOnly (source: string) (tree: SyntaxTree) : unit =
        tree.Reset()

        try
            Lexer.lex source tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let lexOnlyHinted
        (tokenHint: int)
        (triviaHint: int)
        (source: string)
        (tree: SyntaxTree)
        : unit =
        tree.Reset()

        try
            Lexer.lexHinted tokenHint triviaHint source tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let lexOnlyHintedSpan
        (tokenHint: int)
        (triviaHint: int)
        (source: ReadOnlySpan<char>)
        (tree: SyntaxTree)
        : unit =
        tree.Reset()

        try
            Lexer.lexHintedSpan tokenHint triviaHint source tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let lexOnlyVerifySpan
        (tokenHint: int)
        (triviaHint: int)
        (source: ReadOnlySpan<char>)
        (tree: SyntaxTree)
        : unit =
        tree.Reset()

        try
            Lexer.lexVerifySpan tokenHint triviaHint source tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let lexUnlessGenerated (source: string) (tree: SyntaxTree) : bool =
        tree.Reset()

        try
            Lexer.lexUnlessGenerated source tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let lexOnlyWith (symbols: string array) (source: string) (tree: SyntaxTree) : unit =
        tree.Reset()

        try
            Lexer.lexWith symbols source tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let lexOnlyWithHinted
        (symbols: string array)
        (tokenHint: int)
        (triviaHint: int)
        (source: string)
        (tree: SyntaxTree)
        : unit =
        tree.Reset()

        try
            Lexer.lexWithHinted symbols tokenHint triviaHint source tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let internal lexOnlySeededFromDefault
        (symbols: string array)
        (source: string)
        (defaultBuf: TokenBuffer)
        (win: inref<ConditionalLexWindow>)
        (tree: SyntaxTree)
        : struct (int * int * int * int) =
        tree.Reset()

        try
            Lexer.lexSeededFromDefault symbols source defaultBuf &win tree.LexerBuffer
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let parseFromLexed (source: string) (tree: SyntaxTree) : unit =
        try
            parseLexed source tree
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )

    let parseWith (symbols: string array) (source: string) (tree: SyntaxTree) : unit =
        parseCore symbols source tree

    let parseWithHinted
        (symbols: string array)
        (tokenHint: int)
        (triviaHint: int)
        (source: string)
        (tree: SyntaxTree)
        : unit =
        tree.Reset()

        try
            if isNull symbols || symbols.Length = 0 then
                Lexer.lexHinted tokenHint triviaHint source tree.LexerBuffer
            else
                Lexer.lexWithHinted symbols tokenHint triviaHint source tree.LexerBuffer

            parseLexed source tree
        with :? InsufficientExecutionStackException as error ->
            raise (
                InsufficientExecutionStackException(
                    "C# syntax nested too deeply to parse on this thread's stack.",
                    error
                )
            )
