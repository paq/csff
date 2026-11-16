namespace Csff.Printer

open System
open System.Buffers
open System.Globalization
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open Csff.Lexer
open Csff.Parser

module internal SyntaxFacts =
    let complete (tree: SyntaxTree) = tree.IsComplete

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let lineTerminator (ch: char) =
        ch = '\r' || ch = '\n' || ch = '\u0085' || ch = '\u2028' || ch = '\u2029'

    let lineTerminators = SearchValues.Create("\r\n\u0085\u2028\u2029".AsSpan())

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let spansLines (text: ReadOnlySpan<char>) = text.IndexOfAny(lineTerminators) >= 0

    let private suffixed (text: ReadOnlySpan<char>) (length: int) =
        text.Length = length
        || (text.Length > length + 3 && text.Slice(length).StartsWith(" - ".AsSpan()))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let ignoreMarker (text: ReadOnlySpan<char>) =
        if text.Length < 14 || text[2] <> ' ' || text[3] <> 'c' then
            0
        elif text.StartsWith("// csff-ignore-start".AsSpan()) && suffixed text 20 then
            2
        elif text.StartsWith("// csff-ignore-end".AsSpan()) && suffixed text 18 then
            3
        elif text.StartsWith("// csff-ignore".AsSpan()) && suffixed text 14 then
            1
        else
            0

    let warningCommentCloser (text: ReadOnlySpan<char>) =
        let text = text.TrimEnd()
        let last = text.Slice(text.LastIndexOfAny('\r', '\n') + 1).TrimStart()

        last.StartsWith("#warning".AsSpan(), StringComparison.Ordinal)
        && last.Length > 8
        && Char.IsWhiteSpace last[8]
        && last.EndsWith("*/".AsSpan(), StringComparison.Ordinal)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let binary kind =
        (kind >= NodeKind.AddExpression && kind <= NodeKind.CoalesceExpression)
        || kind = NodeKind.UnsignedRightShiftExpression

    let private fallthrough: byte array = Array.zeroCreate 16384

    [<Literal>]
    let FallsToAll = 1uy

    [<Literal>]
    let FallsToBinary = 2uy

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let fallthroughOf (kind: NodeKind) =
        let index = int kind

        if uint index < uint fallthrough.Length then
            fallthrough[index]
        else
            0uy

    let learnFallthrough (kind: NodeKind) (outcome: byte) =
        let index = int kind

        if uint index < uint fallthrough.Length then
            fallthrough[index] <- outcome

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let assignment kind =
        kind >= NodeKind.SimpleAssignmentExpression
        && kind <= NodeKind.UnsignedRightShiftAssignmentExpression

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let postfix kind =
        kind = NodeKind.PostIncrementExpression
        || kind = NodeKind.PostDecrementExpression
        || kind = NodeKind.SuppressNullableWarningExpression

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let memberAccess kind =
        kind = NodeKind.SimpleMemberAccessExpression
        || kind = NodeKind.PointerMemberAccessExpression

    let initializer kind =
        kind = NodeKind.ObjectInitializerExpression
        || kind = NodeKind.CollectionInitializerExpression
        || kind = NodeKind.ArrayInitializerExpression
        || kind = NodeKind.ComplexElementInitializerExpression
        || kind = NodeKind.WithInitializerExpression

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let lambda kind =
        kind = NodeKind.SimpleLambdaExpression
        || kind = NodeKind.ParenthesizedLambdaExpression

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let literal kind =
        kind >= NodeKind.NumericLiteralExpression
        && kind <= NodeKind.Utf8StringLiteralExpression

    let expression kind =
        (kind >= NodeKind.ParenthesizedExpression
         && kind <= NodeKind.ImplicitObjectCreationExpression)
        || binary kind
        || assignment kind
        || memberAccess kind
        || (kind >= NodeKind.UnaryPlusExpression && kind <= NodeKind.IndexExpression)
        || (kind >= NodeKind.ThisExpression && kind <= NodeKind.FieldExpression)
        || (kind >= NodeKind.TypeOfExpression && kind <= NodeKind.UnsafeExpression)
        || kind = NodeKind.ConditionalAccessExpression
        || kind = NodeKind.SwitchExpression
        || kind = NodeKind.DeclarationExpression
        || kind = NodeKind.RefExpression
        || kind = NodeKind.ThrowExpression
        || kind = NodeKind.ImplicitStackAllocArrayCreationExpression
        || kind = NodeKind.SuppressNullableWarningExpression
        || kind = NodeKind.WithExpression
        || kind = NodeKind.CollectionExpression
        || kind = NodeKind.TupleExpression

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let comment kind =
        kind >= TriviaKind.SingleLineCommentTrivia
        && kind <= TriviaKind.MultiLineDocumentationCommentTrivia
        && kind <> TriviaKind.DocumentationCommentExteriorTrivia

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let directive kind =
        kind >= TriviaKind.IfDirectiveTrivia
        && (kind <= TriviaKind.BadDirectiveTrivia
            || kind = TriviaKind.ShebangDirectiveTrivia
            || kind = TriviaKind.LoadDirectiveTrivia
            || kind = TriviaKind.NullableDirectiveTrivia
            || kind = TriviaKind.LineSpanDirectiveTrivia
            || kind = TriviaKind.IgnoredDirectiveTrivia)

    let conditionalDirective kind (text: ReadOnlySpan<char>) =
        if
            kind = TriviaKind.IfDirectiveTrivia
            || kind = TriviaKind.ElifDirectiveTrivia
            || kind = TriviaKind.ElseDirectiveTrivia
            || kind = TriviaKind.EndIfDirectiveTrivia
        then
            true
        elif kind = TriviaKind.BadDirectiveTrivia then
            let text = text.TrimStart()

            if text.Length = 0 || text[0] <> '#' then
                false
            else
                let word = text.Slice(1).TrimStart()
                let mutable length = 0

                while length < word.Length && Char.IsLetter word[length] do
                    length <- length + 1

                let word = word.Slice(0, length)

                word.SequenceEqual("if".AsSpan())
                || word.SequenceEqual("elif".AsSpan())
                || word.SequenceEqual("else".AsSpan())
                || word.SequenceEqual("endif".AsSpan())
        else
            false

    let precedence kind =
        match kind with
        | TokenKind.QuestionQuestionToken -> 1
        | TokenKind.BarBarToken -> 2
        | TokenKind.AmpersandAmpersandToken -> 3
        | TokenKind.BarToken -> 4
        | TokenKind.CaretToken -> 5
        | TokenKind.AmpersandToken -> 6
        | TokenKind.ExclamationEqualsToken -> 7
        | TokenKind.EqualsEqualsToken -> 8
        | TokenKind.LessThanToken
        | TokenKind.LessThanEqualsToken
        | TokenKind.GreaterThanToken
        | TokenKind.GreaterThanEqualsToken
        | TokenKind.IsKeyword
        | TokenKind.AsKeyword -> 9
        | TokenKind.LessThanLessThanToken
        | TokenKind.GreaterThanGreaterThanToken
        | TokenKind.GreaterThanGreaterThanGreaterThanToken -> 10
        | TokenKind.PlusToken
        | TokenKind.MinusToken -> 11
        | TokenKind.AsteriskToken
        | TokenKind.SlashToken
        | TokenKind.PercentToken -> 12
        | _ -> -1

    let stringToken kind =
        kind = TokenKind.StringLiteralToken
        || kind = TokenKind.Utf8StringLiteralToken
        || kind = TokenKind.InterpolatedStringToken
        || kind = TokenKind.SingleLineRawStringLiteralToken
        || kind = TokenKind.MultiLineRawStringLiteralToken
        || kind = TokenKind.Utf8SingleLineRawStringLiteralToken
        || kind = TokenKind.Utf8MultiLineRawStringLiteralToken

    let closedSingleLineStringCore
        (allowInterpolated: bool)
        (source: string)
        (limit: int)
        (token: Token)
        =
        if
            token.Kind <> TokenKind.StringLiteralToken
            && token.Kind <> TokenKind.Utf8StringLiteralToken
            && token.Kind <> TokenKind.SingleLineRawStringLiteralToken
            && token.Kind <> TokenKind.Utf8SingleLineRawStringLiteralToken
            && (not allowInterpolated || token.Kind <> TokenKind.InterpolatedStringToken)
        then
            false
        else
            let span = source.AsSpan(token.Start, token.Length)

            if span.IndexOfAny('\r', '\n') >= 0 then
                false
            elif token.Kind = TokenKind.InterpolatedStringToken then
                if
                    span.Contains('#')
                    || (span.Contains('/')
                        && (span.Contains("/*".AsSpan(), StringComparison.Ordinal)
                            || span.Contains("//".AsSpan(), StringComparison.Ordinal)))
                    || token.End >= limit
                    || span.Length < 3
                    || span[span.Length - 1] <> '"'
                then
                    false
                elif span[0] = '@' || span[1] = '@' then
                    true
                else
                    let mutable backslashes = 0

                    while span.Length - 2 - backslashes >= 1
                          && span[span.Length - 2 - backslashes] = '\\' do
                        backslashes <- backslashes + 1

                    backslashes % 2 = 0
            else
                let finish =
                    if
                        token.Kind = TokenKind.Utf8StringLiteralToken
                        || token.Kind = TokenKind.Utf8SingleLineRawStringLiteralToken
                    then
                        span.Length - 2
                    else
                        span.Length

                if span.Length >= 2 && span[0] = '"' && finish >= 2 && span[finish - 1] = '"' then
                    if
                        token.Kind = TokenKind.SingleLineRawStringLiteralToken
                        || token.Kind = TokenKind.Utf8SingleLineRawStringLiteralToken
                    then
                        token.End < limit && source[token.End] <> '\r' && source[token.End] <> '\n'
                    else
                        let mutable backslashes = 0

                        while finish - 2 - backslashes >= 1 && span[finish - 2 - backslashes] = '\\' do
                            backslashes <- backslashes + 1

                        backslashes % 2 = 0
                elif
                    finish >= 3
                    && span[0] = '@'
                    && span[1] = '"'
                    && span[finish - 1] = '"'
                    && token.End < limit
                then
                    true
                else
                    false

    let closedSingleLineString (source: string) (limit: int) (token: Token) =
        closedSingleLineStringCore false source limit token

    let literalOwnershipNeededCore
        (allowInterpolated: bool)
        (source: string)
        (tree: SyntaxTree)
        (initialComplete: bool)
        (independent: bool)
        (discovery: bool)
        (scratch: TokenBuffer voption)
        =
        if not (source.Contains '"') || independent then
            false
        elif
            discovery
            || not initialComplete
            || source.Contains("csff-ignore", StringComparison.Ordinal)
            || source.AsSpan().IndexOfAny('\u0085', '\u2028', '\u2029') >= 0
        then
            true
        else
            let buffer = tree.LexerBuffer
            let mutable tokens = scratch
            let mutable needed = false
            let mutable i = 0

            while not needed && i < buffer.TokenCount do
                let token = buffer.Token i

                if
                    stringToken token.Kind
                    && not (closedSingleLineStringCore allowInterpolated source source.Length token)
                then
                    needed <- true

                i <- i + 1

            i <- 0

            while not needed && i < tree.TriviaCount do
                let item = tree.Trivia i

                match item.Kind with
                | kind when i >= buffer.TriviaCount && kind <> TriviaKind.WhitespaceTrivia ->
                    needed <- true
                | TriviaKind.SkippedTokensTrivia -> needed <- true
                | TriviaKind.MultiLineCommentTrivia
                | TriviaKind.MultiLineDocumentationCommentTrivia ->
                    let finish = item.Start + item.Length
                    let span = source.AsSpan(item.Start, item.Length)

                    if
                        (not allowInterpolated || span.Contains('#')) && span.Contains('"')
                        || finish >= source.Length
                        || not (span.EndsWith("*/".AsSpan(), StringComparison.Ordinal))
                    then
                        needed <- true
                | TriviaKind.DisabledTextTrivia ->
                    let finish = item.Start + item.Length

                    if finish >= source.Length then
                        needed <- true
                    elif source.AsSpan(item.Start, item.Length).Contains('"') then
                        let disabledBuffer =
                            match tokens with
                            | ValueSome existing -> existing
                            | ValueNone ->
                                let created = TokenBuffer()
                                tokens <- ValueSome created
                                created

                        Lexer.lexRange source item.Start finish disabledBuffer
                        let mutable j = 0

                        while not needed && j < disabledBuffer.TokenCount do
                            let token = disabledBuffer.Token j

                            if
                                stringToken token.Kind
                                && not (
                                    closedSingleLineStringCore allowInterpolated source finish token
                                )
                            then
                                needed <- true

                            j <- j + 1

                        j <- 0

                        while not needed && j < disabledBuffer.TriviaCount do
                            let nested = disabledBuffer.Trivia j

                            if
                                nested.Kind <> TriviaKind.WhitespaceTrivia
                                && nested.Kind <> TriviaKind.EndOfLineTrivia
                                && nested.Kind <> TriviaKind.SingleLineCommentTrivia
                                && nested.Kind <> TriviaKind.SingleLineDocumentationCommentTrivia
                            then
                                match nested.Kind with
                                | TriviaKind.MultiLineCommentTrivia
                                | TriviaKind.MultiLineDocumentationCommentTrivia ->
                                    let nestedFinish = nested.Start + nested.Length
                                    let span = source.AsSpan(nested.Start, nested.Length)

                                    if
                                        (not allowInterpolated || span.Contains('#'))
                                        && span.Contains('"')
                                        || nestedFinish >= finish
                                        || not (
                                            span.EndsWith("*/".AsSpan(), StringComparison.Ordinal)
                                        )
                                    then
                                        needed <- true
                                | TriviaKind.RegionDirectiveTrivia
                                | TriviaKind.EndRegionDirectiveTrivia
                                | TriviaKind.PragmaWarningDirectiveTrivia
                                | TriviaKind.PragmaChecksumDirectiveTrivia
                                | TriviaKind.NullableDirectiveTrivia
                                | TriviaKind.ErrorDirectiveTrivia
                                | TriviaKind.WarningDirectiveTrivia
                                | TriviaKind.LineDirectiveTrivia ->
                                    if source.AsSpan(nested.Start, nested.Length).Contains('"') then
                                        needed <- true
                                | _ -> needed <- true

                            j <- j + 1
                | _ -> ()

                i <- i + 1

            needed

    let literalOwnershipNeeded
        (source: string)
        (tree: SyntaxTree)
        (initialComplete: bool)
        (independent: bool)
        (discovery: bool)
        (scratch: TokenBuffer voption)
        =
        literalOwnershipNeededCore false source tree initialComplete independent discovery scratch

[<Struct>]
type internal ChainPart = { Node: int; Start: int; Count: int }

[<Struct; System.Runtime.CompilerServices.IsReadOnly; NoEquality; NoComparison>]
type internal ChainGroup =
    {
        Parts: ResizeArray<ChainPart>
        Start: int
        Count: int
    }

    member this.Item
        with get index = this.Parts[this.Start + index]

[<Sealed>]
type internal ChainScratch() =
    let document = new DocumentBuffer()
    let parts = ResizeArray<ChainPart>()
    let groups = ResizeArray<ChainGroup>()
    let emitted = ResizeArray<struct (int * int)>()
    member _.Document = document
    member _.Parts = parts
    member _.Groups = groups
    member _.Emitted = emitted

    interface IDisposable with
        member _.Dispose() = document.Dispose()

[<Sealed>]
type internal ConditionalFrame(opening: int, parent: int, depth: int) =
    let points = ResizeArray<int>()
    let requests = ResizeArray<int>()
    let ancestors = Array.zeroCreate<int> 31
    member _.Opening = opening
    member _.Parent = parent
    member _.Depth = depth
    member val OpeningIndex = -1 with get, set
    member val ContentStart = 0 with get, set
    member val Finish = Int32.MaxValue with get, set
    member val DirectScope = -1 with get, set
    member val BeforeOwner = 0 with get, set
    member val AfterOwner = 0 with get, set
    member val DirectiveOwner = 0 with get, set
    member _.Points = points
    member _.Requests = requests
    member _.Ancestors = ancestors

[<Struct>]
type internal ConditionalRequest =
    {
        Frame: int
        Scope: int
        Start: int
        Index: int
        Comment: bool
        CodeAfter: bool
    }

[<Struct; NoEquality; NoComparison>]
type internal UsingSortKey =
    {
        Node: int
        Ignored: bool
        Tail: bool
        Category: int
        SystemBucket: int
        Dotted: bool
        Nameless: int
        TextStart: int
        TextLength: int
        FallbackText: string
        InputIndex: int
    }

[<Sealed>]
type internal SyntaxNodePrinter
    (initialSource: string, initialTree: SyntaxTree, ?sharedTokens: TokenBuffer) =
    let mutable source = initialSource
    let mutable sourceIsAscii = Text.Ascii.IsValid(initialSource.AsSpan())
    let mutable tree = initialTree
    let mutable treeNodes = initialTree.NodeStorage
    let mutable treeChildren = initialTree.ChildStorage
    let mutable treeTokens = initialTree.TokenStorage
    let mutable treeTrivia = initialTree.TriviaStorage
    let mutable seen = Array.empty<bool>
    let heads = ResizeArray<int>()
    let mutable indexedHeads = false
    let mutable records = 0
    let stats = DocumentStats.enabled
    let mutable stackFloor = StackGuard.Unproven
    let mutable statNodes = 0
    let mutable statTriviaRuns = 0
    let mutable statTriviaEntered = 0
    let mutable queries = 0
    let mutable comparisons = 0
    let mutable lambdaVisits = 0
    let mutable memberProbes = 0L
    let mutable usingProbes = 0L
    let mutable namespaceProbes = 0L
    let mutable sortComparisons = 0L
    let mutable sortedUsings = false
    let mutable sortedModifiers = false
    let mutable changedTrailingCommas = false
    let mutable reindentedRawStrings = false
    let mutable depthCursorToken = -1
    let mutable depthAtCursor = 0
    let mutable depthAfterCursor = 0
    let mutable brokenIndentChars = 0L
    let mutable brokenIndentDepth = 0
    let mutable maxOutputLength = Array.MaxLength
    let mutable maxLineLength = 200
    let mutable unitIndent = 1
    let mutable ignoreUntil = -1
    let ignoredRanges = ResizeArray<struct (int * int)>()
    let ignoredSingles = Collections.Generic.HashSet<int>()
    let importEnds = Dictionary<int, int>()
    let mutable scannedDirectives = Array.empty<int>
    let mutable scannedDirectiveCount = 0
    let mutable pendingDirectiveSymbols = ValueNone
    let mutable recoveringConditionals = false
    let mutable disabledTree = ValueNone
    let mutable closedConditionals = HashSet<int>()
    let alternateConditionals = HashSet<int>()
    let markedConditionals = HashSet<int>()
    let followingIgnoreComments = HashSet<int>()
    let alternateBranchComments = HashSet<int>()
    let conditionalIgnoreStarts = HashSet<int>()
    let rangeConditionals = HashSet<int>()
    let firstRangeConditionals = HashSet<int>()
    let nestedRangeConditionals = HashSet<int>()
    let unfinishedRangeConditionals = HashSet<int>()
    let ownedCommentScopes = Dictionary<int, HashSet<int>>()
    let ignoredDocPrefixes = HashSet<int>()
    let disabledFollowingSingles = HashSet<int>()
    let commentFragments = Dictionary<int, struct (bool * int)>()
    let mutable conditionalPrefixes = Dictionary<int, struct (int * bool)>()
    let conditionalStack = ResizeArray<struct (int * int * int)>(16)
    let mutable emptyConditionalPrefixes = Array.empty<bool>
    let mutable tokenScopes = Array.empty<int>
    let followingSingles = Dictionary<int, ResizeArray<int>>()
    let scopeExits = Dictionary<int, ResizeArray<int>>()
    let commentConditionals = HashSet<int>()
    let bodyMarkedConditionals = HashSet<int>()
    let followingConditionalPrefixes = HashSet<int>()
    let nestedFirstRanges = HashSet<int>()
    let unfinishedFollowingPrefixes = HashSet<int>()
    let followedSingleClosings = HashSet<int>()
    let mutable recoveredWitness = false
    let mutable indexedConditionals = false
    let mutable indexedIgnores = false
    let mutable hasConditionals = false
    let mutable hasComplexConditionals = false
    let mutable hasIgnores = false
    let mutable hasConditionalStructure = false
    let mutable hasComments = false
    let mutable hasDirectives = false
    let mutable headerDirectiveAlwaysFits = false
    let mutable firstDirectiveTrivia = Int32.MaxValue
    let mutable lastDirectiveTrivia = -1
    let mutable cascadeKind = NodeKind.None
    let mutable indexedMultilineTokens = false
    let mutable firstMultilineToken = Int32.MaxValue
    let mutable lastMultilineToken = -1
    let mutable literalOwned = Array.empty<bool>
    let mutable literalLines = Array.empty<bool>
    let mutable literalInteriors = Array.empty<bool>
    let mutable literalBoundaries = Array.empty<int>
    let mutable literalLength = 0
    let mutable literalHasUnclosed = false
    let mutable remapOwned = Array.empty<bool>
    let mutable remapInteriors = Array.empty<bool>
    let mutable remapBoundaries = Array.empty<int>
    let mutable initializedCreations = Array.empty<byte>
    let initScanStack = ResizeArray<struct (int * int)>(16)
    let mutable indexedLiteralLines = false

    static let growCleared (arr: 'T[] byref) (clearLength: int) (minCapacity: int) =
        if arr.Length < minCapacity then
            let maxPooled = PoolArray.maxPooledLength

            let step =
                if arr.Length >= 65536 then
                    arr.Length + (arr.Length >>> 2)
                else
                    max 1024 (arr.Length * 2)

            let target =
                if minCapacity > maxPooled then
                    minCapacity
                else
                    max minCapacity step

            if arr.Length > 0 && arr.Length <= maxPooled then
                SharedBuckets<'T>.Return arr

            arr <-
                if target <= maxPooled then
                    SharedBuckets<'T>.Rent target
                else
                    GC.AllocateUninitializedArray<'T> target

        if clearLength > 0 then
            Array.Clear(arr, 0, clearLength)

    static let releasePooled (arr: 'T[] byref) =
        if arr.Length > 0 && arr.Length <= PoolArray.maxPooledLength then
            SharedBuckets<'T>.Return arr

        arr <- Array.empty

    let chainParts = ResizeArray<int>(64)
    let chainSpans = ResizeArray<struct (int * int * bool * bool)>(32)
    let flatPrefixElements = ResizeArray<int>(32)
    let delimitedRanges = ResizeArray<struct (int * int)>(16)
    let usingNodes = ResizeArray<int>(32)
    let usingMasked = ResizeArray<int>(16)
    let usingBlanks = ResizeArray<int>(16)
    let usingReplays = ResizeArray<struct (int * int * int * int)>(8)
    let usingEndings = ResizeArray<struct (int * int * int * bool)>(8)
    let literalUsingEnds = HashSet<int>()
    let mutable usingEndingsJoin = -1
    let mutable usingRelBefore = Array.empty<int>
    let mutable usingRelAfter = Array.empty<int>
    let mutable usingKeys = Array.empty<UsingSortKey>
    let mutable modifierBuffer = Array.zeroCreate<int> 8
    let mutable literalConfigurations = ValueNone
    let configuredSymbols = HashSet<string>(StringComparer.Ordinal)
    let mutable configuredSymbolsReady = false
    let mutable preserveForeignCode = false

    let mutable closingPositions =
        Collections.Generic.Dictionary<int, struct (int * int)>()

    let mutable siblingSpans =
        Collections.Generic.Dictionary<int, struct (int * int) array>()

    let mutable lastLambdaNode = -1
    let mutable lastLambdaBody = struct (0, 0, 0, 0)

    let mutable suppressBlank = -1
    let mutable blankSibling = -1
    let mutable callTypeArguments = -1
    let mutable flatSingleTypeArguments = false
    let mutable compactUsingTrivia = false
    let mutable replayedTrailingFrame = false
    let mutable triviaTokens = sharedTokens |> ValueOption.ofOption
    let mutable lastDeclinedLeadingToken = -1
    let mutable whitespaceOnly = false
    let mutable hoistedLeadingToken = -1
    let mutable disabledRun = struct (0, 0, Int32.MaxValue)

    member _.HeadTriviaWork = struct (records, queries, comparisons)
    member _.LambdaBodyVisits = lambdaVisits
    member _.MemberMetadataProbes = memberProbes
    member _.UsingTriviaProbes = usingProbes
    member _.NamespaceClassificationProbes = namespaceProbes
    member _.UsingSortComparisons = sortComparisons

    member _.SortedUsings = sortedUsings

    member _.SortedModifiers = sortedModifiers

    member _.WhitespaceOnly
        with get () = whitespaceOnly
        and set value =
            if value <> whitespaceOnly then
                indexedLiteralLines <- false
                literalLength <- 0
                literalHasUnclosed <- false

            whitespaceOnly <- value

    member _.ChangedTrailingCommas = changedTrailingCommas
    member _.ReindentedRawStrings = reindentedRawStrings

    member _.ClearWitness() =
        source <- ""
        sortedUsings <- false
        sortedModifiers <- false
        changedTrailingCommas <- false
        reindentedRawStrings <- false

    member this.Reset
        (
            nextSource: string,
            nextTree: SyntaxTree,
            ?directives: int array,
            ?directiveSymbols: string array voption,
            ?recovery: bool,
            ?recovered: bool,
            ?configurations: string array array,
            ?foreignCode: bool,
            ?ownership: struct (bool array * bool array * int array * int),
            ?knownAscii: bool
        ) =
        this.ResetCore(
            nextSource,
            nextTree,
            (directives |> ValueOption.ofOption),
            (defaultArg directiveSymbols ValueNone),
            (defaultArg recovery false),
            (defaultArg recovered false),
            (configurations |> ValueOption.ofOption),
            (defaultArg foreignCode false),
            (ownership |> ValueOption.ofOption),
            (knownAscii |> ValueOption.ofOption)
        )

    member internal this.ResetCore
        (
            nextSource: string,
            nextTree: SyntaxTree,
            directives: int array voption,
            directiveSymbols: string array voption,
            recovery: bool,
            recovered: bool,
            configurations: string array array voption,
            foreignCode: bool,
            ownership: struct (bool array * bool array * int array * int) voption,
            knownAscii: bool voption
        ) =
        let prevSource = source

        let sameOwnership =
            obj.ReferenceEquals(prevSource, nextSource)
            && match literalConfigurations, configurations with
               | ValueNone, ValueNone -> true
               | ValueSome a, ValueSome b -> obj.ReferenceEquals(a, b)
               | _ -> false

        match knownAscii with
        | ValueSome ascii -> sourceIsAscii <- ascii
        | ValueNone ->
            if not (obj.ReferenceEquals(prevSource, nextSource)) then
                sourceIsAscii <- Text.Ascii.IsValid(nextSource.AsSpan())

        source <- nextSource
        tree <- nextTree
        treeNodes <- nextTree.NodeStorage
        treeChildren <- nextTree.ChildStorage
        treeTokens <- nextTree.TokenStorage
        treeTrivia <- nextTree.TriviaStorage

        match directives with
        | ValueSome arr ->
            scannedDirectives <- arr
            scannedDirectiveCount <- arr.Length
            pendingDirectiveSymbols <- ValueNone
        | ValueNone ->
            scannedDirectiveCount <- 0
            pendingDirectiveSymbols <- directiveSymbols

        recoveringConditionals <- recovery
        recoveredWitness <- recovered
        literalConfigurations <- configurations
        configuredSymbolsReady <- false
        preserveForeignCode <- foreignCode

        growCleared &seen tree.TriviaCount tree.TriviaCount
        growCleared &initializedCreations tree.NodeCount tree.NodeCount

        if heads.Count > 0 then
            heads.Clear()

        indexedHeads <- false
        depthCursorToken <- -1
        depthAtCursor <- 0
        depthAfterCursor <- 0
        brokenIndentChars <- 0L
        brokenIndentDepth <- 0
        maxOutputLength <- Array.MaxLength
        records <- 0
        queries <- 0
        comparisons <- 0
        lambdaVisits <- 0
        memberProbes <- 0L
        usingProbes <- 0L
        namespaceProbes <- 0L
        sortComparisons <- 0L
        ignoreUntil <- -1
        usingEndingsJoin <- -1

        if hasIgnores then
            literalUsingEnds.Clear()
            ignoredRanges.Clear()
            ignoredSingles.Clear()
            importEnds.Clear()
            hasIgnores <- false

        if hasConditionals then
            if closedConditionals.Count > 0 then
                if closedConditionals.EnsureCapacity 0 > 16384 then
                    closedConditionals <- HashSet<int>()
                else
                    closedConditionals.Clear()

            if conditionalPrefixes.Count > 0 then
                if conditionalPrefixes.EnsureCapacity 0 > 16384 then
                    conditionalPrefixes <- Dictionary<int, struct (int * bool)>()
                else
                    conditionalPrefixes.Clear()

            hasConditionals <- false

        if hasComplexConditionals then
            alternateConditionals.Clear()
            markedConditionals.Clear()
            followingIgnoreComments.Clear()
            alternateBranchComments.Clear()
            conditionalIgnoreStarts.Clear()
            rangeConditionals.Clear()
            firstRangeConditionals.Clear()
            nestedRangeConditionals.Clear()
            unfinishedRangeConditionals.Clear()
            ownedCommentScopes.Clear()
            ignoredDocPrefixes.Clear()
            disabledFollowingSingles.Clear()
            commentFragments.Clear()
            followingSingles.Clear()
            scopeExits.Clear()
            commentConditionals.Clear()
            bodyMarkedConditionals.Clear()
            followingConditionalPrefixes.Clear()
            nestedFirstRanges.Clear()
            unfinishedFollowingPrefixes.Clear()
            followedSingleClosings.Clear()
            hasComplexConditionals <- false

        indexedConditionals <- false
        indexedIgnores <- false
        hasConditionalStructure <- false
        hasComments <- false
        hasDirectives <- false
        headerDirectiveAlwaysFits <- false
        firstDirectiveTrivia <- Int32.MaxValue
        lastDirectiveTrivia <- -1
        indexedMultilineTokens <- false
        firstMultilineToken <- Int32.MaxValue
        lastMultilineToken <- -1

        match ownership with
        | ValueSome(struct (_, _, _, len)) when len = 0 ->
            literalLength <- 0
            literalHasUnclosed <- false
            indexedLiteralLines <- true
        | ValueSome(struct (owned, interiors, boundaries, len)) ->
            let mutable unchanged = false

            if obj.ReferenceEquals(owned, remapOwned) then
                let prevOwned = literalOwned
                let prevInteriors = literalInteriors
                let prevBoundaries = literalBoundaries
                literalOwned <- remapOwned
                literalInteriors <- remapInteriors
                literalBoundaries <- remapBoundaries
                remapOwned <- prevOwned
                remapInteriors <- prevInteriors
                remapBoundaries <- prevBoundaries
            elif not (obj.ReferenceEquals(owned, literalOwned)) then
                growCleared &literalOwned 0 len
                growCleared &literalInteriors 0 len
                growCleared &literalBoundaries 0 (len + 1)

                Array.Copy(owned, 0, literalOwned, 0, len)
                Array.Copy(interiors, 0, literalInteriors, 0, len)
                Array.Copy(boundaries, 0, literalBoundaries, 0, len + 1)
            elif
                obj.ReferenceEquals(prevSource, nextSource)
                && indexedLiteralLines
                && literalLength = len
            then
                unchanged <- true

            literalLength <- len

            if not unchanged then
                this.ExpandLiteralLines()

            indexedLiteralLines <- true
        | ValueNone when sameOwnership -> ()
        | ValueNone ->
            literalLength <- 0
            literalHasUnclosed <- false
            indexedLiteralLines <- false

        if closingPositions.Count > 0 then
            if closingPositions.EnsureCapacity 0 > 16384 then
                closingPositions <- Collections.Generic.Dictionary<int, struct (int * int)>()
            else
                closingPositions.Clear()

        if siblingSpans.Count > 0 then
            if siblingSpans.EnsureCapacity 0 > 16384 then
                siblingSpans <- Collections.Generic.Dictionary<int, struct (int * int) array>()
            else
                siblingSpans.Clear()

        lastLambdaNode <- -1

        if chainParts.Count > 0 then
            chainParts.Clear()

        if chainSpans.Count > 0 then
            chainSpans.Clear()

        suppressBlank <- -1
        blankSibling <- -1
        callTypeArguments <- -1
        flatSingleTypeArguments <- false
        compactUsingTrivia <- false
        replayedTrailingFrame <- false
        lastDeclinedLeadingToken <- -1
        hoistedLeadingToken <- -1
        disabledRun <- struct (0, 0, Int32.MaxValue)

    member _.HeadHasTrivia(first: int, finish: int) : bool =
        queries <- queries + 1

        if not indexedHeads then
            let trivia = tree.TriviaSpan()

            for i = 0 to trivia.Length - 1 do
                records <- records + 1
                let item = &trivia[i]

                if SyntaxFacts.comment item.Kind || SyntaxFacts.directive item.Kind then
                    heads.Add item.Start

            heads.Sort()
            indexedHeads <- true

        let mutable lo = 0
        let mutable hi = heads.Count

        while lo < hi do
            comparisons <- comparisons + 1
            let mid = lo + (hi - lo) / 2
            if heads[mid] < first then lo <- mid + 1 else hi <- mid

        first < finish && lo < heads.Count && heads[lo] < finish

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.EnsureStack() =
        stackFloor <- StackGuard.proven stackFloor

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.Children(n: int) =
        let node = &treeNodes[n]
        IntSlice(treeChildren, node.ChildStart, node.ChildCount)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.Kind(n: int) =
        if n < 0 then NodeKind.None else treeNodes[n].Kind

    member private this.ControlStatement(n: int) =
        let mutable statement = n

        while this.Kind statement = NodeKind.GlobalStatement
              || this.Kind statement = NodeKind.LabeledStatement do
            let children = this.Children statement
            statement <- children[children.Length - 1]

        match this.Kind statement with
        | NodeKind.IfStatement
        | NodeKind.ForStatement
        | NodeKind.ForEachStatement
        | NodeKind.ForEachVariableStatement
        | NodeKind.WhileStatement
        | NodeKind.DoStatement
        | NodeKind.SwitchStatement
        | NodeKind.TryStatement
        | NodeKind.LockStatement
        | NodeKind.FixedStatement
        | NodeKind.UnsafeStatement -> true
        | _ -> false

    member private this.WithoutNullForgiving(n: int) =
        let mutable operand = n

        while this.Kind operand = NodeKind.SuppressNullableWarningExpression do
            let children = this.Children operand
            operand <- children[0]

        operand

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.Parent(n: int) = treeNodes[n].Parent

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.ChildCount(n: int) = treeNodes[n].ChildCount

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.TokenKind(n: int) =
        if n < 0 then treeTokens[-n - 1].Kind else TokenKind.None

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.First(n: int) =
        if n < 0 then -n - 1 else treeNodes[n].TokenStart

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.Last(n: int) =
        if n < 0 then
            -n - 1
        else
            let node = &treeNodes[n]
            node.TokenStart + node.TokenCount - 1

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.At(n: int, kind: TokenKind) = this.TokenKind n = kind

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.ContainsLessThan(n: int) =
        let first = this.First n
        let last = this.Last n

        if last <= first then
            false
        else
            let mutable found = false
            let mutable t = first

            while not found && t <= last do
                if treeTokens[t].Kind = TokenKind.LessThanToken then
                    found <- true

                t <- t + 1

            found

    member private this.HasChildOfKind(n: int, target: NodeKind) =
        let c = this.Children n
        let mutable found = false
        let mutable i = 0

        while not found && i < c.Length do
            if this.Kind c[i] = target then
                found <- true

            i <- i + 1

        found

    member private this.SliceContainsKind(c: IntSlice, target: NodeKind) =
        let mutable found = false
        let mutable i = 0

        while not found && i < c.Length do
            if this.Kind c[i] = target then
                found <- true

            i <- i + 1

        found

    member private this.SliceFindKind(c: IntSlice, target: NodeKind) =
        let mutable found = -1
        let mutable i = 0

        while found < 0 && i < c.Length do
            if this.Kind c[i] = target then
                found <- i

            i <- i + 1

        found

    member private this.SliceFindToken(c: IntSlice, target: TokenKind) =
        let mutable found = -1
        let mutable i = 0

        while found < 0 && i < c.Length do
            if this.At(c[i], target) then
                found <- i

            i <- i + 1

        found

    member private this.SliceFindTokenBack(c: IntSlice, target: TokenKind) =
        let mutable found = -1
        let mutable i = c.Length - 1

        while found < 0 && i >= 0 do
            if this.At(c[i], target) then
                found <- i

            i <- i - 1

        found

    member private this.SliceContainsToken(c: IntSlice, target: TokenKind) =
        this.SliceFindToken(c, target) >= 0

    member private this.SliceContainsInitializer(c: IntSlice) =
        let mutable found = false
        let mutable i = 0

        while not found && i < c.Length do
            if SyntaxFacts.initializer (this.Kind c[i]) then
                found <- true

            i <- i + 1

        found

    member private this.MultilineToken(n: int) =
        if not indexedMultilineTokens then
            let tokenCount = tree.TokenCount
            let toks = treeTokens
            let src = source
            let ascii = sourceIsAscii
            let mutable first = Int32.MaxValue
            let mutable last = -1

            for t = 0 to tokenCount - 1 do
                let token = &toks[t]

                if
                    token.Length > 1
                    && (token.Kind >= TokenKind.StringLiteralToken
                        || token.Kind = TokenKind.BadToken)
                    && (let s = src.AsSpan(token.Start, token.Length) in

                        if ascii then
                            s.IndexOfAny('\r', '\n') >= 0
                        else
                            s.IndexOfAny(SyntaxFacts.lineTerminators) >= 0)
                then
                    if t < first then
                        first <- t

                    last <- t

            firstMultilineToken <- first
            lastMultilineToken <- last
            indexedMultilineTokens <- true

        let first = this.First n
        let finish = this.Last n

        if finish < firstMultilineToken || first > lastMultilineToken then
            false
        else
            let toks = treeTokens
            let src = source
            let ascii = sourceIsAscii
            let mutable multiline = false
            let mutable t = max first firstMultilineToken
            let limit = min finish lastMultilineToken

            while not multiline && t <= limit do
                let token = &toks[t]

                if
                    token.Length > 1
                    && (token.Kind >= TokenKind.StringLiteralToken
                        || token.Kind = TokenKind.BadToken)
                then
                    let s = src.AsSpan(token.Start, token.Length)

                    multiline <-
                        if ascii then
                            s.IndexOfAny('\r', '\n') >= 0
                        else
                            s.IndexOfAny(SyntaxFacts.lineTerminators) >= 0

                t <- t + 1

            multiline

    member private _.Space(d: DocumentBuffer) = d.AddSpace()

    member private _.Hard(d: DocumentBuffer) =
        d.AddLine(LineKind.Hard, ElementFlags.Squash)

    member private this.Blank(d: DocumentBuffer) =
        this.Hard d
        d.AddLine(LineKind.Hard, ElementFlags.SquashBlank)

    member private this.Verbatim
        (
            start: int,
            finish: int,
            d: DocumentBuffer,
            [<Optional; DefaultParameterValue(false)>] trimLines: bool,
            [<Optional; DefaultParameterValue(false)>] preserveTokens: bool,
            [<Optional; DefaultParameterValue(false)>] trimEnd: bool,
            [<Optional; DefaultParameterValue(false)>] trailingLine: bool
        ) =
        let tokens =
            if preserveTokens then
                let buffer =
                    match triviaTokens with
                    | ValueSome existing -> existing
                    | ValueNone ->
                        let created = TokenBuffer()
                        triviaTokens <- ValueSome created
                        created

                Lexer.lexRange source start finish buffer
                ValueSome buffer
            else
                ValueNone

        let mutable finish = finish

        if trimEnd then
            let mutable tokenEnd = start

            match tokens with
            | ValueSome tokens ->
                for i = 0 to tokens.TokenCount - 1 do
                    let token = tokens.Token i

                    if token.Length > 0 then
                        tokenEnd <- max tokenEnd token.End
            | _ -> ()

            while finish > tokenEnd
                  && Char.IsWhiteSpace source[finish - 1]
                  && not (this.LiteralLine(finish - 1)) do
                finish <- finish - 1

        let mutable tokenIndex = 0
        let mutable cursor = start

        while cursor < finish do
            let line = cursor

            while cursor < finish && not (SyntaxFacts.lineTerminator source[cursor]) do
                cursor <- cursor + 1

            let mutable ending = cursor

            let tokenEnd =
                match tokens with
                | ValueSome tokens ->
                    while tokenIndex < tokens.TokenCount
                          && (let token = tokens.Token tokenIndex in token.End <= ending - 1) do
                        tokenIndex <- tokenIndex + 1

                    if tokenIndex < tokens.TokenCount then
                        let token = tokens.Token tokenIndex
                        if token.Start < ending then token.End else -1
                    else
                        -1
                | _ -> -1

            let literal = this.LiteralLine line

            if trimLines && tokenEnd < ending && not literal then
                while ending > max line tokenEnd && Char.IsWhiteSpace source[ending - 1] do
                    ending <- ending - 1

            let mutable previous = d.Count - 1

            while previous >= 0 && d.Storage[previous].Kind = ElementKind.Tag do
                previous <- previous - 1

            if
                line > start
                || (previous >= 0 && d.Storage[previous].Kind = ElementKind.Reindent)
            then
                d.AddTrim()

            if ending > line then
                d.AddText(source, line, ending - line)

            if cursor < finish then
                let newline = cursor

                if source[cursor] = '\r' && cursor + 1 < finish && source[cursor + 1] = '\n' then
                    cursor <- cursor + 1

                let literalNewline = newline < literalLength && literalOwned[newline]

                if tokenEnd > newline || literalNewline then
                    d.AddText(source, newline, cursor + 1 - newline)
                    d.AddReindent()
                else
                    d.AddLine LineKind.Literal

                cursor <- cursor + 1

        if
            trailingLine
            && (finish = start || not (SyntaxFacts.lineTerminator source[finish - 1]))
        then
            d.AddLine LineKind.Literal

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private _.AllSeen(start: int, count: int) =
        if not seen[start + count - 1] || not seen[start] then
            false
        else
            let mutable i = start + 1
            let last = start + count - 1

            while i < last && seen[i] do
                i <- i + 1

            i = last

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.DeclinedRun(t: int, start: int, count: int) =
        count = 0
        || (count = 1
            && (let kind = treeTrivia[start].Kind in

                kind = TriviaKind.WhitespaceTrivia
                || seen[start]
                || (if kind = TriviaKind.EndOfLineTrivia && blankSibling <> t then
                        seen[start] <- true
                        true
                    else
                        false)))
        || (count = 2
            && ((seen[start] && seen[start + 1])
                || (blankSibling <> t
                    && let k0 = treeTrivia[start].Kind in
                       let k1 = treeTrivia[start + 1].Kind in

                       if
                           k0 <= TriviaKind.WhitespaceTrivia && k1 <= TriviaKind.WhitespaceTrivia
                       then
                           seen[start] <- true
                           seen[start + 1] <- true
                           true
                       else
                           false)))
        || (count > 2 && this.AllSeen(start, count))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.DeclinedTrailing(start: int, count: int) =
        count = 0
        || (count = 1
            && (treeTrivia[start].Kind <= TriviaKind.WhitespaceTrivia || seen[start]))
        || (count = 2
            && ((treeTrivia[start].Kind <= TriviaKind.WhitespaceTrivia
                 && treeTrivia[start + 1].Kind <= TriviaKind.WhitespaceTrivia)
                || (seen[start] && seen[start + 1])))
        || (count > 2 && this.AllSeen(start, count))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.DeclinedLeading(t: int) =
        if uint32 t >= uint32 tree.TokenCount then
            false
        else
            let token = &treeTokens[t]
            this.DeclinedRun(t, token.TriviaStart, token.LeadingCount)

    member private _.HasTrivia(t: int, leading: bool) =
        if (not hasComments && not hasDirectives) || uint32 t >= uint32 tree.TokenCount then
            false
        else
            let token = &treeTokens[t]
            let start = token.TriviaStart + (if leading then 0 else token.LeadingCount)
            let count = if leading then token.LeadingCount else token.TrailingCount

            if count = 0 then
                false
            else
                let mutable found = false
                let mutable i = start
                let finish = start + count

                while not found && i < finish do
                    let kind = treeTrivia[i].Kind

                    if SyntaxFacts.comment kind || SyntaxFacts.directive kind then
                        found <- true

                    i <- i + 1

                found

    member private _.HasLeadingDirective(t: int) =
        if not hasDirectives || uint32 t >= uint32 tree.TokenCount then
            false
        else
            let token = &treeTokens[t]
            let start = token.TriviaStart
            let finish = start + token.LeadingCount
            let mutable i = start
            let mutable found = false

            while not found && i < finish do
                let kind = treeTrivia[i].Kind

                if SyntaxFacts.directive kind || kind = TriviaKind.DisabledTextTrivia then
                    found <- true

                i <- i + 1

            found

    member private this.IndexConditionals() =
        if not indexedConditionals then
            this.IndexIgnores()

            if not hasConditionalStructure then
                indexedConditionals <- true

        if not indexedConditionals then
            this.IndexConditionalsCold()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IndexConditionalsCold() =
        if
            not indexedConditionals
            && not hasIgnores
            && not (source.Contains("// csff-ignore", StringComparison.Ordinal))
        then
            hasConditionals <- true
            let requiredPrefixes = tree.TriviaCount + 1
            growCleared &emptyConditionalPrefixes requiredPrefixes requiredPrefixes
            conditionalStack.Clear()
            let mutable triviaToken = 0
            let mutable groupEnd = -1
            let mutable prefixDepth = 0
            let mutable prefixOpened = false
            let mutable prefixEmpty = true
            let mutable prefixContents = 0

            for i = 0 to min tree.TriviaCount tree.LexerBuffer.TriviaCount - 1 do
                let item = tree.Trivia i

                if i >= groupEnd then
                    prefixDepth <- 0
                    prefixOpened <- false
                    prefixEmpty <- true

                    while triviaToken + 1 < tree.TokenCount
                          && (let token = tree.Token triviaToken in
                              token.TriviaStart + token.LeadingCount + token.TrailingCount <= i) do
                        triviaToken <- triviaToken + 1

                    let token = tree.Token triviaToken
                    let leadingEnd = token.TriviaStart + token.LeadingCount

                    groupEnd <-
                        if i < leadingEnd then
                            leadingEnd
                        else
                            leadingEnd + token.TrailingCount

                let mutable fragmentCode = false

                if
                    item.Kind = TriviaKind.DisabledTextTrivia
                    && ((prefixOpened && prefixEmpty)
                        || (conditionalStack.Count > 0
                            && (let struct (_, _, topStart) =
                                    conditionalStack[conditionalStack.Count - 1] in

                                prefixContents = topStart)))
                then
                    let buffer =
                        match triviaTokens with
                        | ValueSome buffer -> buffer
                        | ValueNone ->
                            let buffer = TokenBuffer()
                            triviaTokens <- ValueSome buffer
                            buffer

                    Lexer.lexRange source item.Start (item.Start + item.Length) buffer
                    fragmentCode <- buffer.TokenCount > 1

                if item.Kind = TriviaKind.IfDirectiveTrivia then
                    prefixOpened <- true
                    prefixDepth <- prefixDepth + 1
                    conditionalStack.Add(struct (item.Start, i, prefixContents))
                elif
                    (item.Kind = TriviaKind.ElifDirectiveTrivia
                     || item.Kind = TriviaKind.ElseDirectiveTrivia)
                    && not prefixOpened
                then
                    prefixOpened <- true
                    prefixDepth <- 1
                elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                    prefixDepth <- prefixDepth - 1
                    prefixEmpty <- prefixEmpty && prefixDepth >= 0

                    if conditionalStack.Count > 0 then
                        let last = conditionalStack.Count - 1
                        let struct (opening, openingIndex, contentStart) = conditionalStack[last]
                        conditionalStack.RemoveAt last

                        conditionalPrefixes[openingIndex] <-
                            struct (i + 1, prefixContents = contentStart)

                        closedConditionals.Add opening |> ignore
                elif fragmentCode || item.Kind = TriviaKind.SkippedTokensTrivia then
                    prefixEmpty <- false
                    prefixContents <- prefixContents + 1

                emptyConditionalPrefixes[i + 1] <-
                    (item.Kind = TriviaKind.EndIfDirectiveTrivia
                     || (item.Kind = TriviaKind.BadDirectiveTrivia && emptyConditionalPrefixes[i]))
                    && prefixOpened
                    && prefixEmpty
                    && prefixDepth >= 0

            indexedConditionals <- true

        if not indexedConditionals then
            this.IndexConditionalsWithIgnores()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IndexConditionalsWithIgnores() =
        hasConditionals <- true
        hasComplexConditionals <- true
        let conditions = Stack<int>()
        let markedAt = Dictionary<int, int>()

        if tokenScopes.Length < tree.TokenCount then
            growCleared &tokenScopes 0 tree.TokenCount

        let scopes = tokenScopes
        let mutable scope = 0

        let record (index: Dictionary<int, ResizeArray<int>>) scope token =
            match index.TryGetValue scope with
            | true, positions -> positions.Add token
            | _ ->
                let positions = ResizeArray<int>()
                positions.Add token
                index[scope] <- positions

        for t = 0 to tree.TokenCount - 1 do
            scopes[t] <- scope
            let token = tree.Token t

            if ignoredSingles.Count > 0 then
                if ignoredSingles.Contains token.Start then
                    record followingSingles scope t

                if t > 0 && scope < scopes[t - 1] then
                    record scopeExits scopes[t - 1] t

            if token.Length > 0 then
                if token.Kind = TokenKind.OpenBraceToken then
                    scope <- scope + 1
                elif token.Kind = TokenKind.CloseBraceToken then
                    scope <- max 0 (scope - 1)

        let frames = ResizeArray<ConditionalFrame>()
        frames.Add(ConditionalFrame(-1, 0, 0))
        let frameIds = Dictionary<int, int>()
        let requests = ResizeArray<ConditionalRequest>()
        let singleOwners = HashSet<int>()
        let commentCounts = Stack<int>()
        let mutable comments = 0

        let classifyComment opening =
            if comments > commentCounts.Pop() then
                commentConditionals.Add opening |> ignore

            frames[frameIds[opening]].Finish <- frames.Count

        let markConditional opening index =
            if markedConditionals.Add opening then
                markedAt[opening] <- index

        let markScope opening owner =
            frames[frameIds[opening]].DirectScope <- owner

        let classifications = Stack<struct (int * int * int * int * int)>()
        let markerIndices = ResizeArray<int>()
        let rangeIndices = ResizeArray<int>()
        let mutable bodyMarkers = 0
        let mutable singleMarkers = 0
        let mutable openings = 0
        let mutable followingRangeCount = 0
        let followingParents = HashSet<int>()

        let classifyFirstRange opening ranges =
            if rangeIndices.Count > ranges then
                firstRangeConditionals.Add opening |> ignore

                if openings > rangeIndices[ranges] then
                    nestedFirstRanges.Add opening |> ignore

        let classify opening =
            let struct (markers, bodies, singles, ranges, following) = classifications.Pop()
            classifyComment opening

            if not (alternateConditionals.Contains opening) then
                classifyFirstRange opening ranges

            if rangeIndices.Count > ranges then
                rangeConditionals.Add opening |> ignore

            if followingRangeCount > following then
                followingParents.Add opening |> ignore

            if markerIndices.Count > markers then
                markConditional opening markerIndices[markers]

            if bodyMarkers > bodies then
                bodyMarkedConditionals.Add opening |> ignore

            if singleMarkers > singles then
                singleOwners.Add opening |> ignore

        let mutable nextToken = 0
        let followingRanges = Dictionary<int, int>()
        let rangeOpenings = Dictionary<int, int>()

        let mutable triviaToken = 0
        let mutable groupEnd = -1
        let mutable previous = -1
        let mutable ignoredDoc = false
        let mutable disabledDepth = 0
        let mutable prefixDepth = 0
        let mutable prefixOpened = false
        let mutable prefixEmpty = true
        let mutable prefixContents = 0
        let requiredPrefixes = tree.TriviaCount + 1
        growCleared &emptyConditionalPrefixes requiredPrefixes requiredPrefixes
        let suffixQueries = ResizeArray<struct (int * int * int)>()
        let suffixMarkers = Dictionary<int, int>()

        let finishGroup () =
            for struct (start, index, depth) in suffixQueries do
                match suffixMarkers.TryGetValue depth with
                | true, last when last > index -> disabledFollowingSingles.Add start |> ignore
                | _ -> ()

            suffixQueries.Clear()
            suffixMarkers.Clear()
            previous <- -1
            ignoredDoc <- false
            disabledDepth <- 0
            prefixDepth <- 0
            prefixOpened <- false
            prefixEmpty <- true

        let request opening owner (item: Trivia) index comment codeAfter =
            let frame = frameIds[opening]
            frames[frame].Requests.Add requests.Count

            requests.Add
                {
                    Frame = frame
                    Scope = owner
                    Start = item.Start
                    Index = index
                    Comment = comment
                    CodeAfter = codeAfter
                }

        for i = 0 to min tree.TriviaCount tree.LexerBuffer.TriviaCount - 1 do
            let item = tree.Trivia i

            if i >= groupEnd then
                finishGroup ()

                while triviaToken + 1 < tree.TokenCount
                      && (let token = tree.Token triviaToken in
                          token.TriviaStart + token.LeadingCount + token.TrailingCount <= i) do
                    triviaToken <- triviaToken + 1

                let token = tree.Token triviaToken
                let leadingEnd = token.TriviaStart + token.LeadingCount

                groupEnd <-
                    if i < leadingEnd then
                        leadingEnd
                    else
                        leadingEnd + token.TrailingCount

            while nextToken < tree.TokenCount
                  && (tree.Token nextToken).Start < item.Start + item.Length do
                nextToken <- nextToken + 1

            let mutable fragmentCode = false
            let mutable scannedComment = false

            if item.Kind = TriviaKind.DisabledTextTrivia then
                let buffer =
                    match triviaTokens with
                    | ValueSome buffer -> buffer
                    | ValueNone ->
                        let buffer = TokenBuffer()
                        triviaTokens <- ValueSome buffer
                        buffer

                Lexer.lexRange source item.Start (item.Start + item.Length) buffer
                fragmentCode <- buffer.TokenCount > 1
                let mutable next = 0
                let mutable fragmentDepth = 0
                let mutable openComment = false

                let advance finish =
                    while next < buffer.TokenCount && (buffer.Token next).Start < finish do
                        let token = buffer.Token next

                        if token.Kind = TokenKind.OpenBraceToken then
                            disabledDepth <- disabledDepth + 1
                            fragmentDepth <- fragmentDepth + 1
                        elif token.Kind = TokenKind.CloseBraceToken then
                            disabledDepth <- disabledDepth - 1
                            fragmentDepth <- fragmentDepth - 1

                        next <- next + 1

                for k = 0 to buffer.TriviaCount - 1 do
                    let comment = buffer.Trivia k

                    if
                        comment.Kind = TriviaKind.SingleLineCommentTrivia
                        && SyntaxFacts.ignoreMarker (
                            source.AsSpan(comment.Start, comment.Length).Trim()
                        )
                            =
                            1
                    then
                        advance (comment.Start + comment.Length)

                        if
                            next < buffer.TokenCount
                            && (buffer.Token next).Kind <> TokenKind.CloseBraceToken
                            && (buffer.Token next).Kind <> TokenKind.EndOfFileToken
                        then
                            suffixMarkers[disabledDepth] <- i

                    if
                        (comment.Kind = TriviaKind.MultiLineCommentTrivia
                         || comment.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                        && comment.Start + comment.Length = item.Start + item.Length
                        && not (
                            source
                                .AsSpan(comment.Start, comment.Length)
                                .TrimEnd()
                                .EndsWith("*/".AsSpan())
                        )
                    then
                        openComment <- true

                advance (item.Start + item.Length)
                commentFragments[item.Start] <- struct (openComment, fragmentDepth)

                if openComment then
                    comments <- comments + 1

            elif SyntaxFacts.comment item.Kind && this.ScannedComment(item.Start, item.Length) then
                scannedComment <- true
                comments <- comments + 1

            if item.Kind = TriviaKind.IfDirectiveTrivia then
                prefixOpened <- true
                prefixDepth <- prefixDepth + 1
            elif
                (item.Kind = TriviaKind.ElifDirectiveTrivia
                 || item.Kind = TriviaKind.ElseDirectiveTrivia)
                && not prefixOpened
            then
                prefixOpened <- true
                prefixDepth <- 1
            elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                prefixDepth <- prefixDepth - 1
                prefixEmpty <- prefixEmpty && prefixDepth >= 0
            elif fragmentCode || item.Kind = TriviaKind.SkippedTokensTrivia then
                prefixEmpty <- false
                prefixContents <- prefixContents + 1

            emptyConditionalPrefixes[i + 1] <-
                (item.Kind = TriviaKind.EndIfDirectiveTrivia
                 || (item.Kind = TriviaKind.BadDirectiveTrivia && emptyConditionalPrefixes[i]))
                && prefixOpened
                && prefixEmpty
                && prefixDepth >= 0

            let text = source.AsSpan(item.Start, item.Length)
            let newline = text.IndexOfAny(SyntaxFacts.lineTerminators)

            let marker =
                SyntaxFacts.ignoreMarker (
                    (if newline < 0 then text else text.Slice(0, newline)).Trim()
                )

            if item.Kind = TriviaKind.IfDirectiveTrivia then
                openings <- openings + 1

                let parent =
                    if conditions.Count > 0 then
                        frameIds[conditions.Peek()]
                    else
                        0

                frameIds[item.Start] <- frames.Count
                frames.Add(ConditionalFrame(item.Start, parent, frames[parent].Depth + 1))
                frames[frames.Count - 1].OpeningIndex <- i
                frames[frames.Count - 1].ContentStart <- prefixContents
                conditions.Push item.Start
                commentCounts.Push comments

                classifications.Push(
                    struct (markerIndices.Count,
                            bodyMarkers,
                            singleMarkers,
                            rangeIndices.Count,
                            followingRangeCount)
                )

            if SyntaxFacts.directive item.Kind then
                if ignoredDoc then
                    ignoredDocPrefixes.Add item.Start |> ignore

                if
                    conditions.Count > 0
                    && previous >= 0
                    && (tree.Trivia previous).Kind = TriviaKind.DisabledTextTrivia
                then
                    let gap = tree.Trivia previous
                    let struct (openComment, depth) = commentFragments[gap.Start]

                    if openComment then
                        request (conditions.Peek()) (scopes[triviaToken] + depth) item i false false

                suffixQueries.Add(struct (item.Start, i, disabledDepth))

            elif SyntaxFacts.comment item.Kind && conditions.Count > 0 then
                if scannedComment && alternateConditionals.Contains(conditions.Peek()) then
                    alternateBranchComments.Add item.Start |> ignore

                let codeAfter =
                    nextToken < tree.TokenCount
                    && (tree.Token nextToken).Kind <> TokenKind.CloseBraceToken
                    && (tree.Token nextToken).Kind <> TokenKind.EndOfFileToken

                let owner = if nextToken < scopes.Length then scopes[nextToken] else 0
                request (conditions.Peek()) owner item i true codeAfter

            if
                item.Kind = TriviaKind.MultiLineDocumentationCommentTrivia
                && this.IgnoreRange item.Start >= 0
            then
                ignoredDoc <- true

            if
                item.Kind <> TriviaKind.WhitespaceTrivia
                && item.Kind <> TriviaKind.EndOfLineTrivia
            then
                previous <- i

            if
                conditions.Count > 0
                && (item.Kind = TriviaKind.ElifDirectiveTrivia
                    || item.Kind = TriviaKind.ElseDirectiveTrivia)
            then
                let opening = conditions.Peek()

                if alternateConditionals.Add opening then
                    let struct (_, _, _, ranges, _) = classifications.Peek()
                    classifyFirstRange opening ranges
            elif item.Kind = TriviaKind.EndIfDirectiveTrivia && conditions.Count > 0 then
                let opening = conditions.Pop()
                let frame = frames[frameIds[opening]]

                conditionalPrefixes[frame.OpeningIndex] <-
                    struct (i + 1, prefixContents = frame.ContentStart)

                classify opening

                if conditions.Count > 0 && rangeConditionals.Contains opening then
                    nestedRangeConditionals.Add(conditions.Peek()) |> ignore

                closedConditionals.Add opening |> ignore
                let mutable next = item.Start + item.Length

                while next < source.Length && Char.IsWhiteSpace source[next] do
                    next <- next + 1

                let mutable finish = next

                while finish < source.Length && not (SyntaxFacts.lineTerminator source[finish]) do
                    finish <- finish + 1

                let followingMarker =
                    SyntaxFacts.ignoreMarker (source.AsSpan(next, finish - next).Trim())

                if followingMarker > 0 then
                    markConditional opening i

                if followingMarker = 1 || followingMarker = 2 then
                    followingConditionalPrefixes.Add opening |> ignore

                    while nextToken < tree.TokenCount && (tree.Token nextToken).Start < finish do
                        nextToken <- nextToken + 1

                if followingMarker = 2 then
                    if nextToken < tree.TokenCount then
                        markScope opening scopes[nextToken]

                if followingMarker = 1 then
                    followedSingleClosings.Add item.Start |> ignore

                    if
                        nextToken < tree.TokenCount
                        && (tree.Token nextToken).Kind <> TokenKind.CloseBraceToken
                        && (tree.Token nextToken).Kind <> TokenKind.EndOfFileToken
                    then
                        singleOwners.Add opening |> ignore
                        bodyMarkedConditionals.Add opening |> ignore
                        markScope opening scopes[nextToken]

                if SyntaxFacts.ignoreMarker (source.AsSpan(next, finish - next).Trim()) = 2 then
                    followingRanges[opening] <- finish
                    followingRangeCount <- followingRangeCount + 1

            if
                conditions.Count > 0
                && (item.Kind = TriviaKind.SingleLineCommentTrivia
                    || item.Kind = TriviaKind.DisabledTextTrivia)
                && marker > 0
            then
                while nextToken < tree.TokenCount
                      && (tree.Token nextToken).Start < item.Start + item.Length do
                    nextToken <- nextToken + 1

                let mutable code =
                    nextToken < tree.TokenCount
                    && (tree.Token nextToken).Kind <> TokenKind.CloseBraceToken
                    && (tree.Token nextToken).Kind <> TokenKind.EndOfFileToken

                if
                    code
                    && (tree.Token nextToken).Kind = TokenKind.OpenBraceToken
                    && nextToken + 1 < tree.TokenCount
                then
                    let close = tree.Token(nextToken + 1)
                    code <- close.Kind <> TokenKind.CloseBraceToken || close.LeadingCount > 0

                if item.Kind = TriviaKind.DisabledTextTrivia then
                    code <- code || fragmentCode

                markerIndices.Add i

                if code && (marker = 1 || marker = 2) then
                    bodyMarkers <- bodyMarkers + 1

                    if nextToken < tree.TokenCount then
                        frames[frameIds[conditions.Peek()]].Points.Add scopes[nextToken]

                    if marker = 1 then
                        singleMarkers <- singleMarkers + 1

                if marker = 2 then
                    rangeIndices.Add openings
                    conditionalIgnoreStarts.Add(item.Start + item.Length) |> ignore
                    rangeOpenings[item.Start + item.Length] <- conditions.Peek()

        finishGroup ()
        let mutable descendantRange = false

        for opening in conditions do
            if descendantRange then
                nestedRangeConditionals.Add opening |> ignore

            classify opening
            descendantRange <- rangeConditionals.Contains opening

        if conditions.Count > 0 then
            for opening in followingConditionalPrefixes do
                unfinishedFollowingPrefixes.Add opening |> ignore

            for opening in conditions do
                if followingParents.Contains opening then
                    unfinishedFollowingPrefixes.Add opening |> ignore

        for f = 1 to frames.Count - 1 do
            let frame = frames[f]
            let parent = frames[frame.Parent]
            let opening = frame.Opening
            let body = bodyMarkedConditionals.Contains opening
            let ranged = rangeConditionals.Contains opening
            let commented = commentConditionals.Contains opening
            frame.Ancestors[0] <- frame.Parent

            for bit = 1 to 30 do
                frame.Ancestors[bit] <- frames[frame.Ancestors[bit - 1]].Ancestors[bit - 1]

            let before =
                singleOwners.Contains opening
                || (followingRanges.ContainsKey opening
                    && not (alternateConditionals.Contains opening))
                || (ranged && body)

            frame.BeforeOwner <- if commented && before then f else parent.BeforeOwner

            frame.AfterOwner <-
                if commented && ranged && body && not (closedConditionals.Contains opening) then
                    f
                else
                    parent.AfterOwner

            frame.DirectiveOwner <- if commented && body then f else parent.DirectiveOwner

        let commonAncestor left right =
            let mutable left = left
            let mutable right = right

            if frames[left].Depth < frames[right].Depth then
                let swap = left
                left <- right
                right <- swap

            let difference = frames[left].Depth - frames[right].Depth

            for bit = 0 to 30 do
                if difference &&& (1 <<< bit) <> 0 then
                    left <- frames[left].Ancestors[bit]

            if left <> right then
                for bit = 30 downto 0 do
                    if frames[left].Ancestors[bit] <> frames[right].Ancestors[bit] then
                        left <- frames[left].Ancestors[bit]
                        right <- frames[right].Ancestors[bit]

                left <- frames[left].Parent

            left

        let candidates = Array.zeroCreate<int> requests.Count
        let last = Dictionary<int, int>()

        let collect f =
            for owner in frames[f].Points do
                last[owner] <- f

            for r in frames[f].Requests do
                match last.TryGetValue requests[r].Scope with
                | true, point ->
                    let ancestor = commonAncestor f point

                    if frames[ancestor].Depth > frames[candidates[r]].Depth then
                        candidates[r] <- ancestor
                | _ -> ()

        for f = 1 to frames.Count - 1 do
            collect f

        last.Clear()

        for f = frames.Count - 1 downto 1 do
            collect f

        let beforeScopes = Dictionary<int, Stack<int>>()
        let afterScopes = Dictionary<int, Stack<int>>()
        let directiveScopes = Dictionary<int, Stack<int>>()
        let active = Stack<int>()

        let push (index: Dictionary<int, Stack<int>>) scope frame =
            match index.TryGetValue scope with
            | true, owners -> owners.Push frame
            | _ ->
                let owners = Stack<int>()
                owners.Push frame
                index[scope] <- owners

        let peek (index: Dictionary<int, Stack<int>>) scope =
            match index.TryGetValue scope with
            | true, owners when owners.Count > 0 -> owners.Peek()
            | _ -> 0

        let pop (index: Dictionary<int, Stack<int>>) scope frame =
            match index.TryGetValue scope with
            | true, owners when owners.Count > 0 && owners.Peek() = frame -> owners.Pop() |> ignore
            | _ -> ()

        for f = 1 to frames.Count - 1 do
            while active.Count > 0 && frames[active.Peek()].Finish <= f do
                let old = active.Pop()
                let owner = frames[old].DirectScope
                pop beforeScopes owner old
                pop afterScopes owner old
                pop directiveScopes owner old

            let frame = frames[f]

            if frame.DirectScope >= 0 then
                active.Push f

                if frame.BeforeOwner = f then
                    push beforeScopes frame.DirectScope f

                if frame.AfterOwner = f then
                    push afterScopes frame.DirectScope f

                if frame.DirectiveOwner = f then
                    push directiveScopes frame.DirectScope f

            for r in frame.Requests do
                let query = requests[r]
                let candidate = frames[candidates[r]]
                let before = max candidate.BeforeOwner (peek beforeScopes query.Scope)
                let after = max candidate.AfterOwner (peek afterScopes query.Scope)
                let directive = max candidate.DirectiveOwner (peek directiveScopes query.Scope)

                if query.Comment then
                    if
                        (before > 0 && markedAt[frames[before].Opening] > query.Index)
                        || (query.CodeAfter && after > 0)
                    then
                        followingIgnoreComments.Add query.Start |> ignore
                elif directive > 0 then
                    let owners = HashSet<int>()
                    owners.Add query.Scope |> ignore
                    ownedCommentScopes[query.Start] <- owners

        for KeyValue(ending, opening) in rangeOpenings do
            if not (closedConditionals.Contains opening) then
                conditionalIgnoreStarts.Remove ending |> ignore

        let unfinishedRanges = HashSet<int>()

        for opening in conditions do
            let ending = this.IgnoreRange opening

            if ending >= 0 then
                unfinishedRanges.Add ending |> ignore

        for KeyValue(opening, markerEnd) in followingRanges do
            if unfinishedRanges.Contains(this.IgnoreRange markerEnd) then
                unfinishedRangeConditionals.Add opening |> ignore

        indexedConditionals <- true

    member private _.FollowingSingle(t: int, scope: int) =
        let next (positions: ResizeArray<int>) =
            let mutable lo = 0
            let mutable hi = positions.Count

            while lo < hi do
                let mid = lo + (hi - lo) / 2
                if positions[mid] < t then lo <- mid + 1 else hi <- mid

            if lo < positions.Count then
                positions[lo]
            else
                tree.TokenCount

        if tokenScopes[t] < scope then
            false
        else
            match followingSingles.TryGetValue scope with
            | true, positions ->
                let marker = next positions

                let finish =
                    match scopeExits.TryGetValue scope with
                    | true, positions -> next positions
                    | _ -> tree.TokenCount

                marker < finish
            | _ -> false

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.ScannedComment(start: int, length: int) =
        if
            (scannedDirectiveCount = 0 && pendingDirectiveSymbols.IsNone)
            || (length > 1
                && (let span = source.AsSpan(start, length) in

                    span.IndexOf('#') < 0
                    || span.IndexOfAny('\r', '\n') < 0
                    || (let mutable found = false
                        let mutable pos = 0

                        while not found && pos < span.Length do
                            let next = span.Slice(pos).IndexOf('#')

                            if next < 0 then
                                pos <- span.Length
                            else
                                let mutable k = start + pos + next + 1

                                while k < source.Length && (source[k] = ' ' || source[k] = '\t') do
                                    k <- k + 1

                                if k + 1 < source.Length then
                                    let c0 = source[k]
                                    let c1 = source[k + 1]

                                    found <-
                                        (c0 = 'i' && c1 = 'f')
                                        || (c0 = 'e' && (c1 = 'l' || c1 = 'n'))

                                pos <- pos + next + 1

                        not found)))
        then
            false
        else
            match pendingDirectiveSymbols with
            | ValueSome symbols ->
                pendingDirectiveSymbols <- ValueNone
                let scanned = DocumentStats.enter ()

                let buffer =
                    match triviaTokens with
                    | ValueSome existing -> existing
                    | ValueNone ->
                        let created = TokenBuffer()
                        triviaTokens <- ValueSome created
                        created

                let baseBuf = tree.LexerBuffer
                let tokHint = baseBuf.TokenCount + (baseBuf.TokenCount >>> 3) + 32
                let trivHint = baseBuf.TriviaCount + (baseBuf.TriviaCount >>> 3) + 64
                Lexer.lexWithHinted symbols tokHint trivHint source buffer
                let mutable count = 0

                for i = 0 to buffer.TriviaCount - 1 do
                    let item = buffer.Trivia i

                    if
                        item.Kind = TriviaKind.IfDirectiveTrivia
                        || item.Kind = TriviaKind.ElifDirectiveTrivia
                        || item.Kind = TriviaKind.ElseDirectiveTrivia
                        || item.Kind = TriviaKind.EndIfDirectiveTrivia
                    then
                        if count = scannedDirectives.Length then
                            Array.Resize(&scannedDirectives, max 16 (scannedDirectives.Length * 2))

                        scannedDirectives[count] <- item.Start
                        count <- count + 1

                scannedDirectiveCount <- count
                DocumentStats.lapse DocumentStats.tDirectives scanned
            | ValueNone -> ()

            if scannedDirectiveCount = 0 then
                false
            else
                let index = Array.BinarySearch(scannedDirectives, 0, scannedDirectiveCount, start)

                let next = if index < 0 then ~~~index else index
                next < scannedDirectiveCount && scannedDirectives[next] < start + length

    member private _.ConditionalIgnore(position: int) =
        let mutable lo = 0
        let mutable hi = ignoredRanges.Count

        while lo < hi do
            let mid = lo + (hi - lo) / 2
            let struct (first, _) = ignoredRanges[mid]
            if first <= position then lo <- mid + 1 else hi <- mid

        if lo = 0 then
            false
        else
            let struct (first, finish) = ignoredRanges[lo - 1]
            position < finish && conditionalIgnoreStarts.Contains first

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PreserveCommentDirectives(item: Trivia, length: int) =
        if not (this.ScannedComment(item.Start, length)) then
            false
        elif
            followingIgnoreComments.Contains item.Start
            && not (alternateBranchComments.Contains item.Start)
        then
            false
        elif this.IgnoreRange item.Start >= 0 then
            this.ConditionalIgnore item.Start
        else
            not (SyntaxFacts.warningCommentCloser (source.AsSpan(item.Start, length)))

    member private _.PrintableDisabled(item: Trivia) =
        let fragment =
            match disabledTree with
            | ValueSome value -> value
            | ValueNone ->
                let value = SyntaxTree()
                disabledTree <- ValueSome value
                value

        Parser.parse (source.Substring(item.Start, item.Length)) fragment
        SyntaxFacts.complete fragment && fragment.TokenCount > 1

    member private _.ExpandLiteralLines() =
        growCleared &literalLines literalLength literalLength

        let span = literalOwned.AsSpan(0, literalLength)
        let mutable cursor = 0

        while cursor < literalLength do
            let rel = span.Slice(cursor).IndexOf(true)

            if rel < 0 then
                cursor <- literalLength
            else
                let hit = cursor + rel
                let mutable first = hit

                while first > cursor && not (SyntaxFacts.lineTerminator source[first - 1]) do
                    first <- first - 1

                let mutable finish = hit

                while finish < literalLength && not (SyntaxFacts.lineTerminator source[finish]) do
                    finish <- finish + 1

                if finish < literalLength then
                    if
                        source[finish] = '\r'
                        && finish + 1 < literalLength
                        && source[finish + 1] = '\n'
                    then
                        finish <- finish + 2
                    else
                        finish <- finish + 1

                Array.Fill(literalLines, true, first, finish - first)
                cursor <- finish

    member private _.HasMultiConfigurationOwnership =
        match literalConfigurations with
        | ValueSome sets -> sets.Length > 0 || tree.LexerBuffer.HasSeededSymbols
        | ValueNone -> true

    member private this.LiteralLine(position: int) =
        if not indexedLiteralLines then
            if source.Contains '"' then
                let configurations =
                    match literalConfigurations with
                    | ValueSome sets -> sets
                    | ValueNone -> Preprocessor.symbolSets source tree

                if
                    configurations.Length > 0
                    || SyntaxFacts.literalOwnershipNeededCore
                        true
                        source
                        tree
                        (SyntaxFacts.complete tree)
                        false
                        false
                        (match triviaTokens with
                         | ValueSome _ -> triviaTokens
                         | ValueNone ->
                             let created = TokenBuffer()
                             triviaTokens <- ValueSome created
                             triviaTokens)
                then
                    let validMargin start ending =
                        let mutable delimiter = ending

                        while delimiter > start && source[delimiter - 1] = '"' do
                            delimiter <- delimiter - 1

                        let mutable margin = delimiter

                        while margin > start
                              && (source[margin - 1] = ' ' || source[margin - 1] = '\t') do
                            margin <- margin - 1

                        let width = delimiter - margin
                        let mutable cursor = start

                        let mutable valid =
                            margin > start && SyntaxFacts.lineTerminator source[margin - 1]

                        while cursor < margin && not (SyntaxFacts.lineTerminator source[cursor]) do
                            cursor <- cursor + 1

                        while valid && cursor < margin do
                            if
                                source[cursor] = '\r'
                                && cursor + 1 < margin
                                && source[cursor + 1] = '\n'
                            then
                                cursor <- cursor + 1

                            cursor <- cursor + 1
                            let first = cursor
                            let mutable blank = true

                            while cursor < margin && not (SyntaxFacts.lineTerminator source[cursor]) do
                                blank <- blank && (source[cursor] = ' ' || source[cursor] = '\t')
                                cursor <- cursor + 1

                            if not blank then
                                valid <- cursor - first >= width
                                let mutable offset = 0

                                while valid && offset < width do
                                    valid <- source[first + offset] = source[margin + offset]
                                    offset <- offset + 1

                        valid

                    let maxPass =
                        if
                            configurations.Length > 0
                            && tree.LexerBuffer.TokenCount > 0
                            && not tree.LexerBuffer.HasSeededSymbols
                        then
                            let buf = tree.LexerBuffer
                            let mutable needOtherPasses = false
                            let mutable k = 0

                            while not needOtherPasses && k < buf.TriviaCount do
                                let item = buf.Trivia k

                                match item.Kind with
                                | TriviaKind.SkippedTokensTrivia -> needOtherPasses <- true
                                | TriviaKind.DisabledTextTrivia ->
                                    if source.AsSpan(item.Start, item.Length).Contains('"') then
                                        needOtherPasses <- true
                                | TriviaKind.MultiLineCommentTrivia
                                | TriviaKind.MultiLineDocumentationCommentTrivia ->
                                    let finish = item.Start + item.Length
                                    let span = source.AsSpan(item.Start, item.Length)

                                    if
                                        (span.Contains('#') && span.Contains('"'))
                                        || finish >= source.Length
                                        || not (
                                            span.EndsWith("*/".AsSpan(), StringComparison.Ordinal)
                                        )
                                    then
                                        needOtherPasses <- true
                                | _ -> ()

                                k <- k + 1

                            k <- 0

                            while not needOtherPasses && k < buf.TokenCount do
                                let tok = buf.Token k

                                if SyntaxFacts.stringToken tok.Kind then
                                    if
                                        source
                                            .AsSpan(tok.Start, tok.Length)
                                            .IndexOfAny('#', '\r', '\n')
                                        >= 0
                                    then
                                        needOtherPasses <- true

                                k <- k + 1

                            if needOtherPasses then configurations.Length - 1 else -1
                        else
                            configurations.Length - 1

                    for pass = -1 to maxPass do
                        let buffer =
                            if
                                pass < 0
                                && tree.LexerBuffer.TokenCount > 0
                                && not tree.LexerBuffer.HasSeededSymbols
                            then
                                tree.LexerBuffer
                            else
                                let scratch =
                                    match triviaTokens with
                                    | ValueSome existing -> existing
                                    | ValueNone ->
                                        let created = TokenBuffer()
                                        triviaTokens <- ValueSome created
                                        created

                                let symbols = if pass < 0 then [||] else configurations[pass]
                                let baseBuf = tree.LexerBuffer
                                let tokHint = baseBuf.TokenCount + (baseBuf.TokenCount >>> 3) + 32

                                let trivHint =
                                    baseBuf.TriviaCount + (baseBuf.TriviaCount >>> 3) + 64

                                Lexer.lexWithHinted symbols tokHint trivHint source scratch
                                scratch

                        for i = 0 to buffer.TokenCount - 1 do
                            let token = buffer.Token i

                            if SyntaxFacts.stringToken token.Kind then
                                let start = token.Start
                                let ending = token.End

                                let finish =
                                    if
                                        token.Kind = TokenKind.Utf8StringLiteralToken
                                        || token.Kind =
                                            TokenKind.Utf8SingleLineRawStringLiteralToken
                                        || token.Kind = TokenKind.Utf8MultiLineRawStringLiteralToken
                                    then
                                        ending - 2
                                    else
                                        ending

                                let closed = finish > start && source[finish - 1] = '"'

                                let owned =
                                    not closed
                                    || (token.Kind <> TokenKind.MultiLineRawStringLiteralToken
                                        && token.Kind
                                           <> TokenKind.Utf8MultiLineRawStringLiteralToken)
                                    || whitespaceOnly
                                    || validMargin start finish

                                if owned then
                                    if literalLength = 0 then
                                        let n = source.Length
                                        literalLength <- n
                                        growCleared &literalOwned n n
                                        growCleared &literalInteriors n n
                                        growCleared &literalBoundaries (n + 1) (n + 1)

                                    Array.Fill(literalOwned, true, start, token.Length)

                                    if not closed then
                                        literalHasUnclosed <- true

                                if closed && owned then
                                    Array.Fill(
                                        literalInteriors,
                                        true,
                                        start + 1,
                                        max 0 (token.Length - 1)
                                    )

                                    literalBoundaries[start] <- 1
                                    literalBoundaries[ending] <- 1

                    if literalLength > 0 then
                        for i = 1 to literalLength do
                            literalBoundaries[i] <- literalBoundaries[i] + literalBoundaries[i - 1]

                        this.ExpandLiteralLines()

            indexedLiteralLines <- true

        position < literalLength && literalLines[position]

    member this.PrepareLiteralOwnership() =
        this.LiteralLine 0 |> ignore
        struct (literalOwned, literalInteriors, literalBoundaries, literalLength)

    member _.CurrentLiteralOwnership =
        struct (literalOwned, literalInteriors, literalBoundaries, literalLength)

    member _.PreserveLiteralGaps
        (formatted: string, mappings: ResizeArray<struct (int * int * int)>)
        =
        if not preserveForeignCode || literalLength = 0 then
            formatted
        else
            let mutable result = ValueNone
            let mutable restored = ValueNone
            let mutable cursor = 0
            let mutable shift = 0
            let buffer = tree.LexerBuffer

            for index = 0 to mappings.Count - 1 do
                let struct (position, first, count) = mappings[index]

                if index > 0 then
                    let struct (previous, start, length) = mappings[index - 1]
                    let ending = start + length
                    let outputEnd = previous + length

                    if
                        ending > 0
                        && first >= ending
                        && position >= outputEnd
                        && first < literalLength
                        && literalInteriors[ending - 1]
                        && literalInteriors[first]
                    then
                        let mutable ownedGap = true
                        let mutable offset = ending

                        while ownedGap && offset < first do
                            ownedGap <- literalInteriors[offset]
                            offset <- offset + 1

                        let mutable lo = 0
                        let mutable hi = buffer.TokenCount

                        while lo < hi do
                            let mid = lo + (hi - lo) / 2

                            if (buffer.Token mid).Start <= first then
                                lo <- mid + 1
                            else
                                hi <- mid

                        let ownLiteral =
                            lo > 0
                            && (let token = buffer.Token(lo - 1) in

                                token.End > first
                                && literalOwned[token.Start]
                                && not literalInteriors[token.Start])

                        let gap = source.AsSpan(ending, first - ending)

                        if
                            ownedGap
                            && not ownLiteral
                            && (not (
                                    gap.SequenceEqual(
                                        formatted.AsSpan(outputEnd, position - outputEnd)
                                    )
                                )
                                || (not gap.IsEmpty
                                    && literalBoundaries[first] <> literalBoundaries[ending - 1]))
                        then
                            let struct (text, slices) =
                                match result, restored with
                                | ValueSome text, ValueSome slices -> struct (text, slices)
                                | _ ->
                                    let text = System.Text.StringBuilder(formatted.Length)
                                    let slices = ResizeArray<struct (int * int * int)>()

                                    for previousIndex = 0 to index - 1 do
                                        slices.Add mappings[previousIndex]

                                    result <- ValueSome text
                                    restored <- ValueSome slices
                                    struct (text, slices)

                            text.Append(formatted.AsSpan(cursor, outputEnd - cursor)) |> ignore

                            if not gap.IsEmpty then
                                slices.Add(struct (text.Length, ending, gap.Length))
                                text.Append gap |> ignore

                            cursor <- position
                            shift <- shift + gap.Length - (position - outputEnd)

                match restored with
                | ValueSome slices -> slices.Add(struct (position + shift, first, count))
                | _ -> ()

            match result, restored with
            | ValueSome text, ValueSome slices ->
                text.Append(formatted.AsSpan cursor) |> ignore
                mappings.Clear()
                mappings.AddRange slices
                text.ToString()
            | _ -> formatted

    member _.RemapLiteralOwnership(length: int, mappings: ResizeArray<struct (int * int * int)>) =
        growCleared &remapOwned length length
        growCleared &remapInteriors length length
        growCleared &remapBoundaries (length + 1) (length + 1)

        let owned = remapOwned
        let interiors = remapInteriors
        let boundaries = remapBoundaries

        if literalLength > 0 then
            let mutable previousEnd = 0
            let mutable previousSourceEnd = 0
            let mutable wroteBoundary = false

            for struct (position, first, count) in mappings do
                if count > 0 then
                    let beforeFirst = if first = 0 then 0 else literalBoundaries[first - 1]
                    let hasBoundary = literalBoundaries[first + count] > beforeFirst

                    if hasBoundary || literalOwned[first] || literalHasUnclosed then
                        Array.Copy(literalOwned, first, owned, position, count)
                        Array.Copy(literalInteriors, first, interiors, position, count)

                    if
                        previousEnd > 0
                        && position > previousEnd
                        && literalInteriors[previousSourceEnd - 1]
                        && literalInteriors[first]
                        && first >= previousSourceEnd
                        && literalBoundaries[first] = literalBoundaries[previousSourceEnd - 1]
                    then
                        Array.Fill(owned, true, previousEnd, position - previousEnd)
                        Array.Fill(interiors, true, previousEnd, position - previousEnd)

                    if hasBoundary then
                        for offset = 0 to count do
                            let cursor = first + offset

                            if
                                literalBoundaries[cursor] >
                                    (if cursor = 0 then 0 else literalBoundaries[cursor - 1])
                            then
                                boundaries[position + offset] <- 1
                                wroteBoundary <- true

                    previousEnd <- position + count
                    previousSourceEnd <- first + count

            if wroteBoundary then
                for index = 1 to length do
                    boundaries[index] <- boundaries[index] + boundaries[index - 1]

        struct (owned, interiors, boundaries, length)

    member private this.ForeignLiteral(token: Token) =
        if not this.HasMultiConfigurationOwnership then
            let buffer = tree.LexerBuffer

            if not buffer.HasInterpolated || buffer.TokenCount = 0 then
                false
            else
                let mutable lo = 0
                let mutable hi = buffer.TokenCount

                while lo < hi do
                    let mid = lo + (hi - lo) / 2

                    if (buffer.Token mid).Start <= token.Start then
                        lo <- mid + 1
                    else
                        hi <- mid

                lo > 0
                && (let outer = buffer.Token(lo - 1) in

                    outer.Kind = TokenKind.InterpolatedStringToken
                    && outer.Start < token.Start
                    && token.Start < outer.End
                    && outer.End > outer.Start
                    && source[outer.End - 1] = '"')
        else
            this.LiteralLine token.Start |> ignore

            token.Start < literalLength
            && (literalInteriors[token.Start]
                || (token.Length > 1
                    && literalBoundaries[token.End - 1] > literalBoundaries[token.Start]))

    member private _.CommentFragment(item: Trivia) =
        match commentFragments.TryGetValue item.Start with
        | true, result -> result
        | _ ->
            let buffer =
                match triviaTokens with
                | ValueSome buffer -> buffer
                | ValueNone ->
                    let buffer = TokenBuffer()
                    triviaTokens <- ValueSome buffer
                    buffer

            let finish = item.Start + item.Length
            Lexer.lexRange source item.Start finish buffer
            let mutable opened = false
            let mutable depth = 0

            for i = 0 to buffer.TokenCount - 1 do
                let token = buffer.Token i

                if token.Kind = TokenKind.OpenBraceToken then
                    depth <- depth + 1
                elif token.Kind = TokenKind.CloseBraceToken then
                    depth <- depth - 1

            for i = 0 to buffer.TriviaCount - 1 do
                let comment = buffer.Trivia i

                if
                    (comment.Kind = TriviaKind.MultiLineCommentTrivia
                     || comment.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                    && comment.Start + comment.Length = finish
                    && not (
                        source
                            .AsSpan(comment.Start, comment.Length)
                            .TrimEnd()
                            .EndsWith("*/".AsSpan())
                    )
                then
                    opened <- true

            let result = struct (opened, depth)
            hasConditionals <- true
            commentFragments[item.Start] <- result
            result

    member private this.OpenCommentFragment(item: Trivia) =
        let struct (opened, _) = this.CommentFragment item
        opened

    member private this.Trivia
        (
            t: int,
            leading: bool,
            d: DocumentBuffer,
            [<Optional; DefaultParameterValue(-1)>] finishIndex: int,
            [<Optional; DefaultParameterValue(false)>] spaceBeforeComments: bool,
            [<Optional; DefaultParameterValue(false)>] measureComments: bool
        ) =
        let mutable enter = true

        if stats then
            statTriviaRuns <- statTriviaRuns + 1

        if uint32 t < uint32 tree.TokenCount then
            let token = &treeTokens[t]
            let start = token.TriviaStart + (if leading then 0 else token.LeadingCount)
            let total = if leading then token.LeadingCount else token.TrailingCount

            let finish =
                start
                + min total ((if finishIndex < 0 then start + total else finishIndex) - start)

            let keepBlank = leading && blankSibling = t
            let mutable i = start
            let mutable nontrivial = false

            while not nontrivial && i < finish do
                let kind = treeTrivia[i].Kind

                if kind > TriviaKind.WhitespaceTrivia then
                    nontrivial <- true
                elif not seen[i] && keepBlank && kind = TriviaKind.EndOfLineTrivia then
                    nontrivial <- true

                i <- i + 1

            if not nontrivial then
                for j = start to finish - 1 do
                    seen[j] <- true

                enter <- false
            else
                let mutable k = start
                let mutable unseen = false

                while not unseen && k < finish do
                    unseen <- not seen[k]
                    k <- k + 1

                enter <- unseen

        if enter then
            if stats then
                statTriviaEntered <- statTriviaEntered + 1

            this.TriviaCore(t, leading, d, finishIndex, spaceBeforeComments, measureComments)

    member private this.TriviaCore
        (
            t: int,
            leading: bool,
            d: DocumentBuffer,
            [<Optional; DefaultParameterValue(-1)>] finishIndex: int,
            [<Optional; DefaultParameterValue(false)>] spaceBeforeComments: bool,
            [<Optional; DefaultParameterValue(false)>] measureComments: bool
        ) =
        if uint32 t < uint32 tree.TokenCount then
            let token = &treeTokens[t]
            let start = token.TriviaStart + (if leading then 0 else token.LeadingCount)
            let total = if leading then token.LeadingCount else token.TrailingCount

            let count =
                min total ((if finishIndex < 0 then start + total else finishIndex) - start)

            if
                leading
                && (token.Kind = TokenKind.ElseKeyword
                    || token.Kind = TokenKind.CatchKeyword
                    || token.Kind = TokenKind.FinallyKeyword)
            then
                this.TriviaContinuationGap(start, count)

            let mutable newlines = 0
            let mutable afterEndIf = false
            let mutable afterRegion = false
            let mutable afterOpening = false
            let mutable afterTrivia = false
            let mutable copiedCommentEnd = -1
            let mutable preserveBlank = blankSibling = t
            let mutable endMarker = -1

            for i = start to start + count - 1 do
                let item = tree.Trivia i
                let kind = item.Kind

                if SyntaxFacts.comment kind || SyntaxFacts.directive kind then
                    preserveBlank <- true

                if
                    hasIgnores
                    && endMarker < 0
                    && kind = TriviaKind.SingleLineCommentTrivia
                    && SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, item.Length).Trim()) = 3
                then
                    endMarker <- i

                if seen[i] && kind = TriviaKind.EndRegionDirectiveTrivia then
                    afterRegion <- true

            let literal = endMarker >= 0 && not seen[endMarker] && this.LiteralIgnoreGap t
            let mutable afterLiteral = false

            for i = start to start + count - 1 do
                if not seen[i] then
                    seen[i] <- true
                    let item = tree.Trivia i
                    let kind = item.Kind

                    if
                        kind <> TriviaKind.EndOfLineTrivia && kind <> TriviaKind.WhitespaceTrivia
                    then
                        afterEndIf <- kind = TriviaKind.EndIfDirectiveTrivia

                    if kind = TriviaKind.EndOfLineTrivia then
                        newlines <- newlines + 1
                        let protectedGap = endMarker >= 0 && i < endMarker

                        if leading && literal && protectedGap then
                            d.AddTrim()

                            let whitespace =
                                i > start && (tree.Trivia(i - 1)).Kind = TriviaKind.WhitespaceTrivia

                            if whitespace then
                                let whitespace = tree.Trivia(i - 1)
                                d.AddText(source, whitespace.Start, whitespace.Length)

                            d.AddLine(
                                LineKind.Literal,
                                if afterLiteral || whitespace then
                                    0uy
                                else
                                    ElementFlags.SquashBlank
                            )

                            afterLiteral <- true
                        elif
                            leading
                            && preserveBlank
                            && (not compactUsingTrivia || afterEndIf || protectedGap)
                            && (newlines = 1 || protectedGap)
                            && (suppressBlank <> t
                                || i > start + 1
                                || afterTrivia
                                || afterOpening
                                || afterEndIf
                                || protectedGap)
                        then
                            d.AddLine(LineKind.Hard, ElementFlags.SquashBlank)
                    elif SyntaxFacts.comment kind then
                        afterLiteral <- false

                        this.TriviaComment(
                            t,
                            leading,
                            d,
                            start,
                            count,
                            i,
                            item,
                            kind,
                            afterRegion,
                            spaceBeforeComments,
                            measureComments,
                            literal && i < endMarker,
                            &newlines
                        )
                    elif
                        SyntaxFacts.directive kind
                        || kind = TriviaKind.DisabledTextTrivia
                        || kind = TriviaKind.SkippedTokensTrivia
                    then
                        afterLiteral <- false

                        let wrapAlwaysFits =
                            headerDirectiveAlwaysFits
                            && (SyntaxFacts.directive kind || kind = TriviaKind.DisabledTextTrivia)

                        if wrapAlwaysFits then
                            d.AddTag Tag.StartAlwaysFits

                        this.TriviaDirectiveOrDisabled(
                            t,
                            leading,
                            d,
                            start,
                            i,
                            item,
                            kind,
                            &afterRegion,
                            &afterOpening,
                            &copiedCommentEnd
                        )

                        if wrapAlwaysFits then
                            d.AddTag Tag.EndAlwaysFits

                        newlines <- 0

                match treeTrivia[i].Kind with
                | TriviaKind.EndOfLineTrivia
                | TriviaKind.WhitespaceTrivia -> ()
                | _ -> afterTrivia <- true

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TriviaContinuationGap(start: int, count: int) =
        let mutable first = start

        while first < start + count
              && ((tree.Trivia first).Kind = TriviaKind.WhitespaceTrivia
                  || (tree.Trivia first).Kind = TriviaKind.EndOfLineTrivia) do
            first <- first + 1

        if first < start + count && SyntaxFacts.comment (tree.Trivia first).Kind then
            for i = start to first - 1 do
                seen[i] <- true

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TriviaComment
        (
            t: int,
            leading: bool,
            d: DocumentBuffer,
            start: int,
            count: int,
            i: int,
            item: Trivia,
            kind: TriviaKind,
            afterRegion: bool,
            spaceBeforeComments: bool,
            measureComments: bool,
            protectedGap: bool,
            newlines: byref<int>
        ) =
        let token = &treeTokens[t]

        if spaceBeforeComments then
            this.Space d

        let mutable length = item.Length

        while length > 0 && SyntaxFacts.lineTerminator source[item.Start + length - 1] do
            length <- length - 1

        let marker =
            hasIgnores
            && afterRegion
            && SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, length).TrimEnd()) = 2

        if afterRegion && marker && token.Kind <> TokenKind.CloseBraceToken then
            d.AddTrim()
            let mutable first = item.Start

            while first > 0 && (source[first - 1] = ' ' || source[first - 1] = '\t') do
                first <- first - 1

            d.AddText(source, first, item.Start + length - first)
        elif measureComments then
            d.AddText(source, item.Start, length)
        else
            let mutable first = item.Start

            if kind = TriviaKind.MultiLineDocumentationCommentTrivia then
                let mutable onlySpaceOrTab = true

                while first > 0
                      && (let c = source[first - 1] in

                          if c = ' ' || c = '\t' then
                              true
                          elif c = '\v' || c = '\f' then
                              onlySpaceOrTab <- false
                              true
                          else
                              false) do
                    first <- first - 1

                if
                    onlySpaceOrTab
                    || (hasIgnores
                        && token.Kind <> TokenKind.EndOfFileToken
                        && (ignoredSingles.Contains token.Start
                            || (this.IgnoreRange token.Start >= 0
                                && not (importEnds.ContainsKey token.Start))))
                then
                    first <- item.Start
                else
                    while first < item.Start && (source[first] = ' ' || source[first] = '\t') do
                        first <- first + 1

            d.AddComment(
                source,
                first,
                item.Start + length - first,
                leading,
                kind = TriviaKind.MultiLineCommentTrivia
                || kind = TriviaKind.MultiLineDocumentationCommentTrivia,
                conditional = this.PreserveCommentDirectives(item, length)
            )

        if leading then
            let endOfLine = item.Start + item.Length > item.Start + length
            let mutable j = i + 1
            let mutable line = endOfLine

            while j < start + count && (tree.Trivia j).Kind = TriviaKind.WhitespaceTrivia do
                j <- j + 1

            if j < start + count && (tree.Trivia j).Kind = TriviaKind.EndOfLineTrivia then
                line <- true

            if line then
                d.AddLine(LineKind.Hard, ElementFlags.Squash ||| ElementFlags.SkipBreakIfFirst)

                if not endOfLine then
                    if j < start + count then
                        seen[j] <- true

                newlines <- 0

                if
                    endOfLine
                    && not compactUsingTrivia
                    && not protectedGap
                    && j < start + count
                    && (tree.Trivia j).Kind = TriviaKind.EndOfLineTrivia
                then
                    d.AddLine(LineKind.Hard, ElementFlags.SquashBlank)

    member private this.ContinuesDisabledConstruct(i: int) =
        let start = (tree.Trivia i).Start
        let struct (runStart, runEnd, _) = disabledRun

        if start < runStart || start >= runEnd then
            let adjacent k =
                let item = tree.Trivia k
                item.Start + item.Length = (tree.Trivia(k + 1)).Start

            let mutable low = i

            while low > 0 && adjacent (low - 1) do
                low <- low - 1

            let mutable high = i

            while high + 1 < tree.TriviaCount && adjacent high do
                high <- high + 1

            let buffer =
                match triviaTokens with
                | ValueSome existing -> existing
                | ValueNone ->
                    let created = TokenBuffer()
                    triviaTokens <- ValueSome created
                    created

            let mutable opened = Int32.MaxValue
            let mutable k = low

            while k <= high && opened = Int32.MaxValue do
                let item = tree.Trivia k

                if item.Kind = TriviaKind.DisabledTextTrivia then
                    let finish = item.Start + item.Length
                    Lexer.lexRange source item.Start finish buffer
                    let tokens = buffer.TokenCount
                    let trivia = buffer.TriviaCount

                    let openToken =
                        tokens > 1 && (let token = buffer.Token(tokens - 2) in token.End >= finish)

                    let openComment =
                        if trivia = 0 then
                            false
                        else
                            let last = buffer.Trivia(trivia - 1)

                            (last.Kind = TriviaKind.MultiLineCommentTrivia
                             || last.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                            && last.Start + last.Length >= finish

                    if openToken || openComment then
                        opened <- finish

                k <- k + 1

            let last = tree.Trivia high
            disabledRun <- struct ((tree.Trivia low).Start, last.Start + last.Length, opened)

        let struct (_, _, opened) = disabledRun
        start >= opened

    member private this.DisabledText(i: int, first: int, finish: int, d: DocumentBuffer) =
        let span = source.AsSpan(first, finish - first)

        if hasIgnores || span.Contains("// csff-ignore".AsSpan(), StringComparison.Ordinal) then
            d.AddText(source, first, finish - first, ElementFlags.Directive)
        else
            let mutable tokens = ValueNone
            let mutable tokenIndex = 0
            let mutable segment = first
            let mutable cursor = first

            while cursor < finish do
                let line = cursor

                while cursor < finish && not (SyntaxFacts.lineTerminator source[cursor]) do
                    cursor <- cursor + 1

                let mutable ending = cursor
                let mutable trimmed = false

                if cursor = finish || source[cursor] = '\r' || source[cursor] = '\n' then
                    while ending > line && (source[ending - 1] = ' ' || source[ending - 1] = '\t') do
                        ending <- ending - 1

                if ending < cursor then
                    this.LiteralLine line |> ignore

                if
                    ending < cursor
                    && (cursor > literalLength || not literalOwned[cursor - 1])
                    && (tokens.IsSome || not (this.ContinuesDisabledConstruct i))
                then
                    let buffer =
                        match tokens with
                        | ValueSome existing -> existing
                        | ValueNone ->
                            let buffer =
                                match triviaTokens with
                                | ValueSome existing -> existing
                                | ValueNone ->
                                    let created = TokenBuffer()
                                    triviaTokens <- ValueSome created
                                    created

                            Lexer.lexRange source first finish buffer
                            tokens <- ValueSome buffer
                            buffer

                    while tokenIndex < buffer.TokenCount
                          && (let token = buffer.Token tokenIndex in token.End <= ending) do
                        tokenIndex <- tokenIndex + 1

                    if
                        tokenIndex >= buffer.TokenCount || (buffer.Token tokenIndex).Start >= cursor
                    then
                        d.AddText(source, segment, ending - segment, ElementFlags.Directive)
                        segment <- cursor
                        trimmed <- true

                if cursor < finish then
                    if
                        source[cursor] = '\r' && cursor + 1 < finish && source[cursor + 1] = '\n'
                    then
                        cursor <- cursor + 1

                    cursor <- cursor + 1

                    if trimmed then
                        d.AddText(source, segment, cursor - segment, ElementFlags.Directive)
                        d.AddReindent()
                        d.AddTrim()
                        segment <- cursor

            if segment < finish then
                d.AddText(source, segment, finish - segment, ElementFlags.Directive)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TriviaDirectiveOrDisabled
        (
            t: int,
            leading: bool,
            d: DocumentBuffer,
            start: int,
            i: int,
            item: Trivia,
            kind: TriviaKind,
            afterRegion: byref<bool>,
            afterOpening: byref<bool>,
            copiedCommentEnd: byref<int>
        ) =
        let token = &treeTokens[t]

        if SyntaxFacts.directive kind then
            let canCrossLiteral =
                this.HasMultiConfigurationOwnership || i >= tree.LexerBuffer.TriviaCount

            if canCrossLiteral && this.LiteralLine item.Start then
                d.AddTrim()
                let mutable first = item.Start

                while first > 0 && not (SyntaxFacts.lineTerminator source[first - 1]) do
                    first <- first - 1

                let lineStart = first
                let mutable previous = i - 1

                while previous >= 0
                      && (tree.Trivia previous).Start + (tree.Trivia previous).Length > first do
                    let prefix = tree.Trivia previous

                    if
                        seen[previous]
                        && prefix.Kind <> TriviaKind.WhitespaceTrivia
                        && prefix.Kind <> TriviaKind.EndOfLineTrivia
                    then
                        first <- max first (prefix.Start + prefix.Length)

                    previous <- previous - 1

                d.AddText(source, first, item.Start + item.Length - first, ElementFlags.Directive)

                if
                    item.Length = 0
                    || not (SyntaxFacts.lineTerminator source[item.Start + item.Length - 1])
                then
                    d.AddLine(LineKind.Hard, ElementFlags.Squash ||| ElementFlags.NoTrim)
                elif first = lineStart then
                    d.AddReindent()
            elif i < tree.LexerBuffer.TriviaCount && tree.LexerBuffer.IsInactiveDirective i then
                d.AddTrim()
                let mutable first = item.Start

                if
                    not (
                        kind = TriviaKind.EndIfDirectiveTrivia
                        && followedSingleClosings.Contains item.Start
                    )
                then
                    while first > 0 && (source[first - 1] = ' ' || source[first - 1] = '\t') do
                        first <- first - 1

                let mutable finish = item.Start + item.Length

                while finish > first && SyntaxFacts.lineTerminator source[finish - 1] do
                    finish <- finish - 1

                d.AddText(source, first, finish - first, ElementFlags.Directive)
                this.Hard d
            else
                let region =
                    kind = TriviaKind.RegionDirectiveTrivia
                    || kind = TriviaKind.EndRegionDirectiveTrivia

                if region then
                    d.AddTag Tag.StartAlwaysFits

                this.Hard d
                let mutable length = item.Length

                while length > 0 && Char.IsWhiteSpace source[item.Start + length - 1] do
                    length <- length - 1

                if region then
                    d.AddRegion(
                        source,
                        item.Start,
                        length,
                        (kind = TriviaKind.EndRegionDirectiveTrivia)
                    )
                else
                    d.AddTrim()
                    let mutable first = item.Start

                    let mutable previous = i - 1

                    while previous >= start
                          && ((tree.Trivia previous).Kind = TriviaKind.WhitespaceTrivia
                              || (tree.Trivia previous).Kind = TriviaKind.EndOfLineTrivia) do
                        previous <- previous - 1

                    let struct (openComment, fragmentDepth) =
                        if
                            (hasIgnores
                             || ownedCommentScopes.Count > 0
                             || followingSingles.Count > 0
                             || disabledFollowingSingles.Count > 0
                             || ignoredDocPrefixes.Count > 0)
                            && previous >= start
                            && (tree.Trivia previous).Kind = TriviaKind.DisabledTextTrivia
                        then
                            this.CommentFragment(tree.Trivia previous)
                        else
                            struct (false, 0)

                    let scope =
                        if openComment && t < tokenScopes.Length then
                            tokenScopes[t] + fragmentDepth
                        else
                            0

                    let followingSingle = openComment && this.FollowingSingle(t, scope)
                    let disabledSingle = openComment && disabledFollowingSingles.Contains item.Start

                    let copiedComment =
                        openComment
                        && (followingSingle
                            || disabledSingle
                            || (ownedCommentScopes.ContainsKey item.Start
                                && ownedCommentScopes[item.Start].Contains scope)
                            || (this.IgnoreRange item.Start >= 0
                                && ignoredDocPrefixes.Contains item.Start))

                    if copiedComment && item.Start >= copiedCommentEnd then
                        let closing = source.IndexOf("*/", item.Start, StringComparison.Ordinal)

                        copiedCommentEnd <- if closing < 0 then source.Length else closing + 2

                    if copiedComment || item.Start < copiedCommentEnd then
                        while first > 0 && (source[first - 1] = ' ' || source[first - 1] = '\t') do
                            first <- first - 1

                    if
                        leading
                        && suppressBlank = t
                        && markedConditionals.Contains item.Start
                        && (recoveringConditionals
                            || unfinishedRangeConditionals.Contains item.Start
                            || (token.Kind = TokenKind.OpenBraceToken
                                && closedConditionals.Contains item.Start
                                && not (rangeConditionals.Contains item.Start)
                                && this.ConditionalPrefixAt(t, i, false))
                            || (rangeConditionals.Contains item.Start
                                && alternateConditionals.Contains item.Start
                                && this.ConditionalPrefixAt(t, i, true)))
                    then
                        while first > 0 && (source[first - 1] = ' ' || source[first - 1] = '\t') do
                            first <- first - 1

                    if
                        leading
                        && suppressBlank = t
                        && (unfinishedFollowingPrefixes.Contains item.Start
                            || nestedFirstRanges.Contains item.Start
                            || (nestedRangeConditionals.Contains item.Start
                                && firstRangeConditionals.Contains item.Start)
                            || (markedConditionals.Contains item.Start
                                && not (rangeConditionals.Contains item.Start)
                                && not (alternateConditionals.Contains item.Start)
                                && bodyMarkedConditionals.Contains item.Start
                                && this.ConditionalPrefixAt(t, i, true)))
                        && this.ScannedComment(item.Start, 1)
                    then
                        while first > 0 && (source[first - 1] = ' ' || source[first - 1] = '\t') do
                            first <- first - 1

                    if token.Kind = TokenKind.UsingKeyword && this.IgnoreRange token.Start >= 0 then
                        while first > 0
                              && Char.IsWhiteSpace source[first - 1]
                              && not (SyntaxFacts.lineTerminator source[first - 1]) do
                            first <- first - 1

                    d.AddText(source, first, item.Start + length - first, ElementFlags.Directive)

                this.Hard d

                if region then
                    d.AddTag Tag.EndAlwaysFits

            afterRegion <- kind = TriviaKind.EndRegionDirectiveTrivia

            afterOpening <-
                kind = TriviaKind.RegionDirectiveTrivia || kind = TriviaKind.IfDirectiveTrivia
        else
            d.AddTrim()
            let mutable first = item.Start

            let canCrossLiteral =
                this.HasMultiConfigurationOwnership
                || kind = TriviaKind.SkippedTokensTrivia
                || i >= tree.LexerBuffer.TriviaCount

            if
                kind = TriviaKind.DisabledTextTrivia
                && canCrossLiteral
                && this.LiteralLine first
            then
                while first > 0 && (source[first - 1] = ' ' || source[first - 1] = '\t') do
                    first <- first - 1

            if kind = TriviaKind.DisabledTextTrivia then
                this.DisabledText(i, first, item.Start + item.Length, d)
            else
                d.AddText(source, first, item.Start + item.Length - first, ElementFlags.Directive)

            if
                item.Length = 0
                || not (SyntaxFacts.lineTerminator source[item.Start + item.Length - 1])
                || not canCrossLiteral
                || not (this.LiteralLine(item.Start + item.Length - 1))
            then
                d.AddLine(LineKind.Hard, ElementFlags.Squash ||| ElementFlags.NoTrim)
            else
                d.AddReindent()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ClosingTrivia(t: int, d: DocumentBuffer) =
        let token = &treeTokens[t]

        if not (this.DeclinedRun(t, token.TriviaStart, token.LeadingCount)) then
            let start = d.Count

            if token.LeadingCount > 0 && token.TriviaStart > 0 then
                let mutable i = token.TriviaStart - 1

                while i >= 0 && treeTrivia[i].Kind = TriviaKind.WhitespaceTrivia do
                    i <- i - 1

                if i >= 0 && treeTrivia[i].Kind = TriviaKind.EndOfLineTrivia then
                    this.Hard d

            this.Trivia(t, true, d)
            let mutable last = d.Count - 1

            while last >= start
                  && (d.Storage[last].Kind = ElementKind.Line
                      || d.Storage[last].Kind = ElementKind.Tag) do
                if d.Storage[last].Kind = ElementKind.Line then
                    d.Remove last

                last <- last - 1

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TokenEofLeading(token: inref<Token>, d: DocumentBuffer) =
        if token.LeadingCount > 0 && token.TriviaStart > 0 then
            let mutable i = token.TriviaStart - 1

            while i >= 0 && treeTrivia[i].Kind = TriviaKind.WhitespaceTrivia do
                i <- i - 1

            if i >= 0 && treeTrivia[i].Kind = TriviaKind.EndOfLineTrivia then
                this.Hard d

    member private this.Token
        (
            t: int,
            d: DocumentBuffer,
            [<Optional; DefaultParameterValue(false)>] spaceBeforeComments: bool,
            [<Optional; DefaultParameterValue(false)>] measureComments: bool
        ) =
        let token = &treeTokens[t]

        if token.Kind = TokenKind.EndOfFileToken then
            this.TokenEofLeading(&token, d)

        if t <> lastDeclinedLeadingToken then
            if
                t <> hoistedLeadingToken
                && not (this.DeclinedRun(t, token.TriviaStart, token.LeadingCount))
            then
                this.Trivia(t, true, d)

            lastDeclinedLeadingToken <- t

        if token.Kind = TokenKind.EndOfFileToken then
            this.Hard d
        elif token.Length > 0 then
            let kind = int token.Kind

            let fastCodeToken =
                kind < int TokenKind.BadToken
                || kind = int TokenKind.NumericLiteralToken
                || (sourceIsAscii
                    && (kind = int TokenKind.IdentifierToken
                        || (kind = int TokenKind.StringLiteralToken
                            && source[token.Start] <> '@'
                            && source[token.Start + token.Length - 1] = '"')
                        || (kind = int TokenKind.CharacterLiteralToken
                            && source[token.Start + token.Length - 1] = '\'')
                        || (kind = int TokenKind.Utf8StringLiteralToken
                            && source[token.Start] <> '@'
                            && source[token.Start + token.Length - 1] = '8')
                        || (kind = int TokenKind.SingleLineRawStringLiteralToken
                            && source[token.Start + token.Length - 1] = '"')
                        || (kind = int TokenKind.Utf8SingleLineRawStringLiteralToken
                            && source[token.Start + token.Length - 1] = '8')
                        || kind = int TokenKind.InterpolatedSingleLineRawStringStartToken))

            if fastCodeToken then
                d.AddCodeToken(token.Start, token.Length, uint32 token.Length)
            else
                d.AddText(source, token.Start, token.Length)

        if
            not (this.DeclinedTrailing(token.TriviaStart + token.LeadingCount, token.TrailingCount))
        then
            this.Trivia(t, false, d, -1, spaceBeforeComments, measureComments)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.Emit(n: int, d: DocumentBuffer) =
        if n < 0 then
            let token = -n - 1

            if ignoreUntil < 0 || treeTokens[token].Start >= ignoreUntil then
                this.Token(token, d)
        else
            this.Print(n, d)

    member private this.All(children: IntSlice, d: DocumentBuffer) =
        for i = 0 to children.Length - 1 do
            this.Emit(children[i], d)

    member private this.WordBoundary(a: int, b: int) =
        let last = this.Last a
        let first = this.First b

        if last < 0 || first >= tree.TokenCount then
            false
        else
            let x = &treeTokens[last]
            let y = &treeTokens[first]

            if x.Length = 0 || y.Length = 0 then
                false
            else
                let left = source[x.End - 1]
                let right = source[y.Start]

                let inline identifierEdge (ch: char) =
                    if uint32 ch < 128u then
                        uint32 (int ch - int 'a') <= 25u
                        || uint32 (int ch - int 'A') <= 25u
                        || uint32 (int ch - int '0') <= 9u
                        || ch = '_'
                        || ch = '@'
                    else
                        Char.IsLetterOrDigit ch
                        || match Char.GetUnicodeCategory ch with
                           | UnicodeCategory.LetterNumber
                           | UnicodeCategory.NonSpacingMark
                           | UnicodeCategory.SpacingCombiningMark
                           | UnicodeCategory.ConnectorPunctuation
                           | UnicodeCategory.Format -> true
                           | _ -> false

                (identifierEdge right || right = '\\')
                && (identifierEdge left
                    || left = '?'
                    || (left = '*' && this.Kind a = NodeKind.PointerType)
                    || left = ']'
                    || left = '>'
                    || left = '}'
                    || left = ')')

    member private this.Spaced(children: IntSlice, d: DocumentBuffer) =
        for i = 0 to children.Length - 1 do
            if i > 0 then
                let a, b = children[i - 1], children[i]
                let ta = this.TokenKind a
                let tb = this.TokenKind b
                let ka = this.Kind a
                let kb = this.Kind b

                if
                    this.WordBoundary(a, b)
                    || ta = TokenKind.CommaToken
                    || ta = TokenKind.ColonToken
                    || ta = TokenKind.EqualsToken
                    || tb = TokenKind.EqualsToken
                    || ka = NodeKind.NameColon
                    || ka = NodeKind.NameEquals
                    || kb = NodeKind.EqualsValueClause
                    || ((ta = TokenKind.ReturnKeyword
                         || ta = TokenKind.ThrowKeyword
                         || ta = TokenKind.AwaitKeyword)
                        && tb <> TokenKind.SemicolonToken)
                    || ta = TokenKind.RefKeyword
                    || ta = TokenKind.ReadOnlyKeyword
                    || ta = TokenKind.ScopedKeyword
                    || (ta = TokenKind.ThisKeyword
                        && kb <> NodeKind.ArgumentList
                        && kb <> NodeKind.BracketedArgumentList
                        && kb <> NodeKind.BracketedParameterList)
                    || ta = TokenKind.OutKeyword
                    || ta = TokenKind.InKeyword
                    || ta = TokenKind.NotKeyword
                    || ta = TokenKind.FromKeyword
                    || ta = TokenKind.JoinKeyword
                    || ta = TokenKind.OnKeyword
                    || ta = TokenKind.EqualsKeyword
                    || tb = TokenKind.EqualsKeyword
                    || ta = TokenKind.GroupKeyword
                    || ta = TokenKind.SelectKeyword
                    || ta = TokenKind.WhereKeyword
                    || ta = TokenKind.OrderByKeyword
                    || ta = TokenKind.ByKeyword
                    || tb = TokenKind.ByKeyword
                    || tb = TokenKind.AscendingKeyword
                    || tb = TokenKind.DescendingKeyword
                    || (ta = TokenKind.CaseKeyword && tb <> TokenKind.ColonToken)
                    || ka = NodeKind.AttributeList
                    || (kb = NodeKind.ParenthesizedVariableDesignation
                        && let token = &treeTokens[this.First a] in
                           source.AsSpan(token.Start, token.Length).SequenceEqual("var".AsSpan()))
                    || ta = TokenKind.OperatorKeyword
                    || (ta = TokenKind.CheckedKeyword
                        && i > 1
                        && this.At(children[i - 2], TokenKind.OperatorKeyword))
                    || ((ta = TokenKind.AsyncKeyword || ta = TokenKind.StaticKeyword)
                        && kb = NodeKind.ParameterList)
                    || ((ta = TokenKind.SwitchKeyword || ta = TokenKind.CaseKeyword)
                        && (tb = TokenKind.OpenParenToken
                            || kb = NodeKind.TupleExpression
                            || kb = NodeKind.ParenthesizedPattern))
                    || ta = TokenKind.WhenKeyword
                    || ta = TokenKind.ParamsKeyword
                    || (ta = TokenKind.DelegateKeyword && kb <> NodeKind.ParameterList)
                    || ta = TokenKind.EqualsGreaterThanToken
                    || tb = TokenKind.EqualsGreaterThanToken
                then
                    this.Space d

            this.Emit(children[i], d)

    member private this.DropListCommentBlanks(children: IntSlice) =
        if children.Length >= 4 && hasComments then
            for i = 2 to children.Length - 2 do
                if this.At(children[i - 1], TokenKind.CommaToken) then
                    let token = &treeTokens[this.First children[i]]

                    if token.LeadingCount > 1 then
                        let finish = token.TriviaStart + token.LeadingCount
                        let mutable first = token.TriviaStart

                        while first < finish
                              && (let k = treeTrivia[first].Kind in k <= TriviaKind.WhitespaceTrivia) do
                            first <- first + 1

                        if first < finish && SyntaxFacts.comment treeTrivia[first].Kind then
                            for j = token.TriviaStart to first - 1 do
                                seen[j] <- true

    member private this.Delimited
        (
            children: IntSlice,
            d: DocumentBuffer,
            padding: bool,
            commas: bool,
            forced: bool,
            [<Optional; DefaultParameterValue(false)>] inheritMode: bool,
            [<Optional; DefaultParameterValue(false)>] flatItems: bool,
            [<Optional; DefaultParameterValue(false)>] preserveBlanks: bool,
            [<Optional; DefaultParameterValue(false)>] trimComma: bool,
            [<Optional; DefaultParameterValue(false)>] emptyBreak: bool
        ) =
        if children.Length < 2 then
            this.All(children, d)
        else
            let inline emit node =
                if flatItems then
                    d.AddTag Tag.StartForceFlat

                this.Emit(node, d)

                if flatItems then
                    d.AddTag Tag.EndForceFlat

            let id =
                if inheritMode then
                    -1
                else
                    d.StartGroup(if forced then ElementFlags.Break else 0uy)

            if inheritMode && forced then
                d.AddBreakParent()

            this.Emit(children[0], d)
            let nodes = children.SliceRange(1, children.Length - 2)

            if forced && nodes.Length > 0 then
                suppressBlank <- this.First nodes[0]

            if nodes.Length > 0 then
                let countBroken =
                    maxOutputLength < Array.MaxLength
                    && d.SuppressedBreakDepth = 0
                    && nodes.Length = 1
                    && nodes[0] >= 0
                    && treeNodes[nodes[0]].TokenCount > 2 * maxLineLength
                    && not flatItems
                    && not inheritMode
                    && ignoreUntil < 0
                    && tree.IsComplete

                if countBroken then
                    this.AddBrokenIndent()

                d.AddTag Tag.StartIndent
                d.AddLine(if padding then LineKind.Normal else LineKind.Soft)

                for i = 0 to nodes.Length - 1 do
                    if
                        i > 0
                        && (this.Kind nodes[i] = NodeKind.SwitchExpressionArm
                            || (preserveBlanks && not (this.At(nodes[i], TokenKind.CommaToken))))
                    then
                        blankSibling <- this.First nodes[i]

                    if ignoreUntil >= 0 && treeTokens[this.First nodes[i]].Start < ignoreUntil then
                        ()
                    elif this.At(nodes[i], TokenKind.CommaToken) then
                        if i < nodes.Length - 1 then
                            this.Token(-nodes[i] - 1, d)

                            if this.Kind nodes[i + 1] <> NodeKind.OmittedTypeArgument then
                                d.AddLine LineKind.Normal
                        elif commas || trimComma then
                            this.TrailingComma(
                                -nodes[i] - 1,
                                (if i > 0 then this.Last nodes[i - 1] else -1),
                                id,
                                d
                            )
                        else
                            this.Token(-nodes[i] - 1, d)
                    elif commas && i = nodes.Length - 1 then
                        this.EmitDelimitedTrailingCommaItem(nodes[i], id, flatItems, d)
                    else
                        emit nodes[i]

                let closing = children[children.Length - 1]

                if
                    (this.At(closing, TokenKind.CloseBraceToken)
                     || this.At(closing, TokenKind.CloseBracketToken))
                    && this.HasTrivia(this.First closing, true)
                then
                    this.ClosingTrivia(this.First closing, d)

                d.AddTag Tag.EndIndent

                if countBroken then
                    brokenIndentDepth <- brokenIndentDepth - 1

                d.AddLine(if padding then LineKind.Normal else LineKind.Soft)

            if nodes.Length = 0 then
                let closing = children[children.Length - 1]

                if
                    (this.At(closing, TokenKind.CloseBraceToken)
                     || this.At(closing, TokenKind.CloseBracketToken))
                    && this.HasTrivia(this.First closing, true)
                then
                    d.AddTag Tag.StartIndent
                    this.Hard d
                    this.ClosingTrivia(this.First closing, d)
                    d.AddTag Tag.EndIndent
                    this.Hard d
                elif emptyBreak then
                    d.AddLine LineKind.Normal
                elif padding then
                    this.Space d

            this.Emit(children[children.Length - 1], d)

            if not inheritMode then
                d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TrailingComma(comma: int, previous: int, id: int, d: DocumentBuffer) =
        if not whitespaceOnly then
            changedTrailingCommas <- true

        this.Trivia(comma, true, d)

        if
            whitespaceOnly
            || this.HasTrivia(comma, false)
            || this.HasTrivia(comma, true)
            || this.HasTrivia(previous, false)
        then
            d.AddToken StaticToken.Comma
        else
            d.AddTag(Tag.StartIfBreak, id)
            d.AddToken StaticToken.Comma
            d.AddTag Tag.EndIfBreak

        this.Trivia(comma, false, d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private _.AddBrokenIndent() =
        brokenIndentDepth <- brokenIndentDepth + 1

        brokenIndentChars <-
            brokenIndentChars + int64 ((2 * brokenIndentDepth - 1) * unitIndent + 2)

        if brokenIndentChars > int64 maxOutputLength then
            raise (VerificationLimitException VerificationLimit.Message)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.EmitDelimitedTrailingCommaItem
        (node: int, id: int, flatItems: bool, d: DocumentBuffer)
        =
        let next = this.Last node + 1

        let directiveFollows =
            next < tree.TokenCount
            && (let token = tree.Token next
                let mutable found = false

                for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                    let kind = (tree.Trivia j).Kind

                    if SyntaxFacts.directive kind || kind = TriviaKind.DisabledTextTrivia then
                        found <- true

                found)

        if not directiveFollows && not whitespaceOnly then
            changedTrailingCommas <- true
            let t = this.Last node
            let token = tree.Token t

            for j = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                              + token.LeadingCount
                                                              + token.TrailingCount
                                                              - 1 do
                if seen.Length < tree.TriviaCount then
                    Array.Resize(&seen, max 16 tree.TriviaCount)

                seen[j] <- true

            if flatItems then
                d.AddTag Tag.StartForceFlat

            this.Emit(node, d)

            if flatItems then
                d.AddTag Tag.EndForceFlat

            if token.End >= ignoreUntil then
                if this.HasTrivia(t, false) then
                    d.AddToken StaticToken.Comma
                else
                    d.AddTag(Tag.StartIfBreak, id)
                    d.AddToken StaticToken.Comma
                    d.AddTag Tag.EndIfBreak

            for j = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                              + token.LeadingCount
                                                              + token.TrailingCount
                                                              - 1 do
                if (tree.Trivia j).Start >= ignoreUntil then
                    seen[j] <- false

            this.Trivia(t, false, d)
        else
            if flatItems then
                d.AddTag Tag.StartForceFlat

            this.Emit(node, d)

            if flatItems then
                d.AddTag Tag.EndForceFlat

    member private this.BareGenericTypeArgument(children: IntSlice) =
        children.Length = 3 && this.Kind children[1] = NodeKind.GenericName

    member private this.BinaryPatternOperand(n: int) =
        let parent = this.Parent n

        SyntaxFacts.binary (this.Kind parent)
        && let children = this.Children parent in children.Length = 3 && children[2] = n

    member private this.JoinsPropertyClause(pattern: int, clause: int) =
        let c = this.Children pattern
        let host = this.Parent pattern

        c[0] <> clause
        && not (this.Kind host = NodeKind.IsPatternExpression && this.BinaryPatternOperand host)
        && not (this.HasTrivia(this.First clause, true))

    member private this.CloserFollowsCloser(c: IntSlice) =
        c.Length > 0
        && c[c.Length - 1] < 0
        && (let closer = -c[c.Length - 1] - 1

            closer > 0
            && treeTokens[closer].Kind = TokenKind.GreaterThanToken
            && treeTokens[closer - 1].Kind = TokenKind.GreaterThanToken
            && treeTokens[closer - 1].End = treeTokens[closer].Start)

    member private this.TypeArguments(n: int, d: DocumentBuffer) =
        let c = this.Children n

        if whitespaceOnly && this.CloserFollowsCloser c then
            d.AddTag Tag.StartForceFlat
            this.Delimited(c, d, false, false, false)
            d.AddTag Tag.EndForceFlat
        elif n = callTypeArguments && (c.Length <> 3 || this.BareGenericTypeArgument c) then
            this.Delimited(c, d, false, false, false)
        else
            let previous = flatSingleTypeArguments

            if c.Length = 3 && (previous || not (this.BareGenericTypeArgument c)) then
                flatSingleTypeArguments <- true
                this.All(c, d)
            else
                flatSingleTypeArguments <- false
                this.Delimited(c, d, false, false, false)

            flatSingleTypeArguments <- previous

    member private this.VisitUnbreakableGenericType
        (flatSingles: bool, node: int, generic: byref<bool>)
        =
        if node < 0 then
            true
        else
            this.EnsureStack()
            let children = this.Children node

            match this.Kind node with
            | NodeKind.TypeArgumentList ->
                generic <- true

                if
                    children.Length = 3
                    && (flatSingles || not (this.BareGenericTypeArgument children))
                then
                    let mutable ok = true
                    let mutable i = 0

                    while ok && i < children.Length do
                        ok <- this.VisitUnbreakableGenericType(true, children[i], &generic)
                        i <- i + 1

                    ok
                else
                    false
            | NodeKind.TupleType
            | NodeKind.FunctionPointerParameterList -> false
            | _ ->
                let mutable ok = true
                let mutable i = 0

                while ok && i < children.Length do
                    ok <- this.VisitUnbreakableGenericType(flatSingles, children[i], &generic)
                    i <- i + 1

                ok

    member private this.UnbreakableGenericType(n: int) =
        let mutable generic = false
        this.VisitUnbreakableGenericType(false, n, &generic) && generic

    member private this.IgnoreCompleteNode(n: int, d: DocumentBuffer) =
        if not hasIgnores && ignoreUntil < 0 then
            false
        else
            let first = (tree.Token(this.First n)).Start
            let last = tree.Token(this.Last n)
            let finish = last.End
            let range = this.IgnoreRange first

            if (range >= 0 && range < finish) || (first < ignoreUntil && ignoreUntil < finish) then
                false
            else
                this.IgnoreNode(n, d)

    member private this.Binary
        (
            n: int,
            d: DocumentBuffer,
            indent: bool,
            [<Optional; DefaultParameterValue(false)>] inheritMode: bool
        ) =
        this.EnsureStack()

        if
            not (this.IgnoreCompleteNode(n, d))
            && (not preserveForeignCode || not (this.ForeignNode(n, d)))
        then
            this.BinaryCore(n, d, indent, inheritMode)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.BinaryCore
        (
            n: int,
            d: DocumentBuffer,
            indent: bool,
            [<Optional; DefaultParameterValue(false)>] inheritMode: bool
        ) =
        let children = this.Children n

        if children.Length <> 3 then
            this.Spaced(children, d)
        else
            let op = this.TokenKind children[1]
            let precedence = SyntaxFacts.precedence op
            let parent = this.Kind(this.Parent n)
            let first = this.First n

            if parent <> NodeKind.ReturnStatement && not (this.DeclinedLeading first) then
                this.Trivia(first, true, d)

            let id =
                if inheritMode then
                    -1
                else
                    d.StartGroup(
                        if
                            SyntaxFacts.binary parent
                            && (SyntaxFacts.binary (this.Kind children[0])
                                || this.Kind children[0] = NodeKind.ParenthesizedExpression)
                            && this.HasTrivia(first, true)
                        then
                            ElementFlags.Break
                        else
                            0uy
                    )

            let mutable spine = n
            let mutable more = true

            while more do
                let c = this.Children spine

                if c.Length = 3 && SyntaxFacts.binary (this.Kind c[0]) then
                    let previous = this.Children c[0]

                    if
                        previous.Length = 3
                        && SyntaxFacts.precedence (this.TokenKind previous[1]) = precedence
                    then
                        spine <- c[0]
                    else
                        more <- false
                else
                    more <- false

            let headChildren = this.Children spine
            let head = headChildren[0]
            let headStart = d.Count

            if
                parent = NodeKind.ReturnStatement
                && (SyntaxFacts.binary (this.Kind head)
                    || this.Kind head = NodeKind.InvocationExpression
                    || (precedence = 1 && this.Kind head = NodeKind.ConditionalAccessExpression)
                    || this.Kind head = NodeKind.ParenthesizedExpression)
            then
                d.AddTag Tag.StartIndent
                this.Emit(head, d)
                d.AddTag Tag.EndIndent
            else
                this.Emit(head, d)

            let mutable headGroup = -1
            let mutable headIndex = headStart
            let mutable headCanBreak = false

            while headIndex < d.Count && (headGroup < 0 || not headCanBreak) do
                let element = d.Storage[headIndex]

                if
                    headGroup < 0
                    && element.Kind = ElementKind.Tag
                    && element.B = int Tag.StartGroup
                then
                    headGroup <- element.A

                if element.Kind = ElementKind.Line then
                    headCanBreak <- true

                headIndex <- headIndex + 1

            if not headCanBreak then
                headGroup <- -1

            let headOperands = this.Children head

            if
                spine <> n
                && this.Kind head = NodeKind.ParenthesizedExpression
                && headOperands.Length = 3
                && not (SyntaxFacts.binary (this.Kind headOperands[1]))
            then
                headGroup <- -1

            let start = d.Count

            if indent then
                d.AddTag Tag.StartIndent
                this.BinaryTail(n, d, spine, precedence, head, headGroup)
                d.AddTag Tag.EndIndent
            else
                this.BinaryTail(n, d, spine, precedence, head, headGroup)

            ignore start

            if id >= 0 then
                d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.EmitCoalesceChain(node: int, d: DocumentBuffer) =
        let inline ignoredOrForeign n =
            (hasIgnores && this.IgnoreCompleteNode(n, d))
            || (preserveForeignCode && this.ForeignNode(n, d))

        if ignoredOrForeign node then
            ()
        else
            let r0 = this.Children node
            this.Emit(r0[0], d)
            let mutable curr = node
            let mutable cont = true

            while cont do
                let r = this.Children curr
                d.AddLine LineKind.Normal
                this.Emit(r[1], d)
                this.Space d

                if this.Kind r[2] = NodeKind.CoalesceExpression then
                    if ignoredOrForeign r[2] then
                        cont <- false
                    else
                        let rr = this.Children r[2]
                        this.Emit(rr[0], d)
                        curr <- r[2]
                else
                    this.Emit(r[2], d)
                    cont <- false

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ShouldIfBreakBinaryHead
        (n: int, c: IntSlice, spine: int, precedence: int, head: int)
        =
        not (
            (precedence = 2 || precedence = 3)
            && (this.Kind head = NodeKind.LogicalNotExpression
                || (this.Kind head = NodeKind.InvocationExpression
                    && SyntaxFacts.binary (this.Kind(this.Parent n))))
        )
        && not (SyntaxFacts.binary (this.Kind c[2]))
        && (precedence = 1
            || this.Kind head <> NodeKind.ParenthesizedExpression
            || let operands = this.Children head in

               operands.Length = 3
               && ((SyntaxFacts.binary (this.Kind operands[1])
                    && this.Kind operands[1] <> NodeKind.LogicalAndExpression
                    && this.Kind operands[1] <> NodeKind.LogicalOrExpression)
                   || not (SyntaxFacts.binary (this.Kind c[2]))))
        && ((n = spine
             && precedence <> 1
             && not (SyntaxFacts.binary (this.Kind head))
             && this.Kind head <> NodeKind.IsPatternExpression)
            || (precedence = 1
                && (this.Kind head = NodeKind.ParenthesizedExpression
                    || this.Kind head = NodeKind.CastExpression)))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.EmitIfBreakBinaryHead
        (c: IntSlice, precedence: int, headGroup: int, d: DocumentBuffer)
        =
        d.AddTag(Tag.StartIfBreak, headGroup)
        d.StartGroup() |> ignore
        d.AddLine LineKind.Normal
        let start = d.Count
        this.Emit(c[1], d)
        this.Space d

        if precedence = 1 && this.Kind c[2] = NodeKind.CoalesceExpression then
            this.EmitCoalesceChain(c[2], d)
        else
            this.Emit(c[2], d)

        let length = d.Count - start
        d.EndGroup()
        d.AddTag Tag.Else
        d.AddLine LineKind.Normal
        d.AddShared(start, length)
        d.AddTag Tag.EndIfBreak

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.BinaryTail
        (n: int, d: DocumentBuffer, spine: int, precedence: int, head: int, headGroup: int)
        =
        this.EnsureStack()
        let c = this.Children n

        if n <> spine then
            let first = this.First c[0]

            if not (this.DeclinedLeading first) then
                this.Trivia(first, true, d)

            this.BinaryTail(c[0], d, spine, precedence, head, headGroup)

        if headGroup >= 0 && this.ShouldIfBreakBinaryHead(n, c, spine, precedence, head) then
            this.EmitIfBreakBinaryHead(c, precedence, headGroup, d)
        else
            d.AddLine LineKind.Normal
            this.Emit(c[1], d)
            this.Space d

            if precedence = 1 && this.Kind c[2] = NodeKind.CoalesceExpression then
                this.EmitCoalesceChain(c[2], d)
            else
                this.Emit(c[2], d)

    member private this.Pattern(n: int, d: DocumentBuffer) =
        let kind = this.Kind n
        let host = this.Kind(this.Parent n)
        let grouped = host <> NodeKind.IsPatternExpression

        if grouped then
            d.StartGroup() |> ignore

        let mutable spine = n
        let mutable children = this.Children spine

        while this.Kind children[0] = kind do
            spine <- children[0]
            children <- this.Children spine

        let spine = spine
        this.Emit(children[0], d)

        if host = NodeKind.SwitchExpressionArm || host = NodeKind.CasePatternSwitchLabel then
            this.PatternTail(n, d, spine)
        else
            d.AddTag Tag.StartIndent
            this.PatternTail(n, d, spine)
            d.AddTag Tag.EndIndent

        if grouped then
            d.EndGroup()

    member private this.PatternTail(n: int, d: DocumentBuffer, spine: int) =
        this.EnsureStack()
        let c = this.Children n

        if n <> spine then
            let first = this.First c[0]

            if not (this.DeclinedLeading first) then
                this.Trivia(first, true, d)

            this.PatternTail(c[0], d, spine)

        d.AddLine LineKind.Normal
        this.Emit(c[1], d)
        this.Space d
        this.Emit(c[2], d)

    member private _.CanReplayFlat(d: DocumentBuffer, start: int, length: int) =
        let mutable canCopy = length <= 256
        let mutable i = start

        while canCopy && i < start + length do
            let e = d.Storage[i]

            if
                e.Kind = ElementKind.Shared
                || (e.Kind = ElementKind.Tag && e.B = int Tag.StartConditionalGroup)
            then
                canCopy <- false

            i <- i + 1

        canCopy

    member private this.ReplayFlat(d: DocumentBuffer, start: int, length: int) =
        if this.CanReplayFlat(d, start, length) then
            d.AddTag Tag.StartForceFlat
            d.Append(d, start, length)
            d.AddTag Tag.EndForceFlat
        else
            d.AddShared(start, length)

    member private _.FlatPrefixEnding
        (d: DocumentBuffer, first: int, finish: int, work: byref<int>, valid: byref<bool>)
        =
        let mutable depth = 1
        let mutable i = first + 1
        let mutable middle = -1

        while valid && i < finish && depth > 0 do
            work <- work + 1
            valid <- work <= 1024
            let e = d.Storage[i]

            if e.Kind = ElementKind.Tag then
                let tag = enum<Tag> e.B

                if
                    tag = Tag.StartGroup
                    || tag = Tag.StartConditionalGroup
                    || tag = Tag.StartAlternative
                    || tag = Tag.StartIndent
                    || tag = Tag.StartForceFlat
                    || tag = Tag.StartAlwaysFits
                    || tag = Tag.StartIfBreak
                then
                    depth <- depth + 1
                elif tag = Tag.Else then
                    if depth = 1 then
                        middle <- i
                else
                    depth <- depth - 1

            i <- i + 1

        struct (i - 1, middle)

    member private this.FlatPrefixVisit
        (d: DocumentBuffer, first: int, finish: int, work: byref<int>, valid: byref<bool>)
        =
        let mutable i = first

        while valid && i < finish do
            work <- work + 1
            valid <- work <= 1024
            let e = d.Storage[i]

            if e.Kind = ElementKind.Shared then
                this.FlatPrefixVisit(d, e.A, e.A + e.B, &work, &valid)
            elif e.Kind = ElementKind.Tag then
                let tag = enum<Tag> e.B

                if tag = Tag.StartConditionalGroup then
                    let struct (close, _) = this.FlatPrefixEnding(d, i, finish, &work, &valid)

                    let struct (alternative, _) =
                        this.FlatPrefixEnding(d, i + 1, close, &work, &valid)

                    this.FlatPrefixVisit(d, i + 2, alternative, &work, &valid)
                    i <- close
                elif tag = Tag.StartIfBreak then
                    let struct (close, middle) = this.FlatPrefixEnding(d, i, finish, &work, &valid)

                    if middle >= 0 then
                        this.FlatPrefixVisit(d, middle + 1, close, &work, &valid)

                    i <- close
                elif tag = Tag.StartGroup && e.Flags &&& ElementFlags.Break <> 0uy then
                    valid <- false
            elif e.Kind = ElementKind.BreakParent then
                valid <- false
            elif e.Kind = ElementKind.Line && e.A >= int LineKind.Hard then
                valid <- false
            else
                flatPrefixElements.Add i

            i <- i + 1

    member private this.FlatPrefix(d: DocumentBuffer, start: int, length: int) =
        flatPrefixElements.Clear()
        let mutable work = 0
        let mutable valid = true
        this.FlatPrefixVisit(d, start, start + length, &work, &valid)
        valid

    member private _.HasUnabsorbedBreak(d: DocumentBuffer, start: int, length: int) =
        let mutable requiredBreak = false
        let mutable absorbed = 0
        let mutable i = start

        while not requiredBreak && i < start + length do
            let e = d.Storage[i]

            if e.Kind = ElementKind.Tag then
                match enum<Tag> e.B with
                | Tag.StartConditionalGroup
                | Tag.StartForceFlat
                | Tag.StartAlwaysFits -> absorbed <- absorbed + 1
                | Tag.EndConditionalGroup
                | Tag.EndForceFlat
                | Tag.EndAlwaysFits -> absorbed <- absorbed - 1
                | Tag.StartGroup when absorbed = 0 ->
                    requiredBreak <- e.Flags &&& ElementFlags.Break <> 0uy
                | _ -> ()
            elif absorbed = 0 then
                requiredBreak <-
                    e.Kind = ElementKind.BreakParent
                    || (e.Kind = ElementKind.Line
                        && e.A >= int LineKind.Hard
                        && e.Flags &&& ElementFlags.SkipBreakIfFirst = 0uy)

            i <- i + 1

        requiredBreak

    member private this.ChainedAssignment(children: IntSlice, d: DocumentBuffer) =
        let inline head () =
            this.Emit(children[0], d)
            this.Space d
            this.Emit(children[1], d)

        let tail = this.Children children[2]

        if this.Kind tail[2] <> NodeKind.SimpleAssignmentExpression then
            let id = d.NewGroupId()
            d.AddTag(Tag.StartConditionalGroup, id)
            d.AddTag Tag.StartAlternative
            let headStart = d.Count
            head ()
            let headLength = d.Count - headStart
            this.Space d
            let tailStart = d.Count
            this.Emit(children[2], d)
            let tailLength = d.Count - tailStart
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.StartAlternative
            d.AddShared(headStart, headLength)
            this.Space d
            d.AddShared(tailStart, tailLength)
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.StartAlternative
            d.AddShared(headStart, headLength)
            d.AddTag Tag.StartIndent
            this.Hard d
            d.AddShared(tailStart, tailLength)
            d.AddTag Tag.EndIndent
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.EndConditionalGroup

            let assign = this.Parent children[0]
            let outer = if assign >= 0 then this.Parent assign else -1
            let outerKind = this.Kind outer

            if
                outerKind <> NodeKind.ExpressionStatement
                && outerKind <> NodeKind.EqualsValueClause
                && this.HasUnabsorbedBreak(d, tailStart, tailLength)
            then
                d.AddBreakParent()
        else
            d.StartGroup() |> ignore
            head ()
            d.AddTag Tag.StartIndent
            let mutable current = children[2]

            while this.Kind current = NodeKind.SimpleAssignmentExpression do
                let assignment = this.Children current
                d.AddLine LineKind.Normal
                this.Emit(assignment[0], d)
                this.Space d
                this.Emit(assignment[1], d)
                current <- assignment[2]

            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal
            this.Emit(current, d)
            d.AddTag Tag.EndIndent
            d.AddTag Tag.EndIndent
            d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IsCastHead(rhs: int) =
        let c = this.Children rhs
        let operand = this.Kind(this.WithoutNullForgiving c[c.Length - 1])
        let generic = this.ContainsLessThan c[1]

        (not generic
         || this.Kind c[1] = NodeKind.FunctionPointerType
         || this.Kind c[1] = NodeKind.TupleType
         || this.Kind c[1] = NodeKind.ArrayType)
        && (operand <> NodeKind.IdentifierName
            || (this.Kind c[1] = NodeKind.TupleType
                && this.Kind c[c.Length - 1] = NodeKind.SuppressNullableWarningExpression))
        && operand <> NodeKind.CastExpression

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.IsExpandableGeneric(node: int) =
        node >= 0
        && this.ContainsLessThan node
        && not (this.UnbreakableGenericType node)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IsGenericTypeMember(rhs: int) =
        let members = this.Children rhs
        let receiver = members[0]

        let typ =
            if this.Kind receiver = NodeKind.ObjectCreationExpression then
                let creation = this.Children receiver
                creation[1]
            elif this.Kind receiver = NodeKind.GenericName then
                receiver
            else
                -1

        this.IsExpandableGeneric typ

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ClassifyMemberChain(memberHead: int) =
        let mutable cur = memberHead
        let mutable links = 0
        let mutable hasExpandableGeneric = false

        while SyntaxFacts.memberAccess (this.Kind cur) do
            let rc = this.Children cur

            if rc.Length = 0 then
                cur <- -1
            else
                links <- links + 1
                let memberNode = rc[rc.Length - 1]

                if
                    this.Kind memberNode = NodeKind.GenericName
                    && this.IsExpandableGeneric memberNode
                then
                    hasExpandableGeneric <- true

                let unwrapped = this.WithoutNullForgiving rc[0]
                let uk = this.Kind unwrapped

                cur <-
                    if
                        SyntaxFacts.memberAccess uk
                        || uk = NodeKind.InvocationExpression
                        || uk = NodeKind.ElementAccessExpression
                        || uk = NodeKind.ConditionalAccessExpression
                        || uk = NodeKind.ParenthesizedExpression
                    then
                        unwrapped
                    else
                        rc[0]

        let recvKind = this.Kind cur

        let isIdentifierOrKeywordRoot =
            recvKind = NodeKind.ThisExpression
            || recvKind = NodeKind.BaseExpression
            || recvKind = NodeKind.PredefinedType

        let plainRoot = isIdentifierOrKeywordRoot || recvKind = NodeKind.IdentifierName

        let mergedRoot =
            isIdentifierOrKeywordRoot
            || (recvKind = NodeKind.IdentifierName && treeTokens[this.First cur].Length <= 4)

        struct (links, recvKind, plainRoot, mergedRoot, hasExpandableGeneric)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IsFixedMemberChain(memberHead: int) =
        let struct (links, recvKind, _, mergedRoot, hasExpandableGeneric) =
            this.ClassifyMemberChain memberHead

        recvKind = NodeKind.InvocationExpression
        || recvKind = NodeKind.ElementAccessExpression
        || recvKind = NodeKind.ConditionalAccessExpression
        || links > 2
        || (links = 2 && (hasExpandableGeneric || not mergedRoot))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ShouldFlattenAssignmentMember(rhs: int, kind: NodeKind, memberHead: int) =
        if SyntaxFacts.memberAccess kind then
            not (this.IsGenericTypeMember rhs)
        elif SyntaxFacts.memberAccess (this.Kind memberHead) then
            let struct (links, _, plainRoot, mergedRoot, hasExpandableGeneric) =
                this.ClassifyMemberChain memberHead

            not hasExpandableGeneric
            && ((links = 1 && plainRoot) || (links = 2 && mergedRoot))
        else
            false

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.AssignmentCall
        (rhs: int, kind: NodeKind, parent: int, usingInvocation: bool, d: DocumentBuffer)
        =
        let mutable requiredBreak = false
        let rhsChildren = this.Children rhs

        let emptyCreation =
            (kind = NodeKind.ObjectCreationExpression
             || kind = NodeKind.ImplicitObjectCreationExpression)
            && (let idx = this.SliceFindKind(rhsChildren, NodeKind.ArgumentList) in
                idx >= 0 && this.ChildCount rhsChildren[idx] = 2)
            && not (this.SliceContainsInitializer rhsChildren)

        let returnedChain =
            this.Kind parent = NodeKind.SimpleAssignmentExpression
            && let outer = (tree.Node parent).Parent in

               this.Kind outer = NodeKind.SimpleAssignmentExpression
               && this.Kind (tree.Node outer).Parent = NodeKind.ReturnStatement

        let detachFirst =
            emptyCreation
            || returnedChain
            || (kind = NodeKind.StackAllocArrayCreationExpression
                && not (this.SliceContainsInitializer rhsChildren))

        let id = d.NewGroupId()
        d.AddTag(Tag.StartConditionalGroup, id)
        d.AddTag Tag.StartAlternative
        this.Space d

        if detachFirst then
            d.AddTag Tag.StartForceFlat

        let start = d.Count
        this.Emit(rhs, d)
        let length = d.Count - start

        if usingInvocation || this.Kind parent = NodeKind.SimpleAssignmentExpression then
            requiredBreak <- this.HasUnabsorbedBreak(d, start, length)

        if detachFirst then
            d.AddTag Tag.EndForceFlat

        d.AddTag Tag.EndAlternative

        if not detachFirst then
            d.AddTag Tag.StartAlternative
            this.Space d
            d.AddShared(start, length)
            d.AddTag Tag.EndAlternative

        d.AddTag Tag.StartAlternative
        d.AddTag Tag.StartIndent
        this.Hard d
        d.AddShared(start, length)
        d.AddTag Tag.EndIndent
        d.AddTag Tag.EndAlternative
        d.AddTag Tag.EndConditionalGroup

        if requiredBreak then
            d.AddBreakParent()

    member private this.Assignment(children: IntSlice, d: DocumentBuffer, prefix: bool) =
        let rhs = children[children.Length - 1]
        let kind = this.Kind rhs

        if
            kind = NodeKind.IdentifierName
            || kind = NodeKind.NumericLiteralExpression
            || kind = NodeKind.TrueLiteralExpression
            || kind = NodeKind.FalseLiteralExpression
            || kind = NodeKind.NullLiteralExpression
            || SyntaxFacts.binary kind
        then
            d.StartGroup() |> ignore

            if prefix then
                this.All(children.SliceRange(0, children.Length - 2), d)
            else
                this.Emit(children[0], d)
                this.Space d
                this.Emit(children[1], d)

            if not prefix then
                d.StartGroup() |> ignore

            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal

            if SyntaxFacts.binary kind then
                this.Binary(rhs, d, false)
            else
                this.Emit(rhs, d)

            d.AddTag Tag.EndIndent

            if not prefix then
                d.EndGroup()

            d.EndGroup()
        else
            this.AssignmentOther(children, rhs, kind, d, prefix)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ClassifyAssignment
        (
            children: IntSlice,
            rhs: int,
            kind: NodeKind,
            prefix: bool,
            parentOut: outref<int>,
            usingInvocationOut: outref<bool>,
            rawOut: outref<bool>,
            noIndentOut: outref<bool>
        ) : int =
        let parent = if rhs >= 0 then this.Parent rhs else -1
        let parentKind = this.Kind parent
        let parentParent = if parent >= 0 then this.Parent parent else -1
        let parentParentKind = this.Kind parentParent

        let propertyInitializer =
            parentKind = NodeKind.EqualsValueClause
            && parentParentKind = NodeKind.PropertyDeclaration

        let listValue =
            parentKind = NodeKind.EqualsValueClause
            && (parentParentKind = NodeKind.EnumMemberDeclaration
                || parentParentKind = NodeKind.Parameter)

        let genericDeclaration =
            if prefix && parentKind = NodeKind.EqualsValueClause then
                let declaration = this.Parent parentParent

                if this.Kind declaration = NodeKind.VariableDeclaration then
                    let variables = this.Children declaration
                    this.ContainsLessThan variables[0]
                else
                    false
            else
                false

        let usingHeader =
            let mutable owner = parent

            while this.Kind owner = NodeKind.EqualsValueClause
                  || this.Kind owner = NodeKind.VariableDeclarator
                  || this.Kind owner = NodeKind.VariableDeclaration do
                owner <- this.Parent owner

            this.Kind owner = NodeKind.UsingStatement

        let castHead = kind = NodeKind.CastExpression && this.IsCastHead rhs

        let deconstruction =
            not prefix
            && (this.Kind children[0] = NodeKind.TupleExpression
                || (this.Kind children[0] = NodeKind.DeclarationExpression
                    && this.HasChildOfKind(children[0], NodeKind.ParenthesizedVariableDesignation)))

        let memberHead = this.WithoutNullForgiving rhs
        let memberKind = this.Kind memberHead

        let hug =
            kind = NodeKind.ImplicitArrayCreationExpression
            || (kind = NodeKind.CollectionExpression
                && not prefix
                && this.TokenKind children[1] <> TokenKind.EqualsToken)
            || kind = NodeKind.ImplicitStackAllocArrayCreationExpression
            || (kind = NodeKind.SwitchExpression && not deconstruction)
            || memberKind = NodeKind.ParenthesizedExpression
            || kind = NodeKind.TupleExpression
            || (((kind >= NodeKind.UnaryPlusExpression && kind <= NodeKind.AddressOfExpression)
                 || kind = NodeKind.IndexExpression)
                && let c = this.Children rhs in
                   c.Length = 2 && this.Kind c[1] = NodeKind.ParenthesizedExpression)
            || kind = NodeKind.CheckedExpression
            || kind = NodeKind.UncheckedExpression
            || (kind = NodeKind.DefaultExpression
                && this.ContainsLessThan rhs
                && not (this.UnbreakableGenericType rhs))

        let raw =
            ((kind = NodeKind.StringLiteralExpression
              || kind = NodeKind.Utf8StringLiteralExpression)
             && let token = tree.Token(this.First rhs) in

                token.Kind = TokenKind.MultiLineRawStringLiteralToken
                || token.Kind = TokenKind.Utf8MultiLineRawStringLiteralToken)
            || (kind = NodeKind.InterpolatedStringExpression
                && (tree.Token(this.First rhs)).Kind =
                    TokenKind.InterpolatedMultiLineRawStringStartToken)

        let conditionalChain =
            kind = NodeKind.ConditionalExpression
            && let c = this.Children rhs in
               c.Length = 5 && this.Kind c[4] = NodeKind.ConditionalExpression

        let breakBeforeCondition =
            kind = NodeKind.ConditionalExpression
            && let c = this.Children rhs in

               c.Length = 5
               && (SyntaxFacts.binary (this.Kind c[0])
                   || this.Kind c[0] = NodeKind.ParenthesizedExpression)

        let multilineVerbatim =
            (kind = NodeKind.StringLiteralExpression
             || kind = NodeKind.InterpolatedStringExpression)
            && let token = tree.Token(this.First rhs) in

               ((kind = NodeKind.StringLiteralExpression
                 && token.Length > 1
                 && source[token.Start] = '@')
                || token.Kind = TokenKind.InterpolatedVerbatimStringStartToken)
               && let struct (start, length) = tree.SourceSpan rhs in

                  source.AsSpan(start, length).IndexOfAny(SyntaxFacts.lineTerminators) >= 0

        let genericTypeMember =
            SyntaxFacts.memberAccess kind && this.IsGenericTypeMember rhs

        let fixedMemberReceiver =
            not propertyInitializer
            && not listValue
            && SyntaxFacts.memberAccess memberKind
            && this.IsFixedMemberChain memberHead

        let fixedHead =
            (kind = NodeKind.ConditionalExpression
             && not propertyInitializer
             && not conditionalChain
             && not breakBeforeCondition)
            || (kind = NodeKind.CastExpression
                && let c = this.Children rhs in
                   c.Length > 0 && this.Kind c[c.Length - 1] = NodeKind.CastExpression)
            || kind = NodeKind.WithExpression
            || (genericTypeMember && not genericDeclaration)
            || SyntaxFacts.assignment kind
            || (SyntaxFacts.memberAccess memberKind
                && let c = this.Children memberHead in
                   c.Length > 0 && this.Kind c[0] = NodeKind.ParenthesizedExpression)
            || fixedMemberReceiver
            || SyntaxFacts.lambda kind
            || kind = NodeKind.AnonymousMethodExpression
            || raw

        let noIndent = kind = NodeKind.CollectionExpression || SyntaxFacts.initializer kind

        let call =
            let mutable operand = memberHead

            if memberKind = NodeKind.RefExpression then
                let c = this.Children operand
                operand <- this.WithoutNullForgiving c[c.Length - 1]

            if
                this.Kind operand = NodeKind.LogicalNotExpression
                || this.Kind operand = NodeKind.UnaryMinusExpression
            then
                let c = this.Children operand
                operand <- this.WithoutNullForgiving c[c.Length - 1]

            let operandKind = this.Kind operand
            let mutable chainRoot = operand

            while SyntaxFacts.memberAccess (this.Kind chainRoot) do
                let c = this.Children chainRoot
                chainRoot <- this.WithoutNullForgiving c[0]

            let rootKind = this.Kind chainRoot

            operandKind = NodeKind.InvocationExpression
            || operandKind = NodeKind.ElementAccessExpression
            || operandKind = NodeKind.ConditionalAccessExpression
            || rootKind = NodeKind.ObjectCreationExpression
            || rootKind = NodeKind.ImplicitObjectCreationExpression
            || rootKind = NodeKind.AnonymousObjectCreationExpression
            || rootKind = NodeKind.ArrayCreationExpression
            || rootKind = NodeKind.ImplicitArrayCreationExpression
            || rootKind = NodeKind.StackAllocArrayCreationExpression
            || (kind = NodeKind.SwitchExpression && deconstruction)
            || kind = NodeKind.AwaitExpression
            || castHead

        let usingInvocation =
            usingHeader
            && this.Kind(this.WithoutNullForgiving rhs) = NodeKind.InvocationExpression

        parentOut <- parent
        usingInvocationOut <- usingInvocation
        rawOut <- raw
        noIndentOut <- noIndent

        if
            ((hug
              && (not genericDeclaration
                  || this.Kind(this.WithoutNullForgiving rhs) = NodeKind.ParenthesizedExpression
                  || kind = NodeKind.ArrayCreationExpression
                  || kind = NodeKind.ImplicitArrayCreationExpression
                  || kind = NodeKind.StackAllocArrayCreationExpression
                  || kind = NodeKind.ImplicitStackAllocArrayCreationExpression))
             || (call && ((usingHeader && not usingInvocation) || listValue)))
            && not propertyInitializer
        then
            1
        elif call && not propertyInitializer then
            2
        elif fixedHead then
            3
        elif multilineVerbatim then
            4
        else
            0

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.AssignmentOther
        (children: IntSlice, rhs: int, kind: NodeKind, d: DocumentBuffer, prefix: bool)
        =
        let mutable parent = -1
        let mutable usingInvocation = false
        let mutable raw = false
        let mutable noIndent = false

        let mode =
            this.ClassifyAssignment(
                children,
                rhs,
                kind,
                prefix,
                &parent,
                &usingInvocation,
                &raw,
                &noIndent
            )

        d.StartGroup() |> ignore

        let memberHead = this.WithoutNullForgiving rhs

        if prefix then
            this.All(children.SliceRange(0, children.Length - 2), d)
        else
            this.Emit(children[0], d)
            this.Space d
            this.Emit(children[1], d)

        match mode with
        | 1 ->
            this.Space d
            this.Emit(rhs, d)
        | 2 -> this.AssignmentCall(rhs, kind, parent, usingInvocation, d)
        | 3 ->
            if raw then
                this.Space d
                d.AddTag Tag.StartIndent
                this.Emit(rhs, d)
                d.AddTag Tag.EndIndent
            elif
                (kind = NodeKind.ConditionalExpression
                 || SyntaxFacts.lambda kind
                 || kind = NodeKind.AnonymousMethodExpression
                 || SyntaxFacts.memberAccess (this.Kind(this.WithoutNullForgiving rhs)))
            then
                let id = d.NewGroupId()
                d.AddTag(Tag.StartConditionalGroup, id)
                d.AddTag Tag.StartAlternative
                this.Space d
                let start = d.Count
                let breakBefore = d.ConditionalBreakCount()
                this.Emit(rhs, d)
                let length = d.Count - start
                let hasUnconditionalBreak = d.ConditionalBreakCount() <> breakBefore
                d.AddTag Tag.EndAlternative
                d.AddTag Tag.StartAlternative
                this.Space d
                d.AddShared(start, length)
                d.AddTag Tag.EndAlternative
                d.AddTag Tag.StartAlternative
                d.AddTag Tag.StartIndent
                this.Hard d
                d.AddShared(start, length)
                d.AddTag Tag.EndIndent
                d.AddTag Tag.EndAlternative
                d.AddTag Tag.EndConditionalGroup

                if hasUnconditionalBreak then
                    d.AddBreakParent()
            else
                this.Space d
                this.Emit(rhs, d)
        | 4 ->
            d.AddTag Tag.StartIndent
            this.Hard d
            this.Emit(rhs, d)
            d.AddTag Tag.EndIndent
        | _ ->
            if not noIndent && not prefix then
                d.StartGroup() |> ignore

            if not noIndent then
                d.AddTag Tag.StartIndent

            d.AddLine LineKind.Normal

            if noIndent then
                this.Emit(rhs, d)
            elif SyntaxFacts.binary kind then
                this.Binary(rhs, d, false)
            elif this.ShouldFlattenAssignmentMember(rhs, kind, memberHead) then
                d.AddTag Tag.StartForceFlat
                this.Emit(rhs, d)
                d.AddTag Tag.EndForceFlat
            else
                this.Emit(rhs, d)

            if not noIndent then
                d.AddTag Tag.EndIndent

            if not noIndent && not prefix then
                d.EndGroup()

        d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.InlineReturnCondition(n: int) =
        let c = this.Children n

        if
            this.Kind (tree.Node n).Parent = NodeKind.ReturnStatement
            && c.Length = 5
            && SyntaxFacts.binary (this.Kind c[0])
            && this.Kind c[4] <> NodeKind.ConditionalExpression
            && not (this.MultilineToken c[0])
        then
            let mutable inlineHead = true

            for token = this.First c[0] to this.Last c[0] do
                if
                    (tree.Token token).Kind = TokenKind.OpenBraceToken
                    || this.HasTrivia(token, true)
                    || this.HasTrivia(token, false)
                then
                    inlineHead <- false

            inlineHead
        else
            false

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TernaryChain(n: int, c: IntSlice, d: DocumentBuffer) =
        let inline link (cc: IntSlice) =
            d.StartGroup() |> ignore

            if this.Kind cc[0] = NodeKind.ParenthesizedExpression then
                this.Delimited(this.Children cc[0], d, false, false, false)
            elif SyntaxFacts.binary (this.Kind cc[0]) then
                this.Binary(cc[0], d, false)
            else
                this.Emit(cc[0], d)

            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal
            this.Emit(cc[1], d)
            this.Space d
            this.Emit(cc[2], d)
            d.AddTag Tag.EndIndent
            d.EndGroup()

        d.StartGroup() |> ignore

        let inline rest startNode startColon =
            let mutable currNode = startNode
            let mutable currColon = startColon
            let mutable cont = true

            while cont do
                this.Hard d
                this.Emit(currColon, d)
                this.Space d
                let cc = this.Children currNode
                link cc

                if this.Kind cc[4] = NodeKind.ConditionalExpression then
                    currNode <- cc[4]
                    currColon <- cc[3]
                else
                    this.Hard d
                    this.Emit(cc[3], d)
                    this.Space d
                    this.Emit(cc[4], d)
                    cont <- false

        let inline body () =
            link c
            let argument = (tree.Node n).Parent
            let arguments = if argument >= 0 then (tree.Node argument).Parent else -1
            let argumentChildren = this.Children arguments

            if
                this.Kind argument = NodeKind.Argument
                && this.Kind arguments = NodeKind.ArgumentList
                && argumentChildren.Length > 3
            then
                d.AddTag Tag.StartIndent
                rest c[4] c[3]
                d.AddTag Tag.EndIndent
            else
                rest c[4] c[3]

        if
            this.Kind (tree.Node n).Parent = NodeKind.ReturnStatement
            && not (SyntaxFacts.binary (this.Kind c[0]))
        then
            d.AddTag Tag.StartIndent
            body ()
            d.AddTag Tag.EndIndent
        else
            body ()

        d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.TernaryInlineReturn(c: IntSlice, d: DocumentBuffer) =
        let mutable conditionStart, conditionLength, branchStart, branchLength = 0, 0, 0, 0

        let id = d.NewGroupId()
        d.AddTag(Tag.StartConditionalGroup, id)

        for alternative = 0 to 2 do
            d.AddTag Tag.StartAlternative

            if alternative < 2 then
                this.Space d

            d.AddTag Tag.StartIndent

            if alternative = 2 then
                this.Hard d

            d.StartGroup() |> ignore

            if alternative < 2 then
                d.AddTag Tag.StartForceFlat

            if alternative = 0 then
                conditionStart <- d.Count

                if SyntaxFacts.binary (this.Kind c[0]) then
                    this.Binary(c[0], d, false)
                else
                    this.Emit(c[0], d)

                conditionLength <- d.Count - conditionStart
            else
                d.AddShared(conditionStart, conditionLength)

            if alternative < 2 then
                d.AddTag Tag.EndForceFlat

            if alternative = 0 then
                branchStart <- d.Count
                d.AddLine LineKind.Normal
                this.Emit(c[1], d)
                this.Space d
                this.Emit(c[2], d)
                d.AddLine LineKind.Normal
                this.Emit(c[3], d)
                this.Space d
                this.Emit(c[4], d)
                branchLength <- d.Count - branchStart
            else
                d.AddShared(branchStart, branchLength)

            d.EndGroup()
            d.AddTag Tag.EndIndent
            d.AddTag Tag.EndAlternative

        d.AddTag Tag.EndConditionalGroup

    member private this.Ternary(n: int, d: DocumentBuffer) =
        this.EnsureStack()
        let c = this.Children n

        if c.Length <> 5 then
            this.Spaced(c, d)
        elif
            this.Kind c[4] = NodeKind.ConditionalExpression
            && this.Kind c[2] <> NodeKind.ConditionalExpression
        then
            this.TernaryChain(n, c, d)
        elif this.InlineReturnCondition n then
            this.TernaryInlineReturn(c, d)
        else
            d.StartGroup() |> ignore

            if SyntaxFacts.binary (this.Kind c[0]) then
                this.Binary(c[0], d, false)
            else
                this.Emit(c[0], d)

            let returnBinary =
                this.Kind (tree.Node n).Parent = NodeKind.ReturnStatement
                && SyntaxFacts.binary (this.Kind c[0])

            if not returnBinary then
                d.AddTag Tag.StartIndent

            d.AddLine LineKind.Normal
            this.Emit(c[1], d)
            this.Space d
            this.Emit(c[2], d)
            d.AddLine LineKind.Normal
            this.Emit(c[3], d)
            this.Space d
            this.Emit(c[4], d)

            if not returnBinary then
                d.AddTag Tag.EndIndent

            d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ExpandedBlockLambda(n: int) =
        SyntaxFacts.lambda (this.Kind n)
        && let children = this.Children n in
           let body = children[children.Length - 1] in

           this.Kind body = NodeKind.Block
           && (let block = this.Children body in

               block.Length > 2
               || this.HasTrivia(this.First block[0], false)
               || this.HasTrivia(this.First block[block.Length - 1], true))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.CallWithExpandedBlockLambda(n: int) =
        let call =
            if this.Kind n = NodeKind.AwaitExpression then
                let children = this.Children n
                children[children.Length - 1]
            else
                n

        if this.Kind call <> NodeKind.InvocationExpression then
            false
        else
            let children = this.Children call
            let arguments = this.Children children[children.Length - 1]
            let mutable found = false
            let mutable i = 0

            while not found && i < arguments.Length do
                let argument = arguments[i]

                if this.Kind argument = NodeKind.Argument then
                    let argChildren = this.Children argument
                    let mutable j = 0

                    while not found && j < argChildren.Length do
                        found <- this.ExpandedBlockLambda argChildren[j]
                        j <- j + 1

                i <- i + 1

            found

    member private this.CallWithInitializedCreation(n: int) =
        let kind = this.Kind n

        (kind = NodeKind.AwaitExpression || kind = NodeKind.InvocationExpression)
        && this.ContainsInitializedCreation n

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ContainsInitializedCreation(n: int) =
        if n < 0 then
            false
        elif uint32 n < uint32 initializedCreations.Length && initializedCreations[n] <> 0uy then
            initializedCreations[n] = 2uy
        else
            initScanStack.Clear()
            initScanStack.Add(struct (n, 0))
            let mutable lastResult = false

            while initScanStack.Count > 0 do
                let topIdx = initScanStack.Count - 1
                let struct (cur, i) = initScanStack[topIdx]
                let curKind = this.Kind cur

                if curKind = NodeKind.AnonymousObjectCreationExpression then
                    let curChildren = this.Children cur
                    let found = curChildren.Length > 3

                    if uint32 cur < uint32 initializedCreations.Length then
                        initializedCreations[cur] <- if found then 2uy else 1uy

                    lastResult <- found
                    initScanStack.RemoveAt topIdx
                elif curKind = NodeKind.Block || curKind = NodeKind.AnonymousMethodExpression then
                    if uint32 cur < uint32 initializedCreations.Length then
                        initializedCreations[cur] <- 1uy

                    lastResult <- false
                    initScanStack.RemoveAt topIdx
                elif i > 0 && lastResult then
                    if uint32 cur < uint32 initializedCreations.Length then
                        initializedCreations[cur] <- 2uy

                    lastResult <- true
                    initScanStack.RemoveAt topIdx
                else
                    let children = this.Children cur

                    let creation =
                        curKind = NodeKind.ObjectCreationExpression
                        || curKind = NodeKind.ImplicitObjectCreationExpression

                    let mutable pushed = false
                    let mutable foundHere = false
                    let mutable idx = i

                    while not pushed && not foundHere && idx < children.Length do
                        let child = children[idx]
                        idx <- idx + 1

                        if child > 0 then
                            if creation && SyntaxFacts.initializer (this.Kind child) then
                                let init = this.Children child

                                foundHere <-
                                    init.Length > 2
                                    || (init.Length = 2
                                        && (let firstTok = this.First init[0]
                                            let secondTok = this.First init[1]

                                            this.HasTrivia(firstTok, false)
                                            || this.HasTrivia(secondTok, true)))
                            elif
                                uint32 child < uint32 initializedCreations.Length
                                && initializedCreations[child] <> 0uy
                            then
                                foundHere <- initializedCreations[child] = 2uy
                            else
                                let childKind = this.Kind child

                                if childKind = NodeKind.AnonymousObjectCreationExpression then
                                    let childChildren = this.Children child
                                    let childFound = childChildren.Length > 3

                                    if uint32 child < uint32 initializedCreations.Length then
                                        initializedCreations[child] <-
                                            if childFound then 2uy else 1uy

                                    foundHere <- childFound
                                elif
                                    childKind = NodeKind.Block
                                    || childKind = NodeKind.AnonymousMethodExpression
                                then
                                    if uint32 child < uint32 initializedCreations.Length then
                                        initializedCreations[child] <- 1uy
                                else
                                    initScanStack[topIdx] <- struct (cur, idx)
                                    initScanStack.Add(struct (child, 0))
                                    pushed <- true

                    if foundHere then
                        if uint32 cur < uint32 initializedCreations.Length then
                            initializedCreations[cur] <- 2uy

                        lastResult <- true
                        initScanStack.RemoveAt topIdx
                    elif not pushed then
                        if uint32 cur < uint32 initializedCreations.Length then
                            initializedCreations[cur] <- 1uy

                        lastResult <- false
                        initScanStack.RemoveAt topIdx

            initScanStack.Clear()

            if initScanStack.Capacity > 4096 then
                initScanStack.TrimExcess()

            lastResult

    member private this.LambdaContainsInitializedCreation(lambda: int) =
        if lambda >= 0 then
            let c = this.Children lambda
            this.ContainsInitializedCreation c[c.Length - 1]
        else
            false

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.EmitLambdaAnonymousObjectBody
        (
            head: IntSlice,
            argument: int,
            argumentList: int,
            body: int,
            expandedStart: byref<int>,
            expandedLength: byref<int>,
            d: DocumentBuffer
        ) =
        if
            this.Kind(this.Parent body) = NodeKind.ParenthesizedLambdaExpression
            && this.ChildCount body > 3
            && argument >= 0
            && argumentList >= 0
            && this.Kind argument = NodeKind.Argument
            && (this.Kind argumentList = NodeKind.ArgumentList
                || this.Kind argumentList = NodeKind.TupleExpression)
            && this.ChildCount argumentList > 3
        then
            expandedStart <- d.Count
            d.AddTag Tag.StartIndent
            this.Hard d
            this.Emit(body, d)
            d.AddTag Tag.EndIndent
            expandedLength <- d.Count - expandedStart
        else
            let id = d.NewGroupId()
            d.AddTag(Tag.StartConditionalGroup, id)
            d.AddTag Tag.StartAlternative
            this.Space d

            let staticLambda =
                if this.SliceContainsToken(head, TokenKind.StaticKeyword) then
                    let args = this.Children argumentList
                    let mutable otherLambda = false
                    let mutable i = 0

                    while not otherLambda && i < args.Length do
                        let child = args[i]

                        if
                            child >= 0 && child <> argument && this.Kind child = NodeKind.Argument
                        then
                            let argChildren = this.Children child
                            let mutable j = 0

                            while not otherLambda && j < argChildren.Length do
                                otherLambda <- SyntaxFacts.lambda (this.Kind argChildren[j])
                                j <- j + 1

                        i <- i + 1

                    otherLambda
                else
                    false

            if staticLambda then
                d.AddTag Tag.StartForceFlat

            d.AddTag Tag.StartIndent
            let start = d.Count
            this.Emit(body, d)
            let length = d.Count - start
            d.AddTag Tag.EndIndent

            if staticLambda then
                d.AddTag Tag.EndForceFlat

            d.AddTag Tag.EndAlternative
            d.AddTag Tag.StartAlternative
            expandedStart <- d.Count
            d.AddTag Tag.StartIndent
            this.Hard d
            d.AddShared(start, length)
            d.AddTag Tag.EndIndent
            expandedLength <- d.Count - expandedStart
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.EndConditionalGroup

    member private this.Lambda(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let body = c[c.Length - 1]
        lambdaVisits <- lambdaVisits + 1
        let head = c.SliceRange(0, c.Length - 3)
        let argument = this.Parent n
        let argumentList = if argument >= 0 then this.Parent argument else -1

        let trailingLambda =
            this.Kind argument = NodeKind.Argument
            && (this.Kind argumentList = NodeKind.ArgumentList
                || this.Kind argumentList = NodeKind.TupleExpression)
            && let arguments = this.Children argumentList in arguments.Length > 3

        let flatParameters =
            if
                trailingLambda
                && head.Length > 0
                && this.Kind head[head.Length - 1] = NodeKind.ParameterList
            then
                let arguments = this.Children argumentList
                let mutable trivia = false

                for token = this.First head[0] to this.Last head[head.Length - 1] do
                    if this.HasTrivia(token, true) || this.HasTrivia(token, false) then
                        trivia <- true

                arguments[arguments.Length - 2] = argument && not trivia
            else
                false

        if flatParameters then
            d.AddTag Tag.StartForceFlat

        if
            head.Length > 1
            && this.Kind head[head.Length - 1] = NodeKind.ParameterList
            && head[head.Length - 2] >= 0
        then
            this.Spaced(head.SliceRange(0, head.Length - 2), d)
            this.Space d
            this.Emit(head[head.Length - 1], d)
        else
            this.Spaced(head, d)

        if flatParameters then
            d.AddTag Tag.EndForceFlat

        this.Space d
        let arrow = this.First c[c.Length - 2]
        let token = tree.Token arrow

        let mutable blockComment = false
        let mutable otherTrivia = false

        for i = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                          + token.LeadingCount
                                                          + token.TrailingCount
                                                          - 1 do
            let kind = (tree.Trivia i).Kind

            if kind = TriviaKind.MultiLineCommentTrivia then
                blockComment <- true
            elif SyntaxFacts.comment kind || SyntaxFacts.directive kind then
                otherTrivia <- true

        if trailingLambda && blockComment && not otherTrivia then
            d.AddTag Tag.StartForceFlat
            this.Token(arrow, d, spaceBeforeComments = true)
            d.AddTag Tag.EndForceFlat
        else
            this.Emit(c[c.Length - 2], d)

        let bodyGroup = d.Count
        let mutable expandedStart, expandedLength = -1, 0

        d.StartGroup() |> ignore

        if this.Kind body = NodeKind.Block then
            this.Block(body, d, true)
        elif
            this.Kind body = NodeKind.AnonymousObjectCreationExpression
            && this.Kind n = NodeKind.ParenthesizedLambdaExpression
        then
            this.EmitLambdaAnonymousObjectBody(
                head,
                argument,
                argumentList,
                body,
                &expandedStart,
                &expandedLength,
                d
            )
        elif
            this.Kind body = NodeKind.AnonymousObjectCreationExpression
            || this.Kind body = NodeKind.ObjectCreationExpression
               && (this.Kind n = NodeKind.SimpleLambdaExpression
                   || this.SliceContainsInitializer(this.Children body))
        then
            this.Space d
            this.Emit(body, d)
        elif
            (this.Kind body = NodeKind.AwaitExpression
             && not (this.CallWithExpandedBlockLambda body)
             && not (this.CallWithInitializedCreation body))
            || (this.Kind body = NodeKind.InvocationExpression
                && (let children = this.Children body in
                    SyntaxFacts.memberAccess (this.Kind children[0]))
                && not (this.MultilineToken body)
                && (let first = tree.Token(this.First body)
                    let last = tree.Token(this.Last body)
                    not (this.HeadHasTrivia(first.Start, last.End)))
                && not (this.CallWithExpandedBlockLambda body)
                && not (this.CallWithInitializedCreation body))
        then
            let id = d.NewGroupId()
            d.AddTag(Tag.StartConditionalGroup, id)
            d.AddTag Tag.StartAlternative
            this.Space d
            d.AddTag Tag.StartForceFlat
            let start = d.Count
            this.Emit(body, d)
            let length = d.Count - start
            d.AddTag Tag.EndForceFlat
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.StartAlternative
            expandedStart <- d.Count
            d.AddTag Tag.StartIndent
            this.Hard d
            d.AddShared(start, length)
            d.AddTag Tag.EndIndent
            expandedLength <- d.Count - expandedStart
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.EndConditionalGroup
        else
            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal

            if SyntaxFacts.binary (this.Kind body) then
                this.Binary(body, d, false)
            else
                this.Emit(body, d)

            d.AddTag Tag.EndIndent

        d.EndGroup()

        lastLambdaNode <- n
        lastLambdaBody <- struct (bodyGroup, d.Count, expandedStart, expandedLength)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.HasArgumentDirectives(c: IntSlice) =
        let tokens = tree.TokenSpan()
        let trivia = tree.TriviaSpan()
        let mutable found = false

        for idx = 1 to c.Length - 1 do
            let token = &tokens[this.First c[idx]]

            for i = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                if SyntaxFacts.directive trivia[i].Kind then
                    found <- true

        for idx = 0 to c.Length - 1 do
            let argument = c[idx]

            if argument >= 0 then
                let values = this.Children argument

                if
                    values.Length = 1
                    && (let vk = this.Kind values[0] in

                        vk = NodeKind.InvocationExpression
                        || vk = NodeKind.ConditionalAccessExpression
                        || SyntaxFacts.memberAccess vk)
                then
                    for t = this.First argument to this.Last argument do
                        let token = &tokens[t]

                        for i = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                            if SyntaxFacts.directive trivia[i].Kind then
                                found <- true

        found

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ArgumentsWithDirectives(n: int, c: IntSlice, d: DocumentBuffer) =
        let opening = tree.Token(this.First c[0])
        let first = tree.Token(this.First c[1])

        let chainDirective =
            let mutable found = false

            for idx = 0 to c.Length - 1 do
                let argument = c[idx]

                if argument >= 0 then
                    for t = this.First argument to this.Last argument do
                        if (tree.Token t).Kind = TokenKind.DotToken && this.HasTrivia(t, true) then
                            let token = tree.Token t

                            for i = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                                if SyntaxFacts.directive (tree.Trivia i).Kind then
                                    found <- true

            found

        let expanded =
            not chainDirective
            && source
                .AsSpan(opening.End, first.Start - opening.End)
                .IndexOfAny(SyntaxFacts.lineTerminators)
               >= 0

        let separator i =
            let previous = tree.Token(this.Last c[i - 1])
            let current = tree.Token(this.First c[i])
            let call = this.Parent n
            let returnedCall = this.Kind(this.Parent call) = NodeKind.ReturnStatement

            if
                (not chainDirective
                 && (i > 1 || not returnedCall)
                 && source
                     .AsSpan(previous.End, current.Start - previous.End)
                     .IndexOfAny(SyntaxFacts.lineTerminators)
                    >= 0)
                || (chainDirective
                    && i = c.Length - 1
                    && (tree.Token(this.Last c[i - 1])).Kind <> TokenKind.CloseParenToken)
                || (expanded && this.At(c[i - 1], TokenKind.CommaToken))
                || (expanded
                    && i = c.Length - 1
                    && this.Kind c[i - 1] = NodeKind.Argument
                    && (tree.Token(this.Last c[i - 1])).Kind = TokenKind.CloseParenToken)
            then
                this.Hard d
            elif this.At(c[i - 1], TokenKind.CommaToken) then
                this.Space d

        this.Emit(c[0], d)

        d.AddTag Tag.StartIndent

        for i = 1 to c.Length - 2 do
            separator i
            this.Emit(c[i], d)

        d.AddTag Tag.EndIndent

        separator (c.Length - 1)
        this.Emit(c[c.Length - 1], d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ArgumentsWithLambda
        (
            n: int,
            c: IntSlice,
            argCount: int,
            lastArg: int,
            lambda: int,
            multilineToken: bool,
            d: DocumentBuffer
        ) =
        let eligible = argCount > 1

        let multipleLambdas =
            if not eligible then
                false
            else
                let mutable found = false

                for i = 0 to c.Length - 1 do
                    let argument = c[i]

                    if not found && argument >= 0 && argument <> lastArg then
                        let children = this.Children argument

                        if
                            children.Length > 0
                            && SyntaxFacts.lambda (this.Kind children[children.Length - 1])
                        then
                            found <- true

                found

        let hasHeadTrivia =
            if eligible then
                let lc = this.Children lambda

                this.HeadHasTrivia(
                    (tree.Token(this.First lambda)).Start,
                    (tree.Token(this.First lc[lc.Length - 1])).Start
                )
            else
                false

        let emptyParameters =
            let lc = this.Children lambda
            let pIdx = this.SliceFindKind(lc, NodeKind.ParameterList)
            pIdx >= 0 && this.ChildCount lc[pIdx] = 2

        let mutable separatorTrivia = false

        if eligible then
            for token = this.First c[1] to this.First lambda - 1 do
                if this.HasTrivia(token, true) || this.HasTrivia(token, false) then
                    separatorTrivia <- true

        let onlyBlockTrivia =
            let lc = this.Children lambda
            let first = this.First lambda
            let finish = this.First lc[lc.Length - 1]
            let mutable line = false

            for token = first to finish do
                let t = tree.Token token

                for j = t.TriviaStart to t.TriviaStart + t.LeadingCount + t.TrailingCount - 1 do
                    let trivia = tree.Trivia j
                    let arrow = tree.Token(this.First lc[lc.Length - 2])

                    if
                        SyntaxFacts.directive trivia.Kind
                        || trivia.Kind = TriviaKind.SingleLineCommentTrivia
                        || trivia.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                        || SyntaxFacts.comment trivia.Kind && trivia.Start < arrow.End
                    then
                        line <- true

            not line

        let closeParen = this.First c[c.Length - 1]
        let closeToken = tree.Token closeParen
        let closeTrailingStart = closeToken.TriviaStart + closeToken.LeadingCount

        let delimiterTrivia =
            this.HasTrivia(this.First c[0], true)
            || this.HasTrivia(this.First c[0], false)
            || this.HasTrivia(closeParen, true)
            || (this.HasTrivia(closeParen, false)
                && not (this.DeclinedTrailing(closeTrailingStart, closeToken.TrailingCount)))

        let ignoredArgument =
            hasIgnores
            && (ignoredSingles.Contains((tree.Token(this.First lastArg)).Start)
                || this.IgnoreRange((tree.Token(this.First lambda)).Start) >= 0)

        let special =
            not multipleLambdas
            && not ignoredArgument
            && (not hasHeadTrivia || onlyBlockTrivia)
            && not separatorTrivia
            && not delimiterTrivia
            && (eligible
                || this.Kind lambda = NodeKind.SimpleLambdaExpression
                || emptyParameters)

        let soleBlock =
            argCount = 1
            && let children = this.Children lambda in
               this.Kind children[children.Length - 1] = NodeKind.Block

        let multiArgInitialized =
            argCount > 1 && this.LambdaContainsInitializedCreation lambda

        if not special || ((multilineToken || multiArgInitialized) && argCount > 1) then
            this.Delimited(c, d, false, false, multilineToken || multiArgInitialized)
        else
            let mutable lambdaStart = 0
            let conditionalTag = d.Count
            let id = d.NewGroupId()
            d.AddTag(Tag.StartConditionalGroup, id)

            d.AddTag Tag.StartAlternative
            this.Emit(c[0], d)
            let start = d.Count
            let rangesStart = delimitedRanges.Count
            let mutable argStart = start

            for i = 1 to c.Length - 2 do
                if this.At(c[i], TokenKind.CommaToken) then
                    this.Emit(c[i], d)
                    let afterComma = d.Count
                    delimitedRanges.Add(struct (argStart, afterComma - argStart))
                    let nextFirst = this.First c[i + 1]

                    if not (this.DeclinedLeading nextFirst) then
                        this.Trivia(nextFirst, true, d)

                    this.Space d
                    argStart <- if d.Count = afterComma + 1 then d.Count else afterComma
                else
                    if i = c.Length - 2 then
                        lambdaStart <- d.Count

                    this.Emit(c[i], d)

            if argStart < d.Count then
                delimitedRanges.Add(struct (argStart, d.Count - argStart))

            let rangeCount = delimitedRanges.Count - rangesStart

            let hasFlatPrefix =
                argCount = 2
                && this.Kind lambda = NodeKind.SimpleLambdaExpression
                && this.FlatPrefix(d, start, lambdaStart - start)

            if argCount = 1 && not soleBlock && lambda >= 0 && lastLambdaNode = lambda then
                let struct (bodyStart, _, _, _) = lastLambdaBody

                if d.Storage[bodyStart + 1].Kind <> ElementKind.StaticToken then
                    d.AddTag(Tag.StartIfBreak, d.Storage[bodyStart].A)
                    this.Hard d
                    d.AddTag Tag.Else
                    d.AddTag Tag.EndIfBreak

            this.Emit(c[c.Length - 1], d)
            d.AddTag Tag.EndAlternative

            let inline emitExpandedAlternative () =
                let expandedLambda =
                    if this.Kind lambda = NodeKind.ParenthesizedLambdaExpression then
                        let children = this.Children lambda

                        if
                            this.Kind children[children.Length - 1] =
                                NodeKind.AnonymousObjectCreationExpression
                            || (argCount = 1
                                && this.Kind children[children.Length - 1] =
                                    NodeKind.AwaitExpression
                                && not (
                                    this.CallWithExpandedBlockLambda children[children.Length - 1]
                                )
                                && not (
                                    this.CallWithInitializedCreation children[children.Length - 1]
                                ))
                        then
                            lambda
                        else
                            -1
                    else
                        -1

                this.DelimitedShared(c, d, rangesStart, rangeCount, expandedLambda)

            d.AddTag Tag.StartAlternative

            if
                lambda >= 0
                && lastLambdaNode = lambda
                && (this.CanReplayFlat(d, start, lambdaStart - start) || hasFlatPrefix)
            then
                this.Token(this.First c[0], d)

                if hasFlatPrefix then
                    for idx = 0 to flatPrefixElements.Count - 1 do
                        let index = flatPrefixElements[idx]
                        let e = d.Storage[index]

                        if e.Kind = ElementKind.Line then
                            if e.A = int LineKind.Normal then
                                this.Space d
                        else
                            d.Append(d, index, 1)
                else
                    this.ReplayFlat(d, start, lambdaStart - start)

                let struct (bodyStart, bodyEnd, expandedStart, expandedLength) = lastLambdaBody

                d.AddShared(lambdaStart, bodyStart - lambdaStart)

                if expandedStart >= 0 then
                    d.AddShared(expandedStart, expandedLength)
                else
                    d.AddShared(bodyStart + 1, bodyEnd - bodyStart - 2)

                if d.Storage[bodyStart + 1].Kind <> ElementKind.StaticToken then
                    this.Hard d

                this.Emit(c[c.Length - 1], d)
            else
                emitExpandedAlternative ()

            d.AddTag Tag.EndAlternative

            d.AddTag Tag.StartAlternative
            emitExpandedAlternative ()
            d.AddTag Tag.EndAlternative

            d.AddTag Tag.EndConditionalGroup

            if this.EarlyArgumentDemandsBreak(d, rangesStart, rangeCount) then
                let tag = d.Storage[conditionalTag]

                d.Storage[conditionalTag] <-
                    { tag with
                        Flags = tag.Flags ||| ElementFlags.Break
                    }

            delimitedRanges.RemoveRange(rangesStart, rangeCount)

        let call = this.Parent n
        let isCall = this.Kind call = NodeKind.InvocationExpression

        let resultReceiver =
            isCall
            && let callChildren = this.Children call in
               let callee = callChildren[0] in

               SyntaxFacts.memberAccess (this.Kind callee)
               && let members = this.Children callee in
                  let receiver = members[0] in

                  this.Kind receiver = NodeKind.InvocationExpression
                  || this.Kind receiver = NodeKind.ElementAccessExpression

        let continuedCall = isCall && SyntaxFacts.memberAccess (this.Kind(this.Parent call))

        let children = this.Children lambda
        let body = children[children.Length - 1]
        let nestedBlock = this.CallWithExpandedBlockLambda body
        let initializedCreation = this.ContainsInitializedCreation body
        let callParentKind = this.Kind(this.Parent call)

        if
            ((soleBlock || resultReceiver) && this.ExpandedBlockLambda lambda)
            || ((resultReceiver || continuedCall) && (nestedBlock || initializedCreation))
            || ((continuedCall
                 || (isCall
                     && (argCount > 1
                         || callParentKind = NodeKind.Argument
                         || callParentKind = NodeKind.ParenthesizedExpression
                         || SyntaxFacts.initializer callParentKind
                         || SyntaxFacts.lambda callParentKind)))
                && initializedCreation)
            || (continuedCall && multilineToken)
        then
            d.AddBreakParent()

    member private this.Arguments(n: int, d: DocumentBuffer) =
        let c = this.Children n
        this.DropListCommentBlanks c

        let mutable argCount = 0
        let mutable firstArg = -1
        let mutable lastArg = -1
        let mutable multilineToken = false

        for i = 0 to c.Length - 1 do
            let child = c[i]

            if child >= 0 then
                if firstArg < 0 then
                    firstArg <- child

                lastArg <- child
                argCount <- argCount + 1

                if not multilineToken && this.MultilineToken child then
                    multilineToken <- true

        let lambda =
            if argCount = 0 then
                -1
            else
                let last = this.Children lastArg

                if last.Length > 0 && SyntaxFacts.lambda (this.Kind last[last.Length - 1]) then
                    last[last.Length - 1]
                else
                    -1

        let collection =
            argCount = 1
            && let ac = this.Children firstArg in
               ac.Length = 1 && this.Kind ac[0] = NodeKind.CollectionExpression

        let directiveLines =
            if
                indexedIgnores
                && (not hasDirectives
                    || (let tokens = tree.TokenSpan() in
                        let firstTok = &tokens[this.First n] in
                        let lastTok = &tokens[this.Last n] in

                        lastTok.TriviaStart + lastTok.LeadingCount + lastTok.TrailingCount
                        <= firstDirectiveTrivia
                        || firstTok.TriviaStart > lastDirectiveTrivia))
            then
                false
            else
                this.HasArgumentDirectives c

        if directiveLines then
            this.ArgumentsWithDirectives(n, c, d)
        elif collection && not multilineToken then
            this.All(c, d)
        elif lambda < 0 then
            this.Delimited(c, d, false, false, multilineToken)
        else
            this.ArgumentsWithLambda(n, c, argCount, lastArg, lambda, multilineToken, d)

    member private _.EarlyArgumentDemandsBreak
        (d: DocumentBuffer, rangesStart: int, rangeCount: int)
        =
        let mutable demanded = false
        let mutable r = 0

        while not demanded && r < rangeCount - 1 do
            let struct (start, length) = delimitedRanges[rangesStart + r]
            let mutable undecidedFrom = -1
            let mutable depth = 0
            let mutable i = start

            while not demanded && i < start + length do
                let e = d.Storage[i]

                if e.Kind = ElementKind.Tag then
                    match enum<Tag> e.B with
                    | Tag.StartConditionalGroup
                    | Tag.StartIfBreak
                    | Tag.StartForceFlat
                    | Tag.StartAlwaysFits ->
                        if undecidedFrom < 0 then
                            undecidedFrom <- depth

                        depth <- depth + 1
                    | Tag.StartGroup ->
                        if undecidedFrom < 0 && e.Flags &&& ElementFlags.Break <> 0uy then
                            demanded <- true

                        depth <- depth + 1
                    | Tag.StartIndent
                    | Tag.StartAlternative -> depth <- depth + 1
                    | Tag.Else -> ()
                    | _ ->
                        depth <- depth - 1

                        if undecidedFrom >= 0 && depth <= undecidedFrom then
                            undecidedFrom <- -1
                elif undecidedFrom >= 0 then
                    ()
                elif e.Kind = ElementKind.BreakParent then
                    demanded <- true
                elif e.Kind = ElementKind.Line && e.A = int LineKind.Hard then
                    demanded <- true

                i <- i + 1

            r <- r + 1

        demanded

    member private this.InsideAnonymousMethodBody(n: int) =
        let mutable node = (tree.Node n).Parent
        let mutable found = false

        while node >= 0 && not found do
            if this.Kind node = NodeKind.AnonymousMethodExpression then
                found <- true
            else
                node <- (tree.Node node).Parent

        found

    member private this.DelimitedShared
        (c: IntSlice, d: DocumentBuffer, rangesStart: int, rangeCount: int, expandedLambda: int)
        =
        this.Token(this.First c[0], d)

        d.AddTag Tag.StartIndent
        this.Hard d

        for i = 0 to rangeCount - 1 do
            if i > 0 then
                this.Hard d

            let struct (s, l) = delimitedRanges[rangesStart + i]

            if i = rangeCount - 1 && expandedLambda >= 0 && lastLambdaNode = expandedLambda then
                let struct (bodyStart, bodyEnd, expandedStart, expandedLength) = lastLambdaBody

                d.AddShared(s, bodyStart - s)
                d.AddShared(expandedStart, expandedLength)
                d.AddShared(bodyEnd, s + l - bodyEnd)
            else
                d.AddShared(s, l)

        d.AddTag Tag.EndIndent

        this.Hard d
        this.Emit(c[c.Length - 1], d)

    member private this.CollectionReceiver(n: int) =
        let mutable head = n

        while SyntaxFacts.memberAccess (this.Kind head)
              || this.Kind head = NodeKind.InvocationExpression
              || this.Kind head = NodeKind.ElementAccessExpression
              || this.Kind head = NodeKind.ConditionalAccessExpression
              || SyntaxFacts.postfix (this.Kind head) do
            let children = this.Children head
            head <- children[0]

        this.Kind head = NodeKind.CollectionExpression

    member private this.CollectChain(node: int) =
        this.EnsureStack()
        let c = this.Children node
        let k = this.Kind node

        if SyntaxFacts.memberAccess k then
            let calls = this.CollectChain c[0]

            for i = 1 to c.Length - 1 do
                chainParts.Add c[i]

            calls
        elif k = NodeKind.ConditionalAccessExpression then
            let leftCalls = this.CollectChain c[0]
            chainParts.Add c[1]
            let rightCalls = this.CollectChain c[2]
            leftCalls + rightCalls
        elif k = NodeKind.InvocationExpression || k = NodeKind.ElementAccessExpression then
            let calls = this.CollectChain c[0]

            for i = 1 to c.Length - 1 do
                chainParts.Add c[i]

            if k = NodeKind.InvocationExpression then
                calls + 1
            else
                calls
        elif SyntaxFacts.postfix k then
            let calls = this.CollectChain c[0]

            for i = 1 to c.Length - 1 do
                chainParts.Add c[i]

            calls
        elif k = NodeKind.MemberBindingExpression || k = NodeKind.ElementBindingExpression then
            for i = 0 to c.Length - 1 do
                chainParts.Add c[i]

            0
        else
            chainParts.Add node
            0

    member private this.Chain(n: int, d: DocumentBuffer) =
        let partsStart = chainParts.Count
        let calls = this.CollectChain n
        let partsCount = chainParts.Count - partsStart

        let mutable lastArguments = -1

        for i = 0 to partsCount - 1 do
            if this.Kind chainParts[partsStart + i] = NodeKind.ArgumentList then
                lastArguments <- i

        if partsCount > 0 then
            let p0 = chainParts[partsStart]
            let p0Kind = this.Kind p0
            let nKind = this.Kind n

            let arrayChain =
                calls > 1
                && p0Kind = NodeKind.ArrayCreationExpression
                && this.HasChildOfKind(p0, NodeKind.ArrayInitializerExpression)

            d.StartGroup(if arrayChain then ElementFlags.Break else 0uy) |> ignore
            this.Emit(p0, d)

            let creationSuffix =
                (p0Kind = NodeKind.ObjectCreationExpression
                 || p0Kind = NodeKind.ImplicitObjectCreationExpression)
                && (let p0Children = this.Children p0
                    let argIdx = this.SliceFindKind(p0Children, NodeKind.ArgumentList)
                    argIdx >= 0 && this.ChildCount p0Children[argIdx] <= 3)

            if creationSuffix then
                d.StartGroup() |> ignore

            let detachedRoot =
                calls >= 2
                && partsCount > 3
                && this.At(chainParts[partsStart + 3], TokenKind.DotToken)
                && (let pk = this.Kind(this.Parent n) in

                    pk = NodeKind.EqualsValueClause
                    || pk = NodeKind.AwaitExpression
                    || pk = NodeKind.ConditionalExpression)

            let merge =
                (p0Kind = NodeKind.ThisExpression
                 && not detachedRoot
                 && (partsCount < 2
                     || this.Kind chainParts[partsStart + 1] <> NodeKind.BracketedArgumentList))
                || p0Kind = NodeKind.BaseExpression
                || ((p0Kind = NodeKind.IdentifierName || p0Kind = NodeKind.PredefinedType)
                    && (partsCount < 2
                        || (let p1Kind = this.Kind chainParts[partsStart + 1] in

                            p1Kind <> NodeKind.ArgumentList
                            && p1Kind <> NodeKind.BracketedArgumentList))
                    && not (calls = 1 && SyntaxFacts.memberAccess nKind && lastArguments <> 3)
                    && not detachedRoot
                    && (p0Kind = NodeKind.PredefinedType
                        || (let tokens = tree.TokenSpan() in tokens[this.First p0].Length <= 4)))

            let propertySuffix =
                calls = 1
                && SyntaxFacts.memberAccess nKind
                && (lastArguments = 1 || (lastArguments = 3 && merge))
                && not (
                    partsCount > lastArguments + 3
                    && this.ChildCount chainParts[partsStart + lastArguments] <= 2
                )

            let propertyIndexer =
                calls = 1
                && partsCount > 3
                && this.Kind chainParts[partsStart + 3] = NodeKind.BracketedArgumentList

            let singleConditionalCall =
                calls = 1
                && nKind = NodeKind.ConditionalAccessExpression
                && lastArguments = partsCount - 1
                && not propertyIndexer
                && (let mutable hasBracket = false
                    let mutable idx = 0

                    while not hasBracket && idx < partsCount do
                        hasBracket <-
                            this.Kind chainParts[partsStart + idx] = NodeKind.BracketedArgumentList

                        idx <- idx + 1

                    not hasBracket)

            let mutable hasIndexer = false
            let mutable lastIndexer = -1

            for idx = 0 to partsCount - 1 do
                if this.Kind chainParts[partsStart + idx] = NodeKind.BracketedArgumentList then
                    hasIndexer <- true
                    lastIndexer <- idx

            let indexerChain =
                if calls <> 0 || not hasIndexer then
                    false
                else
                    let mutable trailingLinks = 0

                    for idx = lastIndexer + 1 to partsCount - 1 do
                        let part = chainParts[partsStart + idx]

                        if
                            part < 0
                            && (let tk = this.TokenKind part in

                                tk = TokenKind.QuestionToken
                                || tk = TokenKind.MinusGreaterThanToken
                                || (tk = TokenKind.DotToken
                                    && not (
                                        this.At(
                                            chainParts[partsStart + idx - 1],
                                            TokenKind.QuestionToken
                                        )
                                    )))
                        then
                            trailingLinks <- trailingLinks + 1

                    trailingLinks <= 1

            let breakFallback =
                not creationSuffix
                && not arrayChain
                && not propertySuffix
                && not singleConditionalCall
                && not indexerChain
                && calls = 1
                && partsCount > 4
                && nKind = NodeKind.ConditionalAccessExpression
                && lastArguments > 3

            if breakFallback then
                let spansStart = chainSpans.Count
                let id = d.NewGroupId()
                d.AddTag(Tag.StartConditionalGroup, id)
                d.AddTag Tag.StartAlternative
                let allStart = d.Count
                let breakBefore = d.ConditionalBreakCount()

                this.EmitChainLoop(
                    nKind,
                    p0Kind,
                    partsStart,
                    partsCount,
                    merge,
                    calls,
                    propertySuffix,
                    singleConditionalCall,
                    indexerChain,
                    hasIndexer,
                    lastArguments,
                    propertyIndexer,
                    true,
                    d
                )

                let allLength = d.Count - allStart
                let hasUnconditionalBreak = d.ConditionalBreakCount() <> breakBefore
                d.AddTag Tag.EndAlternative
                d.AddTag Tag.StartAlternative
                d.AddShared(allStart, allLength)
                d.AddTag Tag.EndAlternative
                d.AddTag Tag.StartAlternative

                let mutable loopLinks = 0

                let mutable indented =
                    merge
                    && calls > 1
                    && (p0Kind = NodeKind.ThisExpression || p0Kind = NodeKind.BaseExpression)

                if indented then
                    d.AddTag Tag.StartIndent

                let mutable includes = 0

                for spanIdx = spansStart to chainSpans.Count - 1 do
                    let struct (partStart, partLength, link, thenInclude) = chainSpans[spanIdx]

                    if link then
                        if thenInclude then
                            d.AddTag Tag.StartIndent
                            includes <- includes + 1
                        else
                            for _ = 1 to includes do
                                d.AddTag Tag.EndIndent

                            includes <- 0

                        loopLinks <- loopLinks + 1

                        if not (merge && loopLinks = 1) then
                            if not indented then
                                d.AddTag Tag.StartIndent
                                indented <- true

                            d.AddLine LineKind.Soft

                    d.AddShared(partStart, partLength)

                for _ = 1 to includes do
                    d.AddTag Tag.EndIndent

                if indented then
                    d.AddTag Tag.EndIndent

                d.AddTag Tag.EndAlternative
                d.AddTag Tag.EndConditionalGroup
                chainSpans.RemoveRange(spansStart, chainSpans.Count - spansStart)

                if hasUnconditionalBreak then
                    d.AddBreakParent()
            else
                this.EmitChainLoop(
                    nKind,
                    p0Kind,
                    partsStart,
                    partsCount,
                    merge,
                    calls,
                    propertySuffix,
                    singleConditionalCall,
                    indexerChain,
                    hasIndexer,
                    lastArguments,
                    propertyIndexer,
                    false,
                    d
                )

            if creationSuffix then
                d.EndGroup()

            d.EndGroup()

        chainParts.RemoveRange(partsStart, partsCount)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.EmitChainPart
        (
            i: int,
            part: int,
            partKind: NodeKind,
            calls: int,
            lastArguments: int,
            linksNow: int,
            indentedNow: bool,
            d: DocumentBuffer
        ) =
        if partKind = NodeKind.GenericName && calls > 0 then
            this.EmitChainGenericName(part, d)
        elif
            partKind = NodeKind.ArgumentList
            && (linksNow > 0
                || let call = this.Parent part in
                   let nextMember = this.Parent call in

                   SyntaxFacts.memberAccess (this.Kind nextMember)
                   && this.Kind(this.Parent nextMember) = NodeKind.InvocationExpression)
            && i <> lastArguments
            && not indentedNow
        then
            d.AddTag Tag.StartIndent
            this.Emit(part, d)
            d.AddTag Tag.EndIndent
        else
            this.Emit(part, d)

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.EmitChainLoop
        (
            nKind: NodeKind,
            p0Kind: NodeKind,
            partsStart: int,
            partsCount: int,
            merge: bool,
            calls: int,
            propertySuffix: bool,
            singleConditionalCall: bool,
            indexerChain: bool,
            hasIndexer: bool,
            lastArguments: int,
            propertyIndexer: bool,
            recordSpans: bool,
            d: DocumentBuffer
        ) =
        let mutable loopLinks = 0
        let mutable priorResult = false

        let mutable indented =
            merge
            && calls > 1
            && (p0Kind = NodeKind.ThisExpression || p0Kind = NodeKind.BaseExpression)

        if indented then
            d.AddTag Tag.StartIndent

        let mutable includes = 0

        for i = 1 to partsCount - 1 do
            let part = chainParts[partsStart + i]
            let partKind = this.Kind part

            let link =
                part < 0
                && (let tk = this.TokenKind part in

                    tk = TokenKind.QuestionToken
                    || tk = TokenKind.MinusGreaterThanToken
                    || (tk = TokenKind.DotToken
                        && not (this.At(chainParts[partsStart + i - 1], TokenKind.QuestionToken))))

            let mutable thenInclude = false

            if link then
                thenInclude <-
                    i + 1 < partsCount
                    && (let nextPart = chainParts[partsStart + i + 1] in

                        nextPart > 0
                        && treeTokens[this.First nextPart].Length = 11
                        && this.IsThenInclude nextPart)

                if thenInclude then
                    d.AddTag Tag.StartIndent
                    includes <- includes + 1
                else
                    for _ = 1 to includes do
                        d.AddTag Tag.EndIndent

                    includes <- 0

                loopLinks <- loopLinks + 1

                if
                    not propertySuffix
                    && not singleConditionalCall
                    && not indexerChain
                    && not (merge && loopLinks = 1)
                    && ((calls = 0 && partsCount > 3)
                        || priorResult
                        || (calls = 1 && hasIndexer)
                        || (calls = 1 && i > lastArguments && partsCount - 1 - lastArguments > 2)
                        || (loopLinks = 1
                            && (calls > 1
                                || propertyIndexer
                                || (calls > 0
                                    && (SyntaxFacts.memberAccess nKind
                                        || nKind = NodeKind.ConditionalAccessExpression)))))
                then
                    if not indented then
                        d.AddTag Tag.StartIndent
                        indented <- true

                    d.AddLine LineKind.Soft

                priorResult <- false

            if partKind = NodeKind.ArgumentList || partKind = NodeKind.BracketedArgumentList then
                priorResult <- true

            let partStart = d.Count
            this.EmitChainPart(i, part, partKind, calls, lastArguments, loopLinks, indented, d)
            let partLength = d.Count - partStart

            if recordSpans then
                chainSpans.Add(struct (partStart, partLength, link, thenInclude))

        for _ = 1 to includes do
            d.AddTag Tag.EndIndent

        if indented then
            d.AddTag Tag.EndIndent

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IsThenInclude(part: int) =
        this.Kind part = NodeKind.IdentifierName
        && source
            .AsSpan(treeTokens[this.First part].Start, 11)
            .SequenceEqual("ThenInclude".AsSpan())

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.EmitChainGenericName(part: int, d: DocumentBuffer) =
        let previousArguments = callTypeArguments
        let partChildren = this.Children part
        let tIdx = this.SliceFindKind(partChildren, NodeKind.TypeArgumentList)
        callTypeArguments <- if tIdx >= 0 then partChildren[tIdx] else -1

        let arguments = this.Children callTypeArguments
        let single = arguments.Length <= 3
        let mutable nested = false
        let tokens = tree.TokenSpan()

        for t = this.First callTypeArguments + 1 to this.Last callTypeArguments - 1 do
            if tokens[t].Kind = TokenKind.LessThanToken then
                nested <- true

        if single && not nested then
            d.AddTag Tag.StartForceFlat
            this.Emit(part, d)
            d.AddTag Tag.EndForceFlat
        else
            let id = d.NewGroupId()
            d.AddTag(Tag.StartConditionalGroup, id)
            d.AddTag Tag.StartAlternative
            d.AddTag Tag.StartForceFlat
            let start = d.Count
            this.Emit(part, d)
            let length = d.Count - start
            d.AddTag Tag.EndForceFlat
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.StartAlternative
            d.AddShared(start, length)
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.EndConditionalGroup

        callTypeArguments <- previousArguments

    member private this.BraceRows(children: IntSlice) =
        let mutable found = false
        let mutable i = 0

        while not found && i < children.Length do
            let k = this.Kind children[i]

            if
                k = NodeKind.ArrayInitializerExpression
                || k = NodeKind.ComplexElementInitializerExpression
            then
                found <- true

            i <- i + 1

        found

    member private this.Initializer(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let kind = this.Kind n

        if
            kind = NodeKind.ArrayInitializerExpression
            || kind = NodeKind.CollectionInitializerExpression
            || kind = NodeKind.CollectionExpression
        then
            this.DropListCommentBlanks c

        let creation = this.Parent n
        let owner = if creation >= 0 then this.Parent creation else -1

        let propertyInitializer =
            this.Kind owner = NodeKind.EqualsValueClause
            && this.Kind(this.Parent owner) = NodeKind.PropertyDeclaration

        let forced =
            kind = NodeKind.ObjectInitializerExpression
            || (kind = NodeKind.CollectionInitializerExpression
                && this.BraceRows c
                && not propertyInitializer
                && this.Kind owner <> NodeKind.Argument
                && this.Kind owner <> NodeKind.EqualsValueClause
                && this.Kind owner <> NodeKind.SimpleAssignmentExpression)
            || (kind = NodeKind.ArrayInitializerExpression
                && (this.BraceRows c
                    || (let mutable found = false
                        let mutable i = 0

                        while not found && i < c.Length do
                            if this.MultilineToken c[i] then
                                found <- true

                            i <- i + 1

                        found)))
            || kind = NodeKind.AnonymousObjectCreationExpression
            || (kind = NodeKind.CollectionExpression
                && (let mutable found = false
                    let mutable i = 0

                    while not found && i < c.Length do
                        let x = c[i]

                        if this.Kind x = NodeKind.ExpressionElement then
                            let cc = this.Children x

                            if cc.Length > 0 && this.Kind cc[0] = NodeKind.CollectionExpression then
                                found <- true

                        i <- i + 1

                    found))

        let parent = this.Kind creation

        let returnedCollection =
            if kind = NodeKind.CollectionExpression then
                let mutable owner = creation

                while SyntaxFacts.memberAccess (this.Kind owner)
                      || this.Kind owner = NodeKind.InvocationExpression
                      || this.Kind owner = NodeKind.ElementAccessExpression
                      || this.Kind owner = NodeKind.ConditionalAccessExpression
                      || SyntaxFacts.postfix (this.Kind owner) do
                    owner <- this.Parent owner

                this.Kind owner = NodeKind.ReturnStatement
            else
                false

        let joinedClause =
            kind = NodeKind.PropertyPatternClause
            && parent = NodeKind.RecursivePattern
            && this.JoinsPropertyClause(creation, n)

        let inheritMode =
            parent = NodeKind.ObjectCreationExpression
            || parent = NodeKind.ArrayCreationExpression
            || parent = NodeKind.ImplicitArrayCreationExpression
            || parent = NodeKind.ImplicitObjectCreationExpression
            || parent = NodeKind.StackAllocArrayCreationExpression
            || parent = NodeKind.ImplicitStackAllocArrayCreationExpression
            || parent = NodeKind.WithExpression
            || parent = NodeKind.SimpleAssignmentExpression
            || parent = NodeKind.EqualsValueClause
            || returnedCollection
            || (parent = NodeKind.SwitchExpressionArm && kind = NodeKind.CollectionExpression)
            || joinedClause
            || (kind = NodeKind.PropertyPatternClause
                && parent = NodeKind.RecursivePattern
                && this.Kind owner = NodeKind.IsPatternExpression
                && this.BinaryPatternOperand owner)

        let hasDesignation =
            kind = NodeKind.ListPattern
            && c.Length >= 3
            && c[c.Length - 1] >= 0
            && this.At(c[c.Length - 2], TokenKind.CloseBracketToken)

        let delimitedChildren = if hasDesignation then c.SliceRange(0, c.Length - 2) else c

        this.Delimited(
            delimitedChildren,
            d,
            kind <> NodeKind.CollectionExpression && kind <> NodeKind.ListPattern,
            kind <> NodeKind.PropertyPatternClause
            && kind <> NodeKind.ComplexElementInitializerExpression,
            forced && delimitedChildren.Length > 2,
            inheritMode,
            preserveBlanks = (kind = NodeKind.ObjectInitializerExpression),
            trimComma = (kind = NodeKind.PropertyPatternClause),
            emptyBreak = joinedClause
        )

        if hasDesignation then
            if ignoreUntil < 0 || treeTokens[this.First c[c.Length - 1]].Start >= ignoreUntil then
                this.Space d

            this.Emit(c[c.Length - 1], d)

    member private this.Raw
        (t: int, d: DocumentBuffer, [<Optional; DefaultParameterValue(false)>] attribute: bool)
        =
        let token = tree.Token t
        let text = source.AsSpan(token.Start, token.Length)
        let lastNewline = text.LastIndexOfAny('\r', '\n')
        let mutable close = lastNewline + 1

        while close < text.Length && (text[close] = ' ' || text[close] = '\t') do
            close <- close + 1

        let indent = close - lastNewline - 1

        if
            (this.HasMultiConfigurationOwnership || tree.LexerBuffer.HasInterpolated)
            && this.ForeignLiteral token
        then
            this.Trivia(t, true, d)
            d.AddTrim()
            let mutable first = token.Start

            while first > 0 && (source[first - 1] = ' ' || source[first - 1] = '\t') do
                first <- first - 1

            d.AddText(source, first, token.End - first)
            this.Trivia(t, false, d)
        elif text.IndexOfAny("\u0085\u2028\u2029".AsSpan()) >= 0 then
            this.Token(t, d)
        elif token.Kind = TokenKind.Utf8MultiLineRawStringLiteralToken then
            this.Trivia(t, true, d)
            let mutable start = 0
            let mutable i = 0

            while i < text.Length do
                if text[i] = '\r' || text[i] = '\n' then
                    d.AddText(source, token.Start + start, i - start)

                    if text[i] = '\r' && i + 1 < text.Length && text[i + 1] = '\n' then
                        i <- i + 1

                    d.AddLine LineKind.Literal
                    i <- i + 1
                    start <- i
                else
                    i <- i + 1

            d.AddText(source, token.Start + start, text.Length - start)
            this.Trivia(t, false, d)
        elif lastNewline < 0 || indent = 0 || whitespaceOnly then
            this.Token(t, d)
        else
            reindentedRawStrings <- true
            this.Trivia(t, true, d)
            let mutable start = 0
            let mutable i = 0
            let mutable directiveLine = false

            while i < text.Length do
                if text[i] = '\r' || text[i] = '\n' then
                    let length = i - start

                    if directiveLine then
                        d.AddTrim()

                    d.AddText(source, token.Start + start, length)

                    if text[i] = '\r' && i + 1 < text.Length && text[i + 1] = '\n' then
                        i <- i + 1

                    if start = 0 && attribute then
                        d.AddTag Tag.StartIndent

                    d.AddLine(
                        LineKind.IndentedLiteral,
                        if length > 0 then ElementFlags.NoTrim else 0uy
                    )

                    i <- i + 1
                    start <- i
                    let mutable removed = 0

                    while start < text.Length
                          && removed < indent
                          && (text[start] = ' ' || text[start] = '\t') do
                        start <- start + 1
                        removed <- removed + 1

                    directiveLine <- removed < indent && start < text.Length && text[start] = '#'
                    i <- start
                else
                    i <- i + 1

            d.AddText(source, token.Start + start, text.Length - start)

            if attribute then
                d.AddTag Tag.EndIndent

            this.Trivia(t, false, d)

    member private this.RawSlice
        (start: int, length: int, indent: int, lineStart: byref<bool>, d: DocumentBuffer)
        =
        let finish = start + length
        let mutable i = start

        while i < finish do
            let midline = not lineStart

            if lineStart then
                let mutable removed = 0

                while i < finish && removed < indent && (source[i] = ' ' || source[i] = '\t') do
                    i <- i + 1
                    removed <- removed + 1

            let first = i

            while i < finish && source[i] <> '\r' && source[i] <> '\n' do
                i <- i + 1

            if i > first then
                d.AddText(source, first, i - first)
                lineStart <- false

            if i < finish then
                d.AddLine(
                    LineKind.IndentedLiteral,
                    (if i > first || midline then ElementFlags.NoTrim else 0uy)
                )

                if source[i] = '\r' && i + 1 < finish && source[i + 1] = '\n' then
                    i <- i + 1

                lineStart <- true
                i <- i + 1

    member private this.Interpolated(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let first = this.First n
        let last = this.Last n
        let mutable multilineHole = false

        for idx = 0 to c.Length - 1 do
            let child = c[idx]

            if this.Kind child = NodeKind.Interpolation then
                let struct (start, length) = tree.SourceSpan child

                for i = start to start + length - 1 do
                    if SyntaxFacts.lineTerminator source[i] then
                        multilineHole <- true

        let firstToken = tree.Token first
        let lastToken = tree.Token last

        let foreign =
            this.HasMultiConfigurationOwnership
            && (this.ForeignLiteral firstToken
                || (firstToken.Start < literalLength
                    && lastToken.End <= literalLength
                    && lastToken.End > firstToken.Start
                    && literalBoundaries[lastToken.End - 1] > literalBoundaries[firstToken.Start]))

        let exotic =
            source
                .AsSpan(firstToken.Start, lastToken.End - firstToken.Start)
                .IndexOfAny("\u0085\u2028\u2029".AsSpan())
            >= 0

        if foreign then
            this.Trivia(first, true, d)
            d.AddTrim()
            let mutable startPos = firstToken.Start

            while startPos > 0 && (source[startPos - 1] = ' ' || source[startPos - 1] = '\t') do
                startPos <- startPos - 1

            d.AddText(source, startPos, lastToken.End - startPos)
            this.Trivia(last, false, d)
        elif
            multilineHole
            || exotic
            || (whitespaceOnly
                && (tree.Token first).Kind = TokenKind.InterpolatedMultiLineRawStringStartToken)
        then
            this.Trivia(first, true, d)
            let a, b = tree.Token first, tree.Token last
            d.AddText(source, a.Start, b.End - a.Start)
            this.Trivia(last, false, d)
        elif (tree.Token first).Kind = TokenKind.InterpolatedMultiLineRawStringStartToken then
            let closing = tree.Token last
            let text = source.AsSpan(closing.Start, closing.Length)
            let newline = text.LastIndexOfAny('\r', '\n')
            let mutable close = newline + 1

            while close < text.Length && (text[close] = ' ' || text[close] = '\t') do
                close <- close + 1

            let indent = close - newline - 1

            if newline < 0 || indent = 0 then
                d.AddTag Tag.StartForceFlat
                this.All(c, d)
                d.AddTag Tag.EndForceFlat
            else
                reindentedRawStrings <- true
                let inExprStatement = this.Kind (tree.Node n).Parent = NodeKind.ExpressionStatement

                if inExprStatement then
                    d.AddTag Tag.StartIndent

                let mutable lineStart = false

                for idx = 0 to c.Length - 1 do
                    let child = c[idx]

                    if child < 0 || this.Kind child = NodeKind.InterpolatedStringText then
                        let token = tree.Token(this.First child)
                        this.RawSlice(token.Start, token.Length, indent, &lineStart, d)
                    else
                        d.AddTag Tag.StartForceFlat
                        this.Emit(child, d)
                        d.AddTag Tag.EndForceFlat
                        lineStart <- false

                if inExprStatement then
                    d.AddTag Tag.EndIndent

                this.Trivia(last, false, d)
        else
            d.AddTag Tag.StartForceFlat
            this.All(c, d)
            d.AddTag Tag.EndForceFlat

    member private this.Block
        (
            n: int,
            d: DocumentBuffer,
            separator: bool,
            [<Optional; DefaultParameterValue(false)>] openingPrinted: bool
        ) =
        this.EnsureStack()

        if
            not (this.IgnoreCompleteNode(n, d))
            && (openingPrinted || not preserveForeignCode || not (this.ForeignNode(n, d)))
        then
            this.BlockCore(n, d, separator, openingPrinted)

    member private this.BlockCore
        (
            n: int,
            d: DocumentBuffer,
            separator: bool,
            [<Optional; DefaultParameterValue(false)>] openingPrinted: bool
        ) =
        let c = this.Children n

        if
            c.Length = 2
            && not (this.HasTrivia(this.First c[1], true))
            && not (this.HasTrivia(this.First c[0], false))
        then
            let anonymous = this.Kind(this.Parent n) = NodeKind.AnonymousMethodExpression

            if separator then
                if anonymous then
                    d.StartGroup() |> ignore
                    d.AddLine LineKind.Normal
                else
                    this.Space d

            this.Emit(c[0], d)
            this.Space d
            let closing = tree.Token(this.First c[1])

            if seen.Length < tree.TriviaCount then
                Array.Resize(&seen, max 16 tree.TriviaCount)

            for i = closing.TriviaStart to closing.TriviaStart + closing.LeadingCount - 1 do
                seen[i] <- true

            this.Emit(c[1], d)

            if separator && anonymous then
                d.EndGroup()
        else
            if separator && not openingPrinted then
                this.Hard d

            if not openingPrinted then
                this.Emit(c[0], d)

            let inline body () =
                this.Hard d
                suppressBlank <- this.First c[1]
                this.Members(c.SliceRange(1, c.Length - 2), d, false, false)

                if c.Length > 1 then
                    this.ClosingTrivia(this.First c[c.Length - 1], d)

            if c.Length = 2 && not (this.HasTrivia(this.First c[1], true)) then
                body ()
            else
                d.AddTag Tag.StartIndent
                body ()
                d.AddTag Tag.EndIndent

            this.Hard d

            if c.Length > 1 then
                this.Emit(c[c.Length - 1], d)

    member private this.SimpleMember(child: int) =
        let kind = this.Kind child

        kind = NodeKind.FieldDeclaration
        || kind = NodeKind.EventFieldDeclaration
        || kind = NodeKind.PropertyDeclaration
        || kind = NodeKind.IndexerDeclaration
        || kind = NodeKind.EventDeclaration
        || kind = NodeKind.DelegateDeclaration
        || (kind = NodeKind.MethodDeclaration
            && (this.Kind(this.Parent child) = NodeKind.InterfaceDeclaration
                || this.SliceContainsToken(this.Children child, TokenKind.AbstractKeyword)))

    member private this.EmptyConditionalPrefix(t: int, finish: int) =
        this.IndexConditionals()
        let token = tree.Token t

        hasConditionals
        && finish > token.TriviaStart
        && finish <= token.TriviaStart + token.LeadingCount
        && finish <= tree.TriviaCount
        && emptyConditionalPrefixes[finish]

    member private this.ConditionalPrefixAt(t: int, opening: int, empty: bool) =
        this.IndexConditionals()
        let token = tree.Token t

        match conditionalPrefixes.TryGetValue opening with
        | true, struct (finish, isEmpty) ->
            opening >= token.TriviaStart
            && finish <= token.TriviaStart + token.LeadingCount
            && isEmpty = empty
        | _ -> false

    member private this.AdjacentAttributeRegion(n: int, prefix: int) =
        if prefix <= 0 then
            false
        else
            let first = this.First n
            let token = tree.Token first

            if
                prefix <= token.TriviaStart
                || (tree.Trivia(prefix - 1)).Kind <> TriviaKind.EndIfDirectiveTrivia
            then
                false
            else
                let c = this.Children n
                let mutable attributes = 0

                while attributes < c.Length && this.Kind c[attributes] = NodeKind.AttributeList do
                    attributes <- attributes + 1

                if attributes = 0 || attributes = c.Length then
                    false
                else
                    let header = this.First c[attributes]
                    let mutable depth = 0
                    let mutable opened = false
                    let mutable attributesOnly = true

                    for t = first to header do
                        let token = tree.Token t
                        let start = if t = first then prefix else token.TriviaStart

                        for j = start to token.TriviaStart + token.LeadingCount - 1 do
                            let kind = (tree.Trivia j).Kind

                            if kind = TriviaKind.IfDirectiveTrivia then
                                opened <- true
                                depth <- depth + 1
                            elif kind = TriviaKind.EndIfDirectiveTrivia then
                                depth <- depth - 1
                            elif
                                not opened
                                && (SyntaxFacts.directive kind || SyntaxFacts.comment kind)
                            then
                                attributesOnly <- false

                        if t < header && depth <= 0 then
                            attributesOnly <- false

                    opened && attributesOnly && depth = 0

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.EmitEnumMember
        (
            c: IntSlice,
            i: int,
            child: int,
            ignored: bool,
            attributed: bool,
            commented: bool,
            previous: NodeKind,
            previousIgnored: bool,
            d: DocumentBuffer
        ) =
        if ignored then
            this.Emit(child, d)
        else
            if (attributed || commented) && previous <> NodeKind.None && not previousIgnored then
                this.Blank d

            if i + 1 < c.Length && this.At(c[i + 1], TokenKind.CommaToken) then
                this.Emit(child, d)
            else
                let tokens = tree.TokenSpan()
                let triviaSpan = tree.TriviaSpan()
                let lt = this.Last child
                let token = &tokens[lt]

                if seen.Length < tree.TriviaCount then
                    Array.Resize(&seen, max 16 tree.TriviaCount)

                for j = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                                  + token.LeadingCount
                                                                  + token.TrailingCount
                                                                  - 1 do
                    seen[j] <- true

                this.Emit(child, d)
                let mutable conditionalSeparator = false
                let finish = this.First c[c.Length - 1] + 1

                for next = lt + 1 to min (tree.TokenCount - 1) finish do
                    let nt = &tokens[next]

                    for j = nt.TriviaStart to nt.TriviaStart + nt.LeadingCount - 1 do
                        let trivia = &triviaSpan[j]

                        if
                            trivia.Kind = TriviaKind.DisabledTextTrivia
                            && source
                                .AsSpan(trivia.Start, trivia.Length)
                                .TrimStart()
                                .StartsWith(",".AsSpan(), StringComparison.Ordinal)
                        then
                            conditionalSeparator <- true

                if lt + 1 < tree.TokenCount then
                    let closer = &tokens[lt + 1]

                    for j = closer.TriviaStart to closer.TriviaStart + closer.LeadingCount - 1 do
                        let kind = triviaSpan[j].Kind

                        if SyntaxFacts.directive kind || kind = TriviaKind.DisabledTextTrivia then
                            conditionalSeparator <- true

                if not conditionalSeparator && not whitespaceOnly then
                    changedTrailingCommas <- true
                    d.AddToken StaticToken.Comma

                for j = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                                  + token.LeadingCount
                                                                  + token.TrailingCount
                                                                  - 1 do
                    seen[j] <- false

                this.Trivia(lt, false, d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.MembersComplex
        (c: IntSlice, d: DocumentBuffer, declarations: bool, enum: bool, preserveLeadingBlank: bool)
        =
        let mutable previous = NodeKind.None
        let mutable previousSimple = true
        let mutable previousControl = false
        let mutable previousIgnored = false
        let mutable previousDirectiveEnded = false
        let mutable previousConditionalClose = false
        let tokens = tree.TokenSpan()
        let triviaSpan = tree.TriviaSpan()

        for i = 0 to c.Length - 1 do
            memberProbes <- memberProbes + 1L
            let child = c[i]
            let kind = this.Kind child
            let first = this.First child
            let t = &tokens[first]

            if child >= 0 && t.Start >= ignoreUntil then
                blankSibling <-
                    if
                        (previous <> NodeKind.None || (i = 0 && preserveLeadingBlank))
                        && this.Kind(this.Parent child) <> NodeKind.AccessorList
                    then
                        first
                    else
                        -1

                let ignored =
                    hasIgnores && (this.IgnoreRange t.Start >= 0 || ignoredSingles.Contains t.Start)

                let mutable prefix = -1
                let mutable commented = false
                let mutable marker = 0
                let mutable prefixKind = TriviaKind.None
                let mutable pragmaPrefix = false
                let mutable regionAttributes = false
                let mutable closingPrefix = false
                let mutable alternateAfterPrefix = false

                if
                    t.LeadingCount > 0
                    && not (
                        t.LeadingCount = 1
                        && triviaSpan[t.TriviaStart].Kind = TriviaKind.WhitespaceTrivia
                    )
                then
                    for j = t.TriviaStart to t.TriviaStart + t.LeadingCount - 1 do
                        let trivia = &triviaSpan[j]
                        let tk = trivia.Kind
                        commented <- commented || SyntaxFacts.comment tk

                        pragmaPrefix <-
                            pragmaPrefix
                            || tk = TriviaKind.PragmaWarningDirectiveTrivia
                            || tk = TriviaKind.PragmaChecksumDirectiveTrivia

                        if hasIgnores && tk = TriviaKind.SingleLineCommentTrivia then
                            marker <-
                                SyntaxFacts.ignoreMarker (
                                    source.AsSpan(trivia.Start, trivia.Length).Trim()
                                )

                        if tk = TriviaKind.DisabledTextTrivia then
                            let text = source.AsSpan(trivia.Start, trivia.Length).Trim()
                            closingPrefix <- closingPrefix || text.SequenceEqual("}".AsSpan())

                            regionAttributes <-
                                text.Length > 1 && text[0] = '[' && text[text.Length - 1] = ']'

                        if
                            tk = TriviaKind.EndRegionDirectiveTrivia
                            || tk = TriviaKind.EndIfDirectiveTrivia
                            || tk = TriviaKind.PragmaWarningDirectiveTrivia
                            || tk = TriviaKind.PragmaChecksumDirectiveTrivia
                        then
                            prefix <- j + 1
                            prefixKind <- tk
                            alternateAfterPrefix <- false
                        elif prefix >= 0 && tk = TriviaKind.BadDirectiveTrivia then
                            prefix <- j + 1
                        elif
                            prefix >= 0
                            && (tk = TriviaKind.ElifDirectiveTrivia
                                || tk = TriviaKind.ElseDirectiveTrivia)
                        then
                            alternateAfterPrefix <- true

                let simple =
                    (declarations || prefixKind = TriviaKind.EndIfDirectiveTrivia)
                    && this.SimpleMember child

                let attributed =
                    (declarations || enum || prefixKind = TriviaKind.EndIfDirectiveTrivia)
                    && this.HasChildOfKind(child, NodeKind.AttributeList)

                if prefix >= 0 && not ignored then
                    if previous <> NodeKind.None then
                        if declarations && regionAttributes && not alternateAfterPrefix then
                            this.Blank d
                        else
                            this.Hard d

                    this.Trivia(first, true, d, prefix)

                let emptyRegion =
                    prefixKind = TriviaKind.EndIfDirectiveTrivia
                    && this.EmptyConditionalPrefix(first, prefix)

                let mutable firstTrivia = t.TriviaStart
                let mutable conditionalMember = false

                if declarations && t.LeadingCount > 0 then
                    let mutable ft = max t.TriviaStart prefix
                    let limit = t.TriviaStart + t.LeadingCount

                    while ft < limit
                          && (let k = triviaSpan[ft].Kind in
                              k = TriviaKind.WhitespaceTrivia || k = TriviaKind.EndOfLineTrivia) do
                        ft <- ft + 1

                    firstTrivia <- ft

                    conditionalMember <-
                        ft < limit && triviaSpan[ft].Kind = TriviaKind.IfDirectiveTrivia

                if previous <> NodeKind.None then
                    if
                        not declarations
                        && marker <> 2
                        && marker <> 3
                        && not previousIgnored
                        && not ignored
                        && not alternateAfterPrefix
                        && (previousControl || this.ControlStatement child)
                    then
                        this.Blank d
                    elif
                        ((marker = 2 || marker = 3 || previousIgnored) && not enum)
                        || prefixKind = TriviaKind.EndRegionDirectiveTrivia
                        || prefixKind = TriviaKind.PragmaWarningDirectiveTrivia
                        || prefixKind = TriviaKind.PragmaChecksumDirectiveTrivia
                        || pragmaPrefix
                        || regionAttributes
                        || emptyRegion
                        || alternateAfterPrefix
                        || (prefixKind = TriviaKind.EndIfDirectiveTrivia
                            && previousSimple
                            && (ignored || commented)
                            && not attributed)
                        || (prefixKind = TriviaKind.EndIfDirectiveTrivia
                            && (recoveringConditionals
                                || previousConditionalClose
                                || (t.LeadingCount > 0
                                    && triviaSpan[t.TriviaStart].Kind = TriviaKind.IfDirectiveTrivia
                                    && not (this.ConditionalPrefixAt(first, t.TriviaStart, true))
                                    && not (this.ConditionalPrefixAt(first, t.TriviaStart, false))))
                            && previous = NodeKind.MethodDeclaration
                            && kind = NodeKind.ClassDeclaration
                            && not attributed)
                        || (prefixKind = TriviaKind.EndIfDirectiveTrivia
                            && previousConditionalClose
                            && kind <> NodeKind.MethodDeclaration
                            && not attributed)
                        || (prefixKind = TriviaKind.EndIfDirectiveTrivia
                            && closingPrefix
                            && not attributed)
                        || (conditionalMember
                            && not attributed
                            && ((simple
                                 && previousSimple
                                 && closedConditionals.Contains triviaSpan[firstTrivia].Start)
                                || prefixKind = TriviaKind.EndIfDirectiveTrivia
                                || previousDirectiveEnded))
                        || (prefix > t.TriviaStart && this.AdjacentAttributeRegion(child, prefix))
                    then
                        this.Hard d
                    elif enum && hasIgnores && ignoredSingles.Contains t.Start then
                        this.Blank d
                    elif
                        not declarations
                        && kind = NodeKind.Block
                        && this.Kind(this.Parent child) = NodeKind.SwitchSection
                    then
                        this.Blank d
                    elif
                        declarations
                        && not enum
                        && (not previousSimple || not simple || attributed || commented)
                    then
                        this.Blank d
                    else
                        this.Hard d

                if enum then
                    this.EmitEnumMember(
                        c,
                        i,
                        child,
                        ignored,
                        attributed,
                        commented,
                        previous,
                        previousIgnored,
                        d
                    )
                else
                    this.Emit(child, d)

                previous <- kind
                previousSimple <- simple
                previousControl <- this.ControlStatement child
                previousIgnored <- ignored && not (ignoredSingles.Contains t.Start)
                previousDirectiveEnded <- false
                previousConditionalClose <- false

                if kind = NodeKind.MethodDeclaration then
                    let closing = &tokens[this.Last child]

                    if closing.Kind = TokenKind.CloseBraceToken && closing.LeadingCount > 0 then
                        for j = closing.TriviaStart to closing.TriviaStart + closing.LeadingCount
                                                       - 1 do
                            let tk = triviaSpan[j].Kind

                            if
                                tk <> TriviaKind.WhitespaceTrivia
                                && tk <> TriviaKind.EndOfLineTrivia
                            then
                                previousDirectiveEnded <- tk = TriviaKind.EndIfDirectiveTrivia

                                previousConditionalClose <- tk = TriviaKind.IfDirectiveTrivia
            else
                this.Emit(child, d)

    member private this.Members
        (
            c: IntSlice,
            d: DocumentBuffer,
            declarations: bool,
            enum: bool,
            [<Optional; DefaultParameterValue(false)>] preserveLeadingBlank: bool
        ) =
        if hasDirectives || hasIgnores then
            this.MembersComplex(c, d, declarations, enum, preserveLeadingBlank)
        else
            let mutable previous = NodeKind.None
            let mutable previousSimple = true
            let mutable previousControl = false
            let tokens = tree.TokenSpan()
            let triviaSpan = tree.TriviaSpan()

            for i = 0 to c.Length - 1 do
                memberProbes <- memberProbes + 1L
                let child = c[i]

                if child >= 0 then
                    let kind = this.Kind child
                    let first = this.First child
                    let t = &tokens[first]

                    blankSibling <-
                        if
                            (previous <> NodeKind.None || (i = 0 && preserveLeadingBlank))
                            && this.Kind(this.Parent child) <> NodeKind.AccessorList
                        then
                            first
                        else
                            -1

                    let mutable commented = false

                    if
                        hasComments
                        && t.LeadingCount > 0
                        && not (
                            t.LeadingCount = 1
                            && triviaSpan[t.TriviaStart].Kind = TriviaKind.WhitespaceTrivia
                        )
                    then
                        for j = t.TriviaStart to t.TriviaStart + t.LeadingCount - 1 do
                            if SyntaxFacts.comment triviaSpan[j].Kind then
                                commented <- true

                    let simple = declarations && this.SimpleMember child

                    let attributed =
                        (declarations || enum) && this.HasChildOfKind(child, NodeKind.AttributeList)

                    if previous <> NodeKind.None then
                        if not declarations && (previousControl || this.ControlStatement child) then
                            this.Blank d
                        elif
                            not declarations
                            && kind = NodeKind.Block
                            && this.Kind(this.Parent child) = NodeKind.SwitchSection
                        then
                            this.Blank d
                        elif
                            declarations
                            && not enum
                            && (not previousSimple || not simple || attributed || commented)
                        then
                            this.Blank d
                        else
                            this.Hard d

                    if enum then
                        this.EmitEnumMember(
                            c,
                            i,
                            child,
                            false,
                            attributed,
                            commented,
                            previous,
                            false,
                            d
                        )
                    else
                        this.Emit(child, d)

                    previous <- kind
                    previousSimple <- simple
                    previousControl <- this.ControlStatement child
                else
                    this.Emit(child, d)

    member private this.ModifierRank(n: int) =
        match this.TokenKind n with
        | TokenKind.PublicKeyword -> 0
        | TokenKind.PrivateKeyword -> 1
        | TokenKind.ProtectedKeyword -> 2
        | TokenKind.InternalKeyword -> 3
        | TokenKind.FileKeyword -> 4
        | TokenKind.StaticKeyword -> 5
        | TokenKind.ExternKeyword -> 6
        | TokenKind.NewKeyword -> 7
        | TokenKind.VirtualKeyword -> 8
        | TokenKind.AbstractKeyword -> 9
        | TokenKind.SealedKeyword -> 10
        | TokenKind.OverrideKeyword -> 11
        | TokenKind.ReadOnlyKeyword -> 12
        | TokenKind.UnsafeKeyword -> 13
        | TokenKind.RequiredKeyword -> 14
        | TokenKind.VolatileKeyword -> 16
        | TokenKind.AsyncKeyword -> 17
        | TokenKind.PartialKeyword -> 20
        | _ -> 15

    member private this.Modifiers(decl: int, c: IntSlice, first: int, d: DocumentBuffer) =
        let mutable finish = first

        while finish < c.Length && c[finish] < 0 && this.ModifierRank c[finish] <> 15 do
            finish <- finish + 1

        if finish = first then
            finish
        elif finish - first = 1 then
            this.Emit(c[first], d)
            this.Space d
            finish
        else
            this.ModifiersMultiple(decl, c, first, finish, d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ModifiersMultiple
        (decl: int, c: IntSlice, first: int, finish: int, d: DocumentBuffer)
        =
        let mutable guarded = false
        let declKind = this.Kind decl
        let isLocal = declKind = NodeKind.LocalFunctionStatement

        let isTypeDecl =
            match declKind with
            | NodeKind.ClassDeclaration
            | NodeKind.StructDeclaration
            | NodeKind.InterfaceDeclaration
            | NodeKind.RecordDeclaration
            | NodeKind.RecordStructDeclaration
            | NodeKind.EnumDeclaration
            | NodeKind.DelegateDeclaration
            | NodeKind.UnionDeclaration -> true
            | _ -> false

        let mutable carriesFile = false
        let mutable carriesPartial = false
        let mutable carriesAsync = false
        let mutable carriesExtern = false
        let mutable carriesStationary = false

        for index = first to finish - 1 do
            match this.TokenKind c[index] with
            | TokenKind.FileKeyword ->
                carriesFile <- true
                carriesStationary <- true
            | TokenKind.PartialKeyword ->
                carriesPartial <- true
                carriesStationary <- true
            | TokenKind.RequiredKeyword
            | TokenKind.FixedKeyword -> carriesStationary <- true
            | TokenKind.AsyncKeyword -> carriesAsync <- true
            | TokenKind.ExternKeyword -> carriesExtern <- true
            | _ -> ()

        if
            (carriesFile && carriesPartial)
            || (carriesExtern && isTypeDecl)
            || (carriesAsync
                && ((declKind <> NodeKind.MethodDeclaration && not isLocal) || carriesStationary))
        then
            guarded <- true

        for index = first to finish - 2 do
            match this.TokenKind c[index] with
            | TokenKind.PartialKeyword
            | TokenKind.RequiredKeyword -> guarded <- true
            | _ -> ()

        for index = first to finish - 1 do
            if not guarded then
                let token = tree.Token(this.First c[index])

                if
                    hasIgnores
                    && (token.Start < ignoreUntil
                        || ignoredSingles.Contains token.Start
                        || this.IgnoreRange token.Start >= 0)
                then
                    guarded <- true
                else
                    for t = token.TriviaStart to token.TriviaStart
                                                 + token.LeadingCount
                                                 + token.TrailingCount
                                                 - 1 do
                        let trivia = tree.Trivia t

                        if
                            SyntaxFacts.directive trivia.Kind
                            || trivia.Kind = TriviaKind.DisabledTextTrivia
                            || (index > first
                                && t < token.TriviaStart + token.LeadingCount
                                && SyntaxFacts.comment trivia.Kind)
                            || (trivia.Kind = TriviaKind.SingleLineCommentTrivia
                                && SyntaxFacts.ignoreMarker (
                                    source.AsSpan(trivia.Start, trivia.Length).Trim()
                                )
                                    >
                                    0)
                        then
                            guarded <- true

        if guarded || whitespaceOnly then
            for index = first to finish - 1 do
                this.Emit(c[index], d)
                this.Space d
        else
            let count = finish - first

            if modifierBuffer.Length < count then
                modifierBuffer <- Array.zeroCreate (max (modifierBuffer.Length * 2) count)

            for i = 0 to count - 1 do
                modifierBuffer[i] <- c[first + i]

            for i = 1 to count - 1 do
                let item = modifierBuffer[i]
                let rank = this.ModifierRank item
                let mutable j = i - 1

                while j >= 0 && this.ModifierRank modifierBuffer[j] > rank do
                    modifierBuffer[j + 1] <- modifierBuffer[j]
                    j <- j - 1

                modifierBuffer[j + 1] <- item

            let mutable index = 0

            while not sortedModifiers && index < count do
                sortedModifiers <- modifierBuffer[index] <> c[first + index]
                index <- index + 1

            let firstToken = this.First c[first]

            if modifierBuffer[0] <> c[first] && firstToken <> lastDeclinedLeadingToken then
                let token = tree.Token firstToken

                if not (this.DeclinedRun(firstToken, token.TriviaStart, token.LeadingCount)) then
                    this.Trivia(firstToken, true, d)

                hoistedLeadingToken <- firstToken

            for i = 0 to count - 1 do
                this.Emit(modifierBuffer[i], d)
                this.Space d

            hoistedLeadingToken <- -1

        finish

    member private this.DeclarationHead(decl: int, c: IntSlice, d: DocumentBuffer) =
        let mutable first = 0

        while first < c.Length && this.Kind c[first] = NodeKind.AttributeList do
            this.Emit(c[first], d)
            this.Hard d
            first <- first + 1

        let finish = this.Modifiers(decl, c, first, d)
        let index = this.SliceFindKind(c, NodeKind.TypeParameterConstraintClause)

        if index >= 0 then
            if finish < c.Length then
                this.Trivia(this.First c[finish], true, d)

            let savedDirectives = headerDirectiveAlwaysFits
            headerDirectiveAlwaysFits <- true
            d.StartGroup() |> ignore

            try
                this.Spaced(c.SliceRange(finish, index - 1), d)
            finally
                headerDirectiveAlwaysFits <- savedDirectives

            d.EndGroup()
            this.Spaced(c.SliceFrom index, d)
        elif this.SliceContainsKind(c, NodeKind.BaseList) then
            if finish < c.Length then
                this.Trivia(this.First c[finish], true, d)

            let savedDirectives = headerDirectiveAlwaysFits
            headerDirectiveAlwaysFits <- true
            d.StartGroup() |> ignore

            try
                this.Spaced(c.SliceFrom finish, d)
            finally
                headerDirectiveAlwaysFits <- savedDirectives

            d.EndGroup()
        else
            this.Spaced(c.SliceFrom finish, d)

    member private this.TypeDeclaration(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let first = this.SliceFindToken(c, TokenKind.OpenBraceToken)

        if first < 0 then
            d.StartGroup() |> ignore
            this.DeclarationHead(n, c, d)
            d.EndGroup()
        else
            d.StartGroup() |> ignore
            this.DeclarationHead(n, c.SliceRange(0, first - 1), d)
            d.EndGroup()

            let closeIndex = this.SliceFindTokenBack(c, TokenKind.CloseBraceToken)
            let members = c.SliceRange(first + 1, closeIndex - 1)

            if members.Length = 0 && not (this.HasTrivia(this.First c[closeIndex], true)) then
                this.Space d
                this.Emit(c[first], d)
                this.Space d
                this.Emit(c[closeIndex], d)
            else
                this.Hard d
                this.Emit(c[first], d)
                d.AddTag Tag.StartIndent
                this.Hard d
                suppressBlank <- this.First c[first + 1]
                this.Members(members, d, true, this.Kind n = NodeKind.EnumDeclaration)
                this.ClosingTrivia(this.First c[closeIndex], d)
                d.AddTag Tag.EndIndent
                this.Hard d
                this.Emit(c[closeIndex], d)

            this.All(c.SliceFrom(closeIndex + 1), d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.HasCommentOpening(blockNode: int, openBraceChild: int) =
        let bodyStart = (tree.Token(this.First blockNode)).Start

        let preservedBody =
            bodyStart < ignoreUntil
            || (hasIgnores
                && (ignoredSingles.Contains bodyStart || this.IgnoreRange bodyStart >= 0))

        if preservedBody then
            false
        else
            let token = tree.Token(this.First openBraceChild)
            let mutable comment = false
            let mutable other = false

            for i = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                              + token.LeadingCount
                                                              + token.TrailingCount
                                                              - 1 do
                let trivia = tree.Trivia i

                if trivia.Kind = TriviaKind.MultiLineCommentTrivia then
                    comment <- true

                    other <-
                        other
                        || source.AsSpan(trivia.Start, trivia.Length).IndexOfAny('\r', '\n') >= 0
                elif SyntaxFacts.comment trivia.Kind || SyntaxFacts.directive trivia.Kind then
                    other <- true

            comment && not other && not (this.HasTrivia(this.First openBraceChild, true))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.MethodSpecial
        (n: int, c: IntSlice, index: int, emptyBody: bool, commentOpening: bool, d: DocumentBuffer)
        =
        let initializerHeader =
            emptyBody
            && index > 0
            && (this.Kind c[index - 1] = NodeKind.ThisConstructorInitializer
                || this.Kind c[index - 1] = NodeKind.BaseConstructorInitializer)

        if emptyBody && not initializerHeader then
            d.StartGroup() |> ignore

        let header =
            if initializerHeader then
                d.StartGroup() |> ignore
                this.DeclarationHead(n, c.SliceRange(0, index - 2), d)
                d.EndGroup()
                d.StartGroup() |> ignore

                d.AddTag Tag.StartIndent

                d.AddLine(LineKind.Hard, ElementFlags.Squash ||| ElementFlags.SkipBreakIfFirst)

                let initializer = d.StartGroup()
                this.Spaced(this.Children c[index - 1], d)
                d.EndGroup()

                d.AddTag Tag.EndIndent

                initializer
            else
                let id = d.StartGroup()
                this.DeclarationHead(n, c.SliceRange(0, index - 1), d)

                if commentOpening then
                    this.Space d
                    let body = this.Children c[index]

                    this.Token(
                        this.First body[0],
                        d,
                        spaceBeforeComments = true,
                        measureComments = true
                    )

                d.EndGroup()
                id

        if this.Kind c[index] = NodeKind.Block then
            if emptyBody then
                d.AddTag(Tag.StartIfBreak, header)
                this.Space d
                d.AddTag Tag.Else
                d.AddLine LineKind.Normal
                d.AddTag Tag.EndIfBreak

                this.Block(c[index], d, false)
            else
                this.Block(c[index], d, true, openingPrinted = commentOpening)
        else
            this.Emit(c[index], d)

        this.All(c.SliceFrom(index + 1), d)

        if emptyBody then
            d.EndGroup()

    member private this.Method(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let mutable index = -1
        let mutable scan = 0

        while index < 0 && scan < c.Length do
            let k = this.Kind c[scan]

            if k = NodeKind.Block || k = NodeKind.ArrowExpressionClause then
                index <- scan

            scan <- scan + 1

        if index < 0 then
            d.StartGroup() |> ignore
            this.DeclarationHead(n, c, d)
            d.EndGroup()
        else
            let isBlock = this.Kind c[index] = NodeKind.Block

            let body =
                if isBlock then
                    this.Children c[index]
                else
                    Unchecked.defaultof<IntSlice>

            let commentOpening =
                isBlock
                && this.Kind n = NodeKind.MethodDeclaration
                && (let openTok = tree.Token(this.First body[0]) in openTok.TrailingCount > 0)
                && this.HasCommentOpening(c[index], body[0])

            let emptyBody =
                isBlock
                && body.Length = 2
                && (this.Kind n = NodeKind.ConstructorDeclaration
                    || this.Kind n = NodeKind.LocalFunctionStatement)
                && not (this.HasTrivia(this.First body[0], false))
                && not (this.HasTrivia(this.First body[1], true))

            if emptyBody || commentOpening then
                this.MethodSpecial(n, c, index, emptyBody, commentOpening, d)
            else
                d.StartGroup() |> ignore
                this.DeclarationHead(n, c.SliceRange(0, index - 1), d)
                d.EndGroup()

                if isBlock then
                    this.Block(c[index], d, true)
                else
                    this.Emit(c[index], d)

                this.All(c.SliceFrom(index + 1), d)

    member private _.TokenDepth(t: int) =
        if not hasConditionalStructure then
            0
        else
            if t < depthCursorToken then
                depthCursorToken <- -1
                depthAtCursor <- 0
                depthAfterCursor <- 0

            while depthCursorToken < t do
                let i = depthCursorToken + 1
                let token = &treeTokens[i]
                let mutable depth = depthAfterCursor

                for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                    usingProbes <- usingProbes + 1L
                    let item = &treeTrivia[j]

                    if item.Kind = TriviaKind.IfDirectiveTrivia then
                        depth <- depth + 1
                    elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                        depth <- max 0 (depth - 1)

                depthAtCursor <- depth

                for j = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                                  + token.LeadingCount
                                                                  + token.TrailingCount
                                                                  - 1 do
                    usingProbes <- usingProbes + 1L
                    let item = &treeTrivia[j]

                    if item.Kind = TriviaKind.IfDirectiveTrivia then
                        depth <- depth + 1
                    elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                        depth <- max 0 (depth - 1)

                depthAfterCursor <- depth
                depthCursorToken <- i

            depthAtCursor

    member private this.SplitsInheritedRun(c: IntSlice, runStart: int, split: int, finish: int) =
        let mutable plain = true
        let mutable j = if hasIgnores then runStart else split

        while plain && j < finish && this.Kind c[j] = NodeKind.UsingDirective do
            let token = tree.Token(this.First c[j])

            if
                hasIgnores
                && (this.IgnoreRange token.Start >= 0 || ignoredSingles.Contains token.Start)
            then
                plain <- false

            for t = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                usingProbes <- usingProbes + 1L
                let item = tree.Trivia t

                if
                    j >= split
                    && SyntaxFacts.directive item.Kind
                    && (j > split || item.Kind <> TriviaKind.EndIfDirectiveTrivia)
                then
                    plain <- false
                elif
                    hasIgnores
                    && item.Kind = TriviaKind.SingleLineCommentTrivia
                    && SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, item.Length).Trim()) > 0
                then
                    plain <- false

            j <- j + 1

        plain && not (this.FrameFollows(this.Last c[j - 1]))

    member private this.FrameFollows(last: int) =
        let mutable framed = false

        if last + 1 < tree.TokenCount then
            let token = tree.Token(last + 1)

            for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                usingProbes <- usingProbes + 1L
                let kind = (tree.Trivia j).Kind

                if
                    kind = TriviaKind.IfDirectiveTrivia
                    || kind = TriviaKind.ElifDirectiveTrivia
                    || kind = TriviaKind.ElseDirectiveTrivia
                    || kind = TriviaKind.EndIfDirectiveTrivia
                then
                    framed <- true

        framed

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.FlushUsings
        (
            c: IntSlice,
            start: int,
            finish: int,
            afterExtern: bool,
            nextIsEof: bool,
            nextHasEndMarker: bool,
            preserveOrder: bool,
            firstDepth: int,
            d: DocumentBuffer
        ) =
        if usingNodes.Count > 0 then
            this.Usings(usingNodes, d, afterExtern, preserveOrder, firstDepth)

            if hasIgnores then
                let last = usingNodes[usingNodes.Count - 1]
                let head = tree.Token(this.First usingNodes[0])
                let mutable markerHeader = false

                for j = head.TriviaStart to head.TriviaStart + head.LeadingCount - 1 do
                    let item = tree.Trivia j

                    if item.Kind = TriviaKind.SingleLineCommentTrivia then
                        let marker =
                            SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, item.Length).Trim())

                        markerHeader <- markerHeader || marker = 2 || marker = 3

                if
                    (this.IgnoreRange((tree.Token(this.First last)).Start) >= 0
                     || (markerHeader && firstDepth = 0))
                    && finish > start
                    && this.Kind c[finish - 1] <> NodeKind.UsingDirective
                    && not nextIsEof
                    && (not nextHasEndMarker
                        || (this.IgnoreRange head.Start >= 0
                            && this.IgnoreRange head.Start =
                                this.IgnoreRange((tree.Token(this.First last)).Start)))
                then
                    d.AddLine LineKind.Hard

            usingNodes.Clear()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.NamespaceContentsComplex
        (c: IntSlice, start: int, finish: int, d: DocumentBuffer)
        =
        usingNodes.Clear()
        let mutable previousCategory = -1
        let mutable previousKind = NodeKind.None
        let mutable previousControl = false
        let mutable afterExtern = false
        let mutable nextIsEof = false
        let mutable nextHasEndMarker = false
        let mutable usingDepth = 0
        let mutable usingFirstDepth = 0
        let mutable usingStart = start

        for i = start to finish - 1 do
            namespaceProbes <- namespaceProbes + 1L
            let child = c[i]
            let k = this.Kind child

            let category =
                if k = NodeKind.ExternAliasDirective then 0
                elif k = NodeKind.UsingDirective then 1
                elif k = NodeKind.AttributeList then 2
                else 3

            if category = 1 then
                let depth = this.TokenDepth(this.First child)

                if usingNodes.Count > 0 && depth < usingDepth then
                    if not (this.SplitsInheritedRun(c, usingStart, i, finish)) then
                        usingDepth <- 0
                    else
                        this.FlushUsings(
                            c,
                            start,
                            i,
                            afterExtern,
                            false,
                            false,
                            true,
                            usingFirstDepth,
                            d
                        )

                        this.Hard d

                if usingNodes.Count = 0 then
                    afterExtern <- previousCategory = 0
                    usingStart <- i
                    usingFirstDepth <- depth
                    let token = tree.Token(this.First child)
                    let mutable leadingDepth = 0

                    for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                        usingProbes <- usingProbes + 1L

                        if (tree.Trivia j).Kind = TriviaKind.IfDirectiveTrivia then
                            leadingDepth <- leadingDepth + 1
                        elif (tree.Trivia j).Kind = TriviaKind.EndIfDirectiveTrivia then
                            leadingDepth <- leadingDepth - 1

                    usingDepth <- min depth (depth - leadingDepth)

                if previousCategory >= 0 && previousCategory <> 1 then
                    this.Hard d

                usingNodes.Add child
            else
                nextIsEof <- this.At(child, TokenKind.EndOfFileToken)
                nextHasEndMarker <- false

                if child >= 0 then
                    let token = tree.Token(this.First child)

                    for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                        let item = tree.Trivia j

                        nextHasEndMarker <-
                            nextHasEndMarker
                            || (item.Kind = TriviaKind.SingleLineCommentTrivia
                                && SyntaxFacts.ignoreMarker (
                                    source.AsSpan(item.Start, item.Length).Trim()
                                )
                                    =
                                    3)

                this.FlushUsings(
                    c,
                    start,
                    finish,
                    afterExtern,
                    nextIsEof,
                    nextHasEndMarker,
                    false,
                    usingFirstDepth,
                    d
                )

                let mutable closing = -1
                let mutable disabledRegion = false
                let mutable endingMarker = false
                let mutable alternateAfterClosing = false

                if child >= 0 then
                    blankSibling <- if previousCategory >= 0 then this.First child else -1
                    let token = tree.Token(this.First child)

                    for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                        let trivia = tree.Trivia j

                        if
                            trivia.Kind = TriviaKind.SingleLineCommentTrivia
                            && SyntaxFacts.ignoreMarker (
                                source.AsSpan(trivia.Start, trivia.Length).Trim()
                            )
                                =
                                3
                        then
                            endingMarker <- true

                        if trivia.Kind = TriviaKind.DisabledTextTrivia then
                            disabledRegion <- true

                        if
                            trivia.Kind = TriviaKind.EndIfDirectiveTrivia
                            || trivia.Kind = TriviaKind.EndRegionDirectiveTrivia
                            || trivia.Kind = TriviaKind.BadDirectiveTrivia
                        then
                            closing <- j + 1
                            alternateAfterClosing <- false
                        elif
                            closing >= 0
                            && (trivia.Kind = TriviaKind.ElifDirectiveTrivia
                                || trivia.Kind = TriviaKind.ElseDirectiveTrivia)
                        then
                            alternateAfterClosing <- true

                    if closing >= 0 && not (ignoredSingles.Contains token.Start) then
                        if previousCategory >= 0 then
                            this.Hard d

                        let previousCompact = compactUsingTrivia
                        compactUsingTrivia <- previousCategory = 1
                        this.Trivia(this.First child, true, d, closing)
                        compactUsingTrivia <- previousCompact

                if
                    child >= 0
                    && previousCategory >= 0
                    && (ignoreUntil < 0 || treeTokens[this.First child].Start >= ignoreUntil)
                then
                    if
                        k = NodeKind.GlobalStatement
                        && previousKind = NodeKind.GlobalStatement
                        && not endingMarker
                        && not alternateAfterClosing
                        && (previousControl || this.ControlStatement child)
                    then
                        this.Blank d
                    elif closing >= 0 then
                        let mutable previousCloseHasIf = false

                        if i > start then
                            let closingTok = tree.Token(this.Last c[i - 1])

                            if closingTok.Kind = TokenKind.CloseBraceToken then
                                let mutable j = closingTok.TriviaStart
                                let triviaEnd = closingTok.TriviaStart + closingTok.LeadingCount

                                while not previousCloseHasIf && j < triviaEnd do
                                    if (tree.Trivia j).Kind = TriviaKind.IfDirectiveTrivia then
                                        previousCloseHasIf <- true

                                    j <- j + 1

                        if
                            disabledRegion
                            || alternateAfterClosing
                            || previousCloseHasIf
                            || this.EmptyConditionalPrefix(this.First child, closing)
                            || this.AdjacentAttributeRegion(child, closing)
                            || category <> 3
                            || previousCategory <> 3
                            || (k = NodeKind.GlobalStatement
                                && previousKind = NodeKind.GlobalStatement)
                            || (this.SimpleMember c[i - 1] && this.SimpleMember child)
                        then
                            this.Hard d
                        else
                            this.Blank d
                    elif
                        nextIsEof
                        && previousCategory = 1
                        && i > start
                        && this.IgnoreRange((tree.Token(this.First c[i - 1])).Start) >= 0
                    then
                        this.Hard d
                    elif
                        endingMarker
                        && (previousCategory <> 1
                            || (i > start
                                && this.IgnoreRange((tree.Token(this.First c[i - 1])).Start) >= 0))
                    then
                        this.Hard d
                    elif replayedTrailingFrame && previousCategory = 1 then
                        this.Hard d
                    elif
                        k = NodeKind.DelegateDeclaration
                        && previousKind = NodeKind.DelegateDeclaration
                        && not (this.HasTrivia(this.First child, true))
                    then
                        this.Hard d
                    elif
                        category <> previousCategory
                        || (category = 3
                            && (k <> NodeKind.GlobalStatement
                                || previousKind <> NodeKind.GlobalStatement)
                            && not (
                                this.SimpleMember c[i - 1]
                                && this.SimpleMember child
                                && not (this.HasTrivia(this.First child, true))
                            ))
                    then
                        this.Blank d
                    else
                        this.Hard d

                let previousCompact = compactUsingTrivia

                if nextIsEof && previousCategory = 1 && i > start then
                    let usingPosition = (tree.Token(this.First c[i - 1])).Start
                    compactUsingTrivia <- this.IgnoreRange usingPosition >= 0

                this.Emit(child, d)
                compactUsingTrivia <- previousCompact

            if child >= 0 then
                previousCategory <- category
                previousKind <- k
                previousControl <- this.ControlStatement child

        nextIsEof <- true

        this.FlushUsings(
            c,
            start,
            finish,
            afterExtern,
            nextIsEof,
            nextHasEndMarker,
            false,
            usingFirstDepth,
            d
        )

    member private this.NamespaceContents(c: IntSlice, start: int, finish: int, d: DocumentBuffer) =
        if hasDirectives || hasIgnores then
            this.NamespaceContentsComplex(c, start, finish, d)
        else
            usingNodes.Clear()
            let mutable previousCategory = -1
            let mutable previousKind = NodeKind.None
            let mutable previousControl = false
            let mutable afterExtern = false

            for i = start to finish - 1 do
                namespaceProbes <- namespaceProbes + 1L
                let child = c[i]
                let k = this.Kind child

                let category =
                    if k = NodeKind.ExternAliasDirective then 0
                    elif k = NodeKind.UsingDirective then 1
                    elif k = NodeKind.AttributeList then 2
                    else 3

                if category = 1 then
                    if usingNodes.Count = 0 then
                        afterExtern <- previousCategory = 0

                    if previousCategory >= 0 && previousCategory <> 1 then
                        this.Hard d

                    usingNodes.Add child
                else
                    if usingNodes.Count > 0 then
                        this.Usings(usingNodes, d, afterExtern)
                        usingNodes.Clear()

                    if child >= 0 then
                        blankSibling <- if previousCategory >= 0 then this.First child else -1

                        if previousCategory >= 0 then
                            if
                                k = NodeKind.GlobalStatement
                                && previousKind = NodeKind.GlobalStatement
                                && (previousControl || this.ControlStatement child)
                            then
                                this.Blank d
                            elif
                                k = NodeKind.DelegateDeclaration
                                && previousKind = NodeKind.DelegateDeclaration
                                && not (this.HasTrivia(this.First child, true))
                            then
                                this.Hard d
                            elif
                                category <> previousCategory
                                || (category = 3
                                    && (k <> NodeKind.GlobalStatement
                                        || previousKind <> NodeKind.GlobalStatement)
                                    && not (
                                        this.SimpleMember c[i - 1]
                                        && this.SimpleMember child
                                        && not (this.HasTrivia(this.First child, true))
                                    ))
                            then
                                this.Blank d
                            else
                                this.Hard d

                    this.Emit(child, d)

                if child >= 0 then
                    previousCategory <- category
                    previousKind <- k
                    previousControl <- this.ControlStatement child

            if usingNodes.Count > 0 then
                this.Usings(usingNodes, d, afterExtern)
                usingNodes.Clear()

    member private this.Namespace(n: int, d: DocumentBuffer) =
        let kind = this.Kind n

        let c =
            let all = this.Children n
            let mutable lead = 0

            if kind <> NodeKind.CompilationUnit then
                while lead < all.Length && this.Kind all[lead] = NodeKind.AttributeList do
                    this.Emit(all[lead], d)
                    this.Hard d
                    lead <- lead + 1

            if lead = 0 then all else all.SliceFrom lead

        let mutable start = 0
        let mutable finish = c.Length

        if kind <> NodeKind.CompilationUnit then
            this.Spaced(c.SliceRange(0, 1), d)
            start <- 3

            if kind = NodeKind.NamespaceDeclaration then
                finish <- this.SliceFindTokenBack(c, TokenKind.CloseBraceToken)
            else
                this.Emit(c[2], d)
                this.Blank d

        if kind = NodeKind.NamespaceDeclaration then
            if start = finish && not (this.HasTrivia(this.First c[finish], true)) then
                this.Space d
                this.Emit(c[2], d)
                this.Space d
                this.Emit(c[finish], d)
            else
                this.Hard d
                this.Emit(c[2], d)

                d.AddTag Tag.StartIndent
                this.Hard d
                suppressBlank <- this.First c[start]
                this.NamespaceContents(c, start, finish, d)
                this.ClosingTrivia(this.First c[finish], d)
                d.AddTag Tag.EndIndent

                if
                    finish > start
                    && this.Kind c[finish - 1] = NodeKind.UsingDirective
                    && (replayedTrailingFrame || usingEndings.Count > 0)
                then
                    d.AddReindent()

                this.Hard d
                this.All(c.SliceFrom finish, d)
        else
            this.NamespaceContents(c, start, finish, d)

    static member inline private NameWeight(c: char) =
        match c with
        | '\t' -> 0
        | ' ' -> 1
        | '_' -> 2
        | '-' -> 3
        | ',' -> 4
        | ';' -> 5
        | ':' -> 6
        | '!' -> 7
        | '?' -> 8
        | '.' -> 9
        | '\'' -> 10
        | '"' -> 11
        | '(' -> 12
        | ')' -> 13
        | '[' -> 14
        | ']' -> 15
        | '{' -> 16
        | '}' -> 17
        | '@' -> 18
        | '*' -> 19
        | '/' -> 20
        | '\\' -> 21
        | '&' -> 22
        | '#' -> 23
        | '%' -> 24
        | '`' -> 25
        | '^' -> 26
        | '+' -> 27
        | '<' -> 28
        | '=' -> 29
        | '>' -> 30
        | '|' -> 31
        | '~' -> 32
        | c when c >= '0' && c <= '9' -> 33 + int c - int '0'
        | c when c >= 'a' && c <= 'z' -> 43 + int c - int 'a'
        | c when c >= 'A' && c <= 'Z' -> 43 + int c - int 'A'
        | c -> 256 + int (Char.ToUpperInvariant c)

    member private this.CompareUsingKeys(a: UsingSortKey, b: UsingSortKey) =
        sortComparisons <- sortComparisons + 1L

        let result =
            if a.Tail && b.Tail then
                0
            elif a.Tail <> b.Tail then
                if a.Tail then 1 else -1
            elif a.Category <> b.Category then
                compare a.Category b.Category
            elif a.SystemBucket <> b.SystemBucket then
                compare a.SystemBucket b.SystemBucket
            elif a.Dotted <> b.Dotted then
                if a.Dotted then 1 else -1
            elif a.Nameless <> b.Nameless then
                compare a.Nameless b.Nameless
            else
                let spanA =
                    if isNull a.FallbackText then
                        source.AsSpan(a.TextStart, a.TextLength)
                    else
                        a.FallbackText.AsSpan()

                let spanB =
                    if isNull b.FallbackText then
                        source.AsSpan(b.TextStart, b.TextLength)
                    else
                        b.FallbackText.AsSpan()

                let shared = min spanA.Length spanB.Length
                let mutable cmp = 0
                let mutable i = 0

                while cmp = 0 && i < shared do
                    cmp <-
                        compare
                            (SyntaxNodePrinter.NameWeight spanA[i])
                            (SyntaxNodePrinter.NameWeight spanB[i])

                    i <- i + 1

                if cmp <> 0 then cmp else compare spanA.Length spanB.Length

        if result = 0 then
            compare a.InputIndex b.InputIndex
        else
            result

    member private this.SortUsingKeys(count: int) =
        let keys = usingKeys

        if count <= 24 then
            for i = 1 to count - 1 do
                let item = keys[i]
                let mutable j = i - 1

                while j >= 0 && this.CompareUsingKeys(keys[j], item) > 0 do
                    keys[j + 1] <- keys[j]
                    j <- j - 1

                keys[j + 1] <- item
        else
            let inline siftDown start finish =
                let mutable root = start
                let mutable item = keys[root]
                let mutable cont = true

                while cont do
                    let left = (root <<< 1) + 1

                    if left > finish then
                        cont <- false
                    else
                        let right = left + 1

                        let child =
                            if
                                right <= finish
                                && this.CompareUsingKeys(keys[left], keys[right]) < 0
                            then
                                right
                            else
                                left

                        if this.CompareUsingKeys(item, keys[child]) < 0 then
                            keys[root] <- keys[child]
                            root <- child
                        else
                            cont <- false

                keys[root] <- item

            let mutable i = (count >>> 1) - 1

            while i >= 0 do
                siftDown i (count - 1)
                i <- i - 1

            let mutable finish = count - 1

            while finish > 0 do
                let top = keys[0]
                keys[0] <- keys[finish]
                keys[finish] <- top
                finish <- finish - 1
                siftDown 0 finish

    member private this.FlushUsingReplays
        (
            limit: int,
            replayCursor: byref<int>,
            afterReplay: byref<bool>,
            emittedAny: byref<bool>,
            d: DocumentBuffer
        ) =
        while replayCursor < usingReplays.Count
              && (limit < 0
                  || (let struct (idx, _, _, _) = usingReplays[replayCursor] in idx < limit)) do
            let struct (_, tokenIndex, triviaStart, count) = usingReplays[replayCursor]

            if emittedAny then
                if afterReplay then this.Blank d else this.Hard d

            let mutable endsOnEndIf = false

            for j = triviaStart to triviaStart + count - 1 do
                seen[j] <- false
                let kind = (tree.Trivia j).Kind

                if kind <> TriviaKind.WhitespaceTrivia && kind <> TriviaKind.EndOfLineTrivia then
                    endsOnEndIf <- kind = TriviaKind.EndIfDirectiveTrivia

            let previousCompact = compactUsingTrivia
            compactUsingTrivia <- true
            this.Trivia(tokenIndex, true, d)
            compactUsingTrivia <- previousCompact
            emittedAny <- true
            afterReplay <- endsOnEndIf
            replayCursor <- replayCursor + 1

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PopulateUsingKey
        (i: int, n: int, nodeIgnored: bool, tail: bool)
        : UsingSortKey =
        let c = this.Children n
        let globalUsing = this.SliceContainsToken(c, TokenKind.GlobalKeyword)
        let staticUsing = this.SliceContainsToken(c, TokenKind.StaticKeyword)
        let aliasIdx = this.SliceFindKind(c, NodeKind.NameEquals)

        let name =
            if aliasIdx >= 0 then
                let ac = this.Children c[aliasIdx] in ac[0]
            else
                c[c.Length - 2]

        let struct (spanStart, spanLength) = tree.SourceSpan name
        let firstName = this.First name
        let lastName = this.Last name
        let mutable tokenLength = 0

        for index = firstName to lastName do
            tokenLength <- tokenLength + (tree.Token index).Length

        let mutable textStart = 0
        let mutable textLength = 0
        let mutable fallbackText: string = null

        let textSpan =
            if tokenLength = spanLength then
                textStart <- spanStart
                textLength <- spanLength
                source.AsSpan(spanStart, spanLength)
            else
                let nameText = Text.StringBuilder(tokenLength)

                for index = firstName to lastName do
                    let token = tree.Token index
                    nameText.Append(source, token.Start, token.Length) |> ignore

                fallbackText <- nameText.ToString()
                fallbackText.AsSpan()

        let globalQualified =
            textSpan.StartsWith("global::".AsSpan(), StringComparison.Ordinal)

        let mutable dotted = false

        if globalQualified then
            for t = firstName to lastName do
                if (tree.Token t).Kind = TokenKind.DotToken then
                    dotted <- true

        let nameless =
            aliasIdx >= 0
            && (let aliased = this.Kind c[c.Length - 2]

                aliased <> NodeKind.QualifiedName
                && aliased <> NodeKind.IdentifierName
                && aliased <> NodeKind.GenericName
                && aliased <> NodeKind.AliasQualifiedName)

        {
            Node = n
            Ignored = nodeIgnored
            Tail = tail
            Category =
                if globalUsing then (if aliasIdx >= 0 then 1 else 0)
                elif staticUsing then 3
                elif aliasIdx >= 0 then 4
                else 2
            SystemBucket =
                if textSpan.StartsWith("System".AsSpan(), StringComparison.Ordinal) then
                    0
                elif globalQualified then
                    1
                else
                    2
            Dotted = dotted
            Nameless = if nameless then 0 else 1
            TextStart = textStart
            TextLength = textLength
            FallbackText = fallbackText
            InputIndex = i
        }

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.UsingsComplex
        (
            nodes: ResizeArray<int>,
            d: DocumentBuffer,
            afterExtern: bool,
            preserveOrder: bool,
            firstDepth: int
        ) =
        let nodeCount = nodes.Count
        let firstToken = tree.Token(this.First nodes[0])

        let firstDepth =
            if firstDepth < 0 then
                this.TokenDepth(this.First nodes[0])
            else
                firstDepth

        if usingRelBefore.Length < nodeCount then
            Array.Resize(&usingRelBefore, max 32 (nodeCount * 2))
            Array.Resize(&usingRelAfter, max 32 (nodeCount * 2))

        let relBefore = usingRelBefore
        let relAfter = usingRelAfter
        let mutable preserve = preserveOrder || whitespaceOnly
        let mutable rel = 0
        let mutable runMarkers = false
        let mutable runIgnored = false
        let mutable laterDirectives = false
        let mutable leadingCloses = 0
        let mutable leadingOther = false

        for idx = 0 to nodeCount - 1 do
            let n = nodes[idx]
            let first, last = this.First n, this.Last n
            let token = tree.Token first
            relBefore[idx] <- rel
            let mutable localRegions = 0

            let position = token.Start

            if this.IgnoreRange position >= 0 || ignoredSingles.Contains position then
                runIgnored <- true

            for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                usingProbes <- usingProbes + 1L
                let item = tree.Trivia j
                let kind = item.Kind

                if kind = TriviaKind.IfDirectiveTrivia then
                    rel <- rel + 1
                elif kind = TriviaKind.EndIfDirectiveTrivia then
                    rel <- rel - 1

                    if rel < 0 then
                        if idx = 0 then
                            leadingCloses <- leadingCloses + 1
                        else
                            preserve <- true
                elif kind = TriviaKind.DisabledTextTrivia && rel > 0 then
                    let buffer =
                        match triviaTokens with
                        | ValueSome buffer -> buffer
                        | ValueNone ->
                            let buffer = TokenBuffer()
                            triviaTokens <- ValueSome buffer
                            buffer

                    Lexer.lexRange source item.Start (item.Start + item.Length) buffer

                    let mutable sawGlobal = false

                    for i = 0 to buffer.TokenCount - 1 do
                        let token = buffer.Token i

                        if
                            token.Kind = TokenKind.GlobalKeyword
                            || (token.Kind = TokenKind.IdentifierToken
                                && source
                                    .AsSpan(token.Start, token.Length)
                                    .SequenceEqual("global".AsSpan()))
                        then
                            sawGlobal <- true
                        elif token.Kind = TokenKind.UsingKeyword && sawGlobal then
                            preserve <- true
                        else
                            sawGlobal <- false
                elif kind = TriviaKind.RegionDirectiveTrivia then
                    localRegions <- localRegions + 1
                elif kind = TriviaKind.EndRegionDirectiveTrivia then
                    if localRegions > 0 then
                        localRegions <- localRegions - 1
                    else
                        preserve <- true
                elif
                    kind = TriviaKind.SingleLineCommentTrivia
                    && SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, item.Length).Trim()) > 0
                then
                    runMarkers <- true
                elif
                    idx > 0
                    && (kind = TriviaKind.DefineDirectiveTrivia
                        || kind = TriviaKind.UndefDirectiveTrivia
                        || kind = TriviaKind.NullableDirectiveTrivia
                        || kind = TriviaKind.LineDirectiveTrivia
                        || kind = TriviaKind.LineSpanDirectiveTrivia
                        || kind = TriviaKind.ErrorDirectiveTrivia
                        || kind = TriviaKind.WarningDirectiveTrivia
                        || kind = TriviaKind.PragmaWarningDirectiveTrivia
                        || kind = TriviaKind.PragmaChecksumDirectiveTrivia
                        || kind = TriviaKind.BadDirectiveTrivia)
                then
                    preserve <- true

                if idx > 0 && SyntaxFacts.directive kind then
                    laterDirectives <- true
                elif SyntaxFacts.directive kind && kind <> TriviaKind.EndIfDirectiveTrivia then
                    leadingOther <- true

            relAfter[idx] <- rel

            if idx > 0 && localRegions > 0 && not (relBefore[idx] > 0 && relAfter[idx] = 0) then
                preserve <- true

            if
                (relAfter[idx] > 0
                 || this.IgnoreRange token.Start >= 0
                 || ignoredSingles.Contains token.Start)
                && this.SliceContainsToken(this.Children n, TokenKind.GlobalKeyword)
            then
                preserve <- true

            for j = token.TriviaStart + token.LeadingCount to token.TriviaStart
                                                              + token.LeadingCount
                                                              + token.TrailingCount
                                                              - 1 do
                usingProbes <- usingProbes + 1L

                if SyntaxFacts.directive (tree.Trivia j).Kind then
                    preserve <- true

            for t = first + 1 to last do
                let token = tree.Token t

                for j = token.TriviaStart to token.TriviaStart
                                             + token.LeadingCount
                                             + token.TrailingCount
                                             - 1 do
                    usingProbes <- usingProbes + 1L

                    if SyntaxFacts.directive (tree.Trivia j).Kind then
                        preserve <- true

        if leadingCloses > 0 then
            if
                leadingOther
                || laterDirectives
                || runMarkers
                || runIgnored
                || this.FrameFollows(this.Last nodes[nodeCount - 1])
            then
                preserve <- true
            else
                for idx = 0 to nodeCount - 1 do
                    if idx > 0 then
                        relBefore[idx] <- relBefore[idx] + leadingCloses

                    relAfter[idx] <- relAfter[idx] + leadingCloses

        let mutable keepUntilEndIf = false
        let mutable headerCount = firstToken.LeadingCount
        let mutable headerDecided = false
        let mutable sawIf = false
        let mutable leadDelta = 0
        let mutable postIfRegions = 0

        for j = firstToken.TriviaStart to firstToken.TriviaStart + firstToken.LeadingCount - 1 do
            usingProbes <- usingProbes + 1L
            let item = tree.Trivia j

            if item.Kind = TriviaKind.IfDirectiveTrivia then
                leadDelta <- leadDelta + 1

                if not headerDecided && not sawIf then
                    sawIf <- true
                    headerCount <- j - firstToken.TriviaStart
            elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                leadDelta <- leadDelta - 1
            elif
                not headerDecided
                && (item.Kind = TriviaKind.DefineDirectiveTrivia
                    || item.Kind = TriviaKind.UndefDirectiveTrivia)
            then
                headerDecided <- true
                headerCount <- firstToken.LeadingCount
                postIfRegions <- 0
            elif sawIf && item.Kind = TriviaKind.RegionDirectiveTrivia then
                postIfRegions <- postIfRegions + 1
            elif sawIf && item.Kind = TriviaKind.EndRegionDirectiveTrivia then
                if postIfRegions > 0 then
                    postIfRegions <- postIfRegions - 1
                else
                    preserve <- true
            elif
                sawIf
                && (item.Kind = TriviaKind.NullableDirectiveTrivia
                    || item.Kind = TriviaKind.LineDirectiveTrivia
                    || item.Kind = TriviaKind.LineSpanDirectiveTrivia
                    || item.Kind = TriviaKind.PragmaWarningDirectiveTrivia
                    || item.Kind = TriviaKind.PragmaChecksumDirectiveTrivia
                    || item.Kind = TriviaKind.BadDirectiveTrivia)
            then
                preserve <- true
            elif not headerDecided && item.Kind = TriviaKind.DisabledTextTrivia then
                let buffer =
                    match triviaTokens with
                    | ValueSome buffer -> buffer
                    | ValueNone ->
                        let buffer = TokenBuffer()
                        triviaTokens <- ValueSome buffer
                        buffer

                Lexer.lexRange source item.Start (item.Start + item.Length) buffer

                for i = 0 to buffer.TokenCount - 1 do
                    if (buffer.Token i).Kind = TokenKind.ExternKeyword then
                        headerDecided <- true
                        keepUntilEndIf <- true
                        headerCount <- firstToken.LeadingCount
                        postIfRegions <- 0

        if postIfRegions > 0 then
            preserve <- true

        if headerDecided && not keepUntilEndIf && leadDelta <> 0 then
            preserve <- true

        if (runIgnored || runMarkers) && (laterDirectives || keepUntilEndIf) then
            preserve <- true

        let runDepth = firstDepth - leadDelta

        for idx = 1 to nodeCount - 1 do
            let token = tree.Token(this.First nodes[idx])

            for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                usingProbes <- usingProbes + 1L
                let item = tree.Trivia j

                if not preserve && item.Kind = TriviaKind.DisabledTextTrivia then
                    let buffer =
                        match triviaTokens with
                        | ValueSome buffer -> buffer
                        | ValueNone ->
                            let buffer = TokenBuffer()
                            triviaTokens <- ValueSome buffer
                            buffer

                    Lexer.lexRange source item.Start (item.Start + item.Length) buffer

                    for i = 0 to buffer.TokenCount - 1 do
                        if (buffer.Token i).Kind = TokenKind.ExternKeyword then
                            preserve <- true

        let ignored =
            hasIgnores
            && (this.IgnoreRange firstToken.Start >= 0
                || ignoredSingles.Contains firstToken.Start)

        let mutable headerDirective = false
        let mutable headerItems = 0
        let mutable unmatchedEnd = false
        let mutable singleMarker = false

        for j = firstToken.TriviaStart to firstToken.TriviaStart + firstToken.LeadingCount - 1 do
            let item = tree.Trivia j

            if
                item.Kind <> TriviaKind.WhitespaceTrivia
                && item.Kind <> TriviaKind.EndOfLineTrivia
            then
                headerItems <- headerItems + 1
                headerDirective <- headerDirective || SyntaxFacts.directive item.Kind

                if headerItems = 1 then
                    unmatchedEnd <-
                        item.Kind = TriviaKind.BadDirectiveTrivia
                        && source
                            .AsSpan(item.Start, item.Length)
                            .Trim()
                            .SequenceEqual("#endif".AsSpan())
                elif headerItems = 2 then
                    singleMarker <-
                        item.Kind = TriviaKind.SingleLineCommentTrivia
                        && SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, item.Length).Trim()) =
                            1

        let mutable hasUnignoredNode = false

        if
            not preserve
            && ignoredSingles.Contains firstToken.Start
            && headerItems = 2
            && unmatchedEnd
            && singleMarker
        then
            let mutable idx = 0

            while not hasUnignoredNode && idx < nodeCount do
                let position = (tree.Token(this.First nodes[idx])).Start

                if not (ignoredSingles.Contains position) && this.IgnoreRange position < 0 then
                    hasUnignoredNode <- true

                idx <- idx + 1

        let replayUnmatchedEnd = hasUnignoredNode

        if ignored && headerDirective && not replayUnmatchedEnd then
            preserve <- true

        if preserve then
            headerCount <- firstToken.LeadingCount

        let isAfterExtern = afterExtern

        blankSibling <-
            if preserve || isAfterExtern then
                this.First nodes[0]
            else
                -1

        let mutable hasHeaderTrivia = false

        if
            not ignored
            || (preserve && not (ignoredSingles.Contains firstToken.Start))
            || replayUnmatchedEnd
        then
            usingMasked.Clear()

            for j = firstToken.TriviaStart + headerCount to firstToken.TriviaStart
                                                            + firstToken.LeadingCount
                                                            - 1 do
                if not seen[j] then
                    seen[j] <- true
                    usingMasked.Add j

            if isAfterExtern then
                usingBlanks.Clear()
                let mutable header = false

                for j = firstToken.TriviaStart to firstToken.TriviaStart + headerCount - 1 do
                    if not seen[j] then
                        let kind = (tree.Trivia j).Kind

                        if kind = TriviaKind.EndOfLineTrivia && not header then
                            usingBlanks.Add j
                            seen[j] <- true
                        elif
                            kind <> TriviaKind.WhitespaceTrivia
                            && kind <> TriviaKind.EndOfLineTrivia
                        then
                            hasHeaderTrivia <- true
                            header <- header || SyntaxFacts.comment kind

                this.Trivia(this.First nodes[0], true, d)

                for i = 0 to usingBlanks.Count - 1 do
                    seen[usingBlanks[i]] <- false
            else
                this.Trivia(this.First nodes[0], true, d)

            for i = 0 to usingMasked.Count - 1 do
                seen[usingMasked[i]] <- false

            if replayUnmatchedEnd then
                for j = firstToken.TriviaStart to firstToken.TriviaStart + firstToken.LeadingCount
                                                  - 1 do
                    seen[j] <- false

            lastDeclinedLeadingToken <- -1

        let mutable startIndex = 0
        let mutable emittedAny = false

        if keepUntilEndIf && not preserve then
            let mutable stop = false

            while startIndex < nodeCount && not stop do
                let n = nodes[startIndex]
                let token = tree.Token(this.First n)
                let mutable sawEnd = false

                for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                    if (tree.Trivia j).Kind = TriviaKind.EndIfDirectiveTrivia then
                        sawEnd <- true

                if sawEnd && relAfter[startIndex] = 0 then
                    stop <- true

                if emittedAny then
                    this.Hard d

                blankSibling <- this.First n
                this.Emit(n, d)
                emittedAny <- true
                startIndex <- startIndex + 1

        usingReplays.Clear()

        if not configuredSymbolsReady then
            configuredSymbolsReady <- true
            configuredSymbols.Clear()

            match literalConfigurations with
            | ValueSome sets ->
                for set in sets do
                    for symbol in set do
                        configuredSymbols.Add symbol |> ignore
            | ValueNone -> ()

        let inline mentionsConfigured (item: Trivia) =
            if configuredSymbols.Count = 0 then
                false
            else
                let configuredLookup = configuredSymbols.GetAlternateLookup<ReadOnlySpan<char>>()
                let finish = item.Start + item.Length
                let mutable i = item.Start
                let mutable found = false

                while not found && i < finish do
                    if Char.IsLetter source[i] || source[i] = '_' then
                        let start = i

                        while i < finish && (Char.IsLetterOrDigit source[i] || source[i] = '_') do
                            i <- i + 1

                        found <- configuredLookup.Contains(source.AsSpan(start, i - start))
                    else
                        i <- i + 1

                found

        if not preserve then
            for idx = startIndex to nodeCount - 1 do
                let tokenIndex = this.First nodes[idx]
                let token = tree.Token tokenIndex

                if relAfter[idx] = 0 then
                    if relBefore[idx] > 0 then
                        usingReplays.Add(
                            struct (idx, tokenIndex, token.TriviaStart, token.LeadingCount)
                        )
                    else
                        let scanStart =
                            if idx = 0 then
                                token.TriviaStart + headerCount
                            else
                                token.TriviaStart

                        let mutable depth = 0
                        let mutable firstFrameStart = -1
                        let mutable lastFrameEnd = -1
                        let mutable frameUsing = false
                        let mutable frameConfigured = false
                        let mutable anyReplayed = false

                        for j = scanStart to token.TriviaStart + token.LeadingCount - 1 do
                            let item = tree.Trivia j

                            if item.Kind = TriviaKind.IfDirectiveTrivia then
                                if depth = 0 then
                                    if firstFrameStart < 0 then
                                        firstFrameStart <- j

                                    frameUsing <- false
                                    frameConfigured <- false

                                depth <- depth + 1

                                if mentionsConfigured item then
                                    frameConfigured <- true
                            elif
                                depth > 0
                                && (item.Kind = TriviaKind.ElifDirectiveTrivia
                                    || item.Kind = TriviaKind.ElseDirectiveTrivia)
                            then
                                if mentionsConfigured item then
                                    frameConfigured <- true
                            elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                                depth <- depth - 1

                                if depth = 0 then
                                    lastFrameEnd <- j

                                    if frameUsing && frameConfigured then
                                        anyReplayed <- true
                            elif
                                depth = 0 && firstFrameStart >= 0 && SyntaxFacts.directive item.Kind
                            then
                                lastFrameEnd <- token.TriviaStart + token.LeadingCount - 1
                            elif depth > 0 && item.Kind = TriviaKind.DisabledTextTrivia then
                                let buffer =
                                    match triviaTokens with
                                    | ValueSome buffer -> buffer
                                    | ValueNone ->
                                        let buffer = TokenBuffer()
                                        triviaTokens <- ValueSome buffer
                                        buffer

                                Lexer.lexRange source item.Start (item.Start + item.Length) buffer

                                for i = 0 to buffer.TokenCount - 1 do
                                    if (buffer.Token i).Kind = TokenKind.UsingKeyword then
                                        frameUsing <- true

                        if
                            firstFrameStart >= 0
                            && lastFrameEnd >= firstFrameStart
                            && (anyReplayed || usingReplays.Count > 0)
                        then
                            usingReplays.Add(
                                struct (idx,
                                        tokenIndex,
                                        firstFrameStart,
                                        lastFrameEnd - firstFrameStart + 1)
                            )

            for i = 0 to usingReplays.Count - 1 do
                let struct (_, _, triviaStart, count) = usingReplays[i]

                for j = triviaStart to triviaStart + count - 1 do
                    seen[j] <- true

        let mutable markerHeader = false

        if not preserve && hasIgnores then
            for j = firstToken.TriviaStart to firstToken.TriviaStart + firstToken.LeadingCount - 1 do
                let item = tree.Trivia j

                if item.Kind = TriviaKind.SingleLineCommentTrivia then
                    markerHeader <-
                        markerHeader
                        || SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, item.Length).Trim()) =
                            3

        if hasIgnores && not isAfterExtern && not markerHeader then
            for idx = 0 to nodeCount - 1 do
                literalUsingEnds.Add(this.Last nodes[idx]) |> ignore

        usingEndings.Clear()

        if not preserve && hasIgnores then
            for idx = 0 to nodeCount - 1 do
                let node = nodes[idx]
                let tokenIndex = this.First node
                let token = tree.Token tokenIndex

                for i = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                    let item = tree.Trivia i

                    if
                        item.Kind = TriviaKind.SingleLineCommentTrivia
                        && not seen[i]
                        && SyntaxFacts.ignoreMarker (source.AsSpan(item.Start, item.Length).Trim()) =
                            3
                    then
                        let literal = usingEndings.Count = 0 && this.LiteralIgnoreGap tokenIndex
                        let mutable gap = i

                        while literal
                              && gap > token.TriviaStart
                              && not seen[gap - 1]
                              && ((tree.Trivia(gap - 1)).Kind = TriviaKind.WhitespaceTrivia
                                  || (tree.Trivia(gap - 1)).Kind = TriviaKind.EndOfLineTrivia) do
                            gap <- gap - 1

                        if literal && gap > token.TriviaStart then
                            let comment = tree.Trivia(gap - 1)

                            if
                                SyntaxFacts.comment comment.Kind
                                && not (
                                    SyntaxFacts.lineTerminator
                                        source[comment.Start + comment.Length - 1]
                                )
                            then
                                let mutable lineBreak = gap

                                while lineBreak < i
                                      && (tree.Trivia lineBreak).Kind = TriviaKind.WhitespaceTrivia do
                                    lineBreak <- lineBreak + 1

                                if lineBreak < i then
                                    gap <- lineBreak + 1

                        for j = gap to i - 1 do
                            seen[j] <- true

                        usingEndings.Add(struct (tokenIndex, i, gap, literal))
                        seen[i] <- true
                        let mutable next = i + 1

                        while next < token.TriviaStart + token.LeadingCount
                              && (tree.Trivia next).Kind = TriviaKind.WhitespaceTrivia do
                            next <- next + 1

                        if
                            next < token.TriviaStart + token.LeadingCount
                            && (tree.Trivia next).Kind = TriviaKind.EndOfLineTrivia
                        then
                            seen[next] <- true

        let keyedCount = nodeCount - startIndex

        if usingKeys.Length < keyedCount then
            Array.Resize(&usingKeys, max 32 (keyedCount * 2))

        for offset = 0 to keyedCount - 1 do
            let i = startIndex + offset
            let n = nodes[i]
            let position = (tree.Token(this.First n)).Start

            let nodeIgnored =
                hasIgnores
                && (this.IgnoreRange position >= 0 || ignoredSingles.Contains position)

            let tail = nodeIgnored || relAfter[i] > 0

            if preserve then
                usingKeys[offset] <-
                    {
                        Node = n
                        Ignored = nodeIgnored
                        Tail = tail
                        Category = 0
                        SystemBucket = 0
                        Dotted = false
                        Nameless = 0
                        TextStart = 0
                        TextLength = 0
                        FallbackText = null
                        InputIndex = i
                    }
            else
                usingKeys[offset] <- this.PopulateUsingKey(i, n, nodeIgnored, tail)

        if not preserve && usingReplays.Count > 0 then
            sortedUsings <- true

        if not preserve && keyedCount > 1 then
            this.SortUsingKeys keyedCount

            let mutable index = 1

            while not sortedUsings && index < keyedCount do
                if usingKeys[index].InputIndex < usingKeys[index - 1].InputIndex then
                    sortedUsings <- true

                index <- index + 1

        let mutable replayCursor = 0
        let mutable afterReplay = false

        for i = 0 to keyedCount - 1 do
            let entry = usingKeys[i]
            let node = entry.Node
            let nodeIgnored = entry.Ignored
            let tail = entry.Tail
            let inputIndex = entry.InputIndex

            let externHead =
                (if usingReplays.Count > 0 then i = 0 else node = nodes[0]) && isAfterExtern

            let externBlank = isAfterExtern && usingReplays.Count = 0

            if ignoreUntil < 0 || treeTokens[this.First node].Start >= ignoreUntil then
                if tail && not preserve then
                    this.FlushUsingReplays(inputIndex, &replayCursor, &afterReplay, &emittedAny, d)

                blankSibling <-
                    if preserve || externHead || externBlank then
                        this.First node
                    else
                        -1

                if emittedAny then
                    if
                        nodeIgnored
                        && not preserve
                        && isAfterExtern
                        && not (ignoredSingles.Contains((tree.Token(this.First node)).Start))
                    then
                        this.Blank d
                    elif afterReplay then
                        this.Blank d
                    else
                        this.Hard d

                afterReplay <- false

                if not nodeIgnored && not preserve && not externHead && not externBlank then
                    suppressBlank <- this.First node

                let previousCompact = compactUsingTrivia

                compactUsingTrivia <-
                    (if preserve then firstDepth = 0 else runDepth = 0)
                    && not externHead
                    && not externBlank

                if
                    i = 0
                    && not hasHeaderTrivia
                    && externBlank
                    && not nodeIgnored
                    && not preserve
                    && node <> nodes[0]
                then
                    let tokenIndex = this.First node
                    let token = tree.Token tokenIndex
                    usingBlanks.Clear()
                    let mutable header = false

                    for j = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                        if not seen[j] then
                            let kind = (tree.Trivia j).Kind

                            if kind = TriviaKind.EndOfLineTrivia && not header then
                                usingBlanks.Add j
                                seen[j] <- true
                            elif
                                kind <> TriviaKind.WhitespaceTrivia
                                && kind <> TriviaKind.EndOfLineTrivia
                            then
                                header <- header || SyntaxFacts.comment kind

                    if header && usingBlanks.Count > 0 then
                        this.Trivia(tokenIndex, true, d)
                        lastDeclinedLeadingToken <- -1

                    for k = 0 to usingBlanks.Count - 1 do
                        seen[usingBlanks[k]] <- false

                this.Emit(node, d)
                compactUsingTrivia <- previousCompact
                emittedAny <- true

        if not preserve then
            this.FlushUsingReplays(-1, &replayCursor, &afterReplay, &emittedAny, d)

        replayedTrailingFrame <- afterReplay

        if markerHeader then
            this.Blank d

        for i = 0 to usingEndings.Count - 1 do
            let struct (token, index, gap, literal) = usingEndings[i]

            if emittedAny then
                if literal then
                    this.Hard d
                else
                    let holder = tree.Token token
                    let mutable blank = false
                    let mutable scanning = true
                    let mutable j = index - 1

                    while scanning && j >= holder.TriviaStart do
                        match (tree.Trivia j).Kind with
                        | TriviaKind.WhitespaceTrivia -> j <- j - 1
                        | TriviaKind.EndOfLineTrivia ->
                            blank <- true
                            scanning <- false
                        | _ -> scanning <- false

                    if blank then this.Blank d else this.Hard d

            for j = gap to index do
                seen[j] <- false

            if i > 0 then
                usingEndingsJoin <- token

            this.Trivia(token, true, d)

        if usingEndings.Count > 0 then
            usingEndingsJoin <- this.Last nodes[nodeCount - 1] + 1

    member private this.Usings
        (
            nodes: ResizeArray<int>,
            d: DocumentBuffer,
            [<Optional; DefaultParameterValue(false)>] afterExtern: bool,
            [<Optional; DefaultParameterValue(false)>] preserveOrder: bool,
            [<Optional; DefaultParameterValue(-1)>] firstDepth: int
        ) =
        if hasDirectives || hasIgnores || afterExtern then
            this.UsingsComplex(nodes, d, afterExtern, preserveOrder, firstDepth)
        else
            let nodeCount = nodes.Count
            blankSibling <- -1
            this.Trivia(this.First nodes[0], true, d)
            lastDeclinedLeadingToken <- -1
            replayedTrailingFrame <- false

            if usingKeys.Length < nodeCount then
                Array.Resize(&usingKeys, max 32 (nodeCount * 2))

            for i = 0 to nodeCount - 1 do
                usingKeys[i] <- this.PopulateUsingKey(i, nodes[i], false, false)

            if nodeCount > 1 then
                this.SortUsingKeys nodeCount

                let mutable index = 1

                while not sortedUsings && index < nodeCount do
                    if usingKeys[index].InputIndex < usingKeys[index - 1].InputIndex then
                        sortedUsings <- true

                    index <- index + 1

            let previousCompact = compactUsingTrivia
            compactUsingTrivia <- true

            for i = 0 to nodeCount - 1 do
                let node = usingKeys[i].Node
                blankSibling <- -1

                if i > 0 then
                    this.Hard d

                suppressBlank <- this.First node
                this.Emit(node, d)

            compactUsingTrivia <- previousCompact

    member private this.Control(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let kind = this.Kind n
        let close = this.SliceFindToken(c, TokenKind.CloseParenToken)

        if
            close < 0
            || kind = NodeKind.ForStatement
            || kind = NodeKind.LockStatement
            || close + 1 >= c.Length
            || this.Kind c[close + 1] <> NodeKind.Block
            || (kind = NodeKind.IfStatement
                && (let body = this.Children c[close + 1] in body.Length <= 2))
        then
            this.ControlCold(kind, c, close, d)
        else
            let opening = this.SliceFindToken(c, TokenKind.OpenParenToken)
            d.StartGroup() |> ignore
            this.Spaced(c.SliceRange(0, opening - 1), d)
            this.Space d
            d.StartGroup() |> ignore
            this.Emit(c[opening], d)
            d.AddTag Tag.StartIndent

            if close > opening + 1 then
                d.AddLine LineKind.Soft

            for i = opening + 1 to close - 1 do
                let child = c[i]

                if i > opening + 1 && not (this.At(child, TokenKind.CommaToken)) then
                    this.Space d

                if SyntaxFacts.binary (this.Kind child) then
                    let operands = this.Children child

                    this.Binary(
                        child,
                        d,
                        false,
                        inheritMode =
                            (kind = NodeKind.IfStatement
                             && operands.Length = 3
                             && (SyntaxFacts.binary (this.Kind operands[0])
                                 || this.Kind operands[0] = NodeKind.IsPatternExpression
                                 || SyntaxFacts.binary (this.Kind operands[2])))
                    )
                else
                    this.Emit(child, d)

            d.AddTag Tag.EndIndent

            if close > opening + 1 then
                d.AddLine LineKind.Soft

            this.Emit(c[close], d)
            d.EndGroup()
            d.EndGroup()

            this.Block(c[close + 1], d, true)

            for i = close + 2 to c.Length - 1 do
                this.Hard d
                this.Emit(c[i], d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ControlCold(kind: NodeKind, c: IntSlice, close: int, d: DocumentBuffer) =
        if close < 0 then
            this.Spaced(c, d)
        else
            let opening = this.SliceFindToken(c, TokenKind.OpenParenToken)

            let emptyBody =
                (kind = NodeKind.IfStatement || kind = NodeKind.ForStatement)
                && close + 1 < c.Length
                && this.Kind c[close + 1] = NodeKind.Block
                && let body = this.Children c[close + 1] in

                   body.Length = 2
                   && not (this.HasTrivia(this.First body[0], false))
                   && not (this.HasTrivia(this.First body[1], true))

            if emptyBody then
                d.StartGroup() |> ignore

            let incrementorStart =
                if kind = NodeKind.ForStatement then
                    this.SliceFindTokenBack(c, TokenKind.SemicolonToken) + 1
                else
                    close

            let header = d.StartGroup()
            this.Spaced(c.SliceRange(0, opening - 1), d)
            this.Space d
            let id = d.StartGroup()
            this.Emit(c[opening], d)

            let isLock = kind = NodeKind.LockStatement

            if not isLock then
                d.AddTag Tag.StartIndent

            if close > opening + 1 && not isLock then
                d.AddLine LineKind.Soft

            for i = opening + 1 to close - 1 do
                let child = c[i]

                if i > opening + 1 then
                    if this.At(c[i - 1], TokenKind.SemicolonToken) then
                        d.AddLine LineKind.Normal
                    elif
                        not (this.At(child, TokenKind.CommaToken))
                        && not (this.At(child, TokenKind.SemicolonToken))
                    then
                        this.Space d

                if i >= incrementorStart then
                    d.AddTag Tag.StartIndent

                if SyntaxFacts.binary (this.Kind child) then
                    let operands = this.Children child

                    this.Binary(
                        child,
                        d,
                        false,
                        inheritMode =
                            (kind = NodeKind.IfStatement
                             && operands.Length = 3
                             && (SyntaxFacts.binary (this.Kind operands[0])
                                 || this.Kind operands[0] = NodeKind.IsPatternExpression
                                 || SyntaxFacts.binary (this.Kind operands[2])))
                    )
                else
                    this.Emit(child, d)

                if i >= incrementorStart then
                    d.AddTag Tag.EndIndent

            if kind = NodeKind.ForStatement && this.At(c[close - 1], TokenKind.SemicolonToken) then
                d.AddTag(Tag.StartIfBreak, id)
                d.AddLine LineKind.Normal
                d.AddTag Tag.EndIfBreak

            if not isLock then
                d.AddTag Tag.EndIndent

            if close > opening + 1 && not isLock then
                d.AddLine(
                    if this.At(c[close - 1], TokenKind.SemicolonToken) then
                        LineKind.Normal
                    else
                        LineKind.Soft
                )

            this.Emit(c[close], d)
            ignore id
            d.EndGroup()
            d.EndGroup()

            if close + 1 < c.Length then
                let body = c[close + 1]

                if this.Kind body = NodeKind.Block then
                    if emptyBody then
                        d.AddTag(Tag.StartIfBreak, header)
                        this.Space d
                        d.AddTag Tag.Else
                        d.AddLine LineKind.Normal
                        d.AddTag Tag.EndIfBreak

                        this.Block(body, d, false)
                    else
                        this.Block(body, d, true)
                else
                    let nested = this.Kind body = kind && kind <> NodeKind.IfStatement

                    if nested then
                        this.Hard d

                        if
                            this.Kind body = NodeKind.ForEachStatement
                            || this.Kind body = NodeKind.ForEachVariableStatement
                            || this.Kind body = NodeKind.FixedStatement
                        then
                            blankSibling <- this.First body

                        this.Emit(body, d)
                    else
                        d.AddTag Tag.StartIndent
                        this.Hard d
                        this.Emit(body, d)
                        d.AddTag Tag.EndIndent

                if emptyBody then
                    d.EndGroup()

                for i = close + 2 to c.Length - 1 do
                    this.Hard d
                    this.Emit(c[i], d)

    member private this.IndexIgnores() =
        if not indexedIgnores then
            let mutable markers = ValueNone

            let limit =
                if tree.TriviaCount = tree.LexerBuffer.TriviaCount then
                    max tree.LexerBuffer.LastCommentTrivia tree.LexerBuffer.LastNonCommentTrivia + 1
                else
                    tree.TriviaCount

            for i = 0 to limit - 1 do
                let trivia = &treeTrivia[i]
                let kind = trivia.Kind

                if kind <> TriviaKind.WhitespaceTrivia && kind <> TriviaKind.EndOfLineTrivia then
                    if kind = TriviaKind.ConflictMarkerTrivia then
                        invalidOp "Cannot format unresolved merge conflict markers."

                    if SyntaxFacts.comment kind then
                        hasComments <- true

                    if
                        SyntaxFacts.directive kind
                        || kind = TriviaKind.DisabledTextTrivia
                        || kind = TriviaKind.SkippedTokensTrivia
                    then
                        hasDirectives <- true

                        if firstDirectiveTrivia > tree.TriviaCount then
                            firstDirectiveTrivia <- i

                        lastDirectiveTrivia <- i

                        if
                            kind = TriviaKind.IfDirectiveTrivia
                            || kind = TriviaKind.ElifDirectiveTrivia
                            || kind = TriviaKind.ElseDirectiveTrivia
                            || kind = TriviaKind.EndIfDirectiveTrivia
                            || kind = TriviaKind.DisabledTextTrivia
                        then
                            hasConditionalStructure <- true

                    if kind = TriviaKind.SingleLineCommentTrivia && trivia.Length >= 14 then
                        let text = source.AsSpan(trivia.Start, trivia.Length).Trim()

                        let marker = SyntaxFacts.ignoreMarker text

                        if marker > 0 then
                            let list =
                                match markers with
                                | ValueSome list -> list
                                | ValueNone ->
                                    let list = ResizeArray<struct (int * int * int)>()
                                    markers <- ValueSome list
                                    list

                            list.Add(struct (trivia.Start, trivia.Start + trivia.Length, marker))

            match markers with
            | ValueNone -> ()
            | ValueSome markers -> this.IndexIgnoreMarkers markers

            indexedIgnores <- true

            if not hasConditionalStructure then
                indexedConditionals <- true

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.IndexIgnoreMarkers(markers: ResizeArray<struct (int * int * int)>) =
        hasIgnores <- true
        let laterMarkers = HashSet<int>()
        let emptyRangeHeaders = HashSet<int>()

        for n = 0 to tree.NodeCount - 1 do
            let kind = this.Kind n

            if kind = NodeKind.FieldDeclaration then
                emptyRangeHeaders.Add(this.First n) |> ignore
            elif
                kind = NodeKind.ArrayInitializerExpression
                || kind = NodeKind.ObjectInitializerExpression
                || kind = NodeKind.CollectionInitializerExpression
                || kind = NodeKind.ComplexElementInitializerExpression
                || kind = NodeKind.WithInitializerExpression
            then
                let children = this.Children n

                for idx = 0 to children.Length - 1 do
                    let child = children[idx]

                    if child >= 0 then
                        emptyRangeHeaders.Add(this.First child) |> ignore

        let mutable headerDepth = 0

        for t = 0 to tree.TokenCount - 1 do
            let token = tree.Token t
            let mutable found = false

            for i = token.TriviaStart to token.TriviaStart + token.LeadingCount - 1 do
                let trivia = tree.Trivia i

                if
                    trivia.Kind = TriviaKind.SingleLineCommentTrivia
                    && SyntaxFacts.ignoreMarker (source.AsSpan(trivia.Start, trivia.Length).Trim()) >
                        0
                then
                    let marker =
                        SyntaxFacts.ignoreMarker (source.AsSpan(trivia.Start, trivia.Length).Trim())

                    if
                        found
                        && ((marker = 2
                             && (headerDepth = 0 || token.Kind = TokenKind.NamespaceKeyword))
                            || (marker = 3
                                && t > 0
                                && headerDepth > 0
                                && token.Kind <> TokenKind.NamespaceKeyword
                                && not (emptyRangeHeaders.Contains t)))
                    then
                        laterMarkers.Add trivia.Start |> ignore

                    found <- true

            if token.Kind = TokenKind.OpenBraceToken then
                headerDepth <- headerDepth + 1
            elif token.Kind = TokenKind.CloseBraceToken then
                headerDepth <- max 0 (headerDepth - 1)

        markers.RemoveAll(fun struct (start, _, _) -> laterMarkers.Contains start)
        |> ignore

        let ordered = markers.ToArray()
        Array.sortInPlaceBy (fun struct (start, _, _) -> start) ordered

        let mutable ending = 0
        let mutable range = -1
        let mutable rangeEnd = source.Length
        let mutable rangeDepth = 0
        let mutable token = 0

        let closes =
            Array.create (if ordered.Length > 0 then tree.TokenCount else 0) source.Length

        let scopes = Stack<int>()

        for i = 0 to closes.Length - 1 do
            let item = tree.Token i

            if item.Kind = TokenKind.OpenBraceToken then
                scopes.Push i
            elif item.Kind = TokenKind.CloseBraceToken && scopes.Count > 0 then
                closes[scopes.Pop()] <- item.Start

        if ordered.Length > 0 then
            for i = 0 to tree.NodeCount - 1 do
                let kind = this.Kind i

                if
                    kind = NodeKind.CompilationUnit
                    || kind = NodeKind.NamespaceDeclaration
                    || kind = NodeKind.FileScopedNamespaceDeclaration
                then
                    let children = this.Children i
                    let mutable first = 0

                    while first < children.Length do
                        if this.Kind children[first] = NodeKind.UsingDirective then
                            let mutable last = first

                            while last + 1 < children.Length
                                  && this.Kind children[last + 1] = NodeKind.UsingDirective do
                                last <- last + 1

                            let lastToken = tree.Token(this.Last children[last])
                            let mutable finish = lastToken.End

                            for j = lastToken.TriviaStart + lastToken.LeadingCount to lastToken
                                                                                          .TriviaStart
                                                                                      + lastToken
                                                                                          .LeadingCount
                                                                                      + lastToken
                                                                                          .TrailingCount
                                                                                      - 1 do
                                let item = tree.Trivia j

                                if SyntaxFacts.comment item.Kind then
                                    finish <- item.Start + item.Length

                            for j = first to last do
                                importEnds[(tree.Token(this.First children[j])).Start] <- finish

                            first <- last + 1
                        else
                            first <- first + 1

        let continuationEnds = Dictionary<int, int>()

        for n = 0 to tree.NodeCount - 1 do
            if this.Kind n = NodeKind.DoStatement then
                let children = this.Children n

                for idx = 0 to children.Length - 1 do
                    let child = children[idx]

                    if this.At(child, TokenKind.WhileKeyword) then
                        let ending = tree.Token(this.Last n)
                        continuationEnds[(tree.Token(this.First child)).Start] <- ending.End

        scopes.Clear()
        let mutable scopeToken = 0

        for struct (start, finish, marker) in ordered do
            while ending < ordered.Length
                  && (let struct (position, _, kind) = ordered[ending] in
                      position <= start || kind <> 3) do
                ending <- ending + 1

            while scopeToken < tree.TokenCount && (tree.Token scopeToken).Start < start do
                let item = tree.Token scopeToken

                if item.Kind = TokenKind.OpenBraceToken then
                    scopes.Push scopeToken
                elif item.Kind = TokenKind.CloseBraceToken && scopes.Count > 0 then
                    scopes.Pop() |> ignore

                scopeToken <- scopeToken + 1

            if range >= 0 && start >= rangeEnd then
                ignoredRanges.Add(struct (range, rangeEnd))
                range <- -1

            if marker = 2 then
                if range < 0 then
                    range <- finish
                    rangeDepth <- scopes.Count

                    rangeEnd <-
                        if scopes.Count > 0 then
                            closes[scopes.Peek()]
                        else
                            source.Length

                    while token < tree.TokenCount && (tree.Token token).Start < finish do
                        token <- token + 1

                    if token < tree.TokenCount then
                        match importEnds.TryGetValue((tree.Token token).Start) with
                        | true, finish ->
                            let endMarker =
                                if ending < ordered.Length then
                                    let struct (position, _, _) = ordered[ending] in position
                                else
                                    source.Length

                            if endMarker <= finish || endMarker >= rangeEnd then
                                rangeEnd <- min rangeEnd finish
                        | _ -> ()

                        match continuationEnds.TryGetValue((tree.Token token).Start) with
                        | true, finish -> rangeEnd <- min rangeEnd finish
                        | _ -> ()
            elif marker = 3 then
                if range >= 0 && scopes.Count <= rangeDepth then
                    let mutable line = start

                    while token < tree.TokenCount && (tree.Token token).Start < finish do
                        token <- token + 1

                    if token < tree.TokenCount then
                        let next = tree.Token token

                        if next.LeadingCount > 0 then
                            line <- min line (tree.Trivia next.TriviaStart).Start

                    while line > 0 && (source[line - 1] = ' ' || source[line - 1] = '\t') do
                        line <- line - 1

                    ignoredRanges.Add(struct (range, min line rangeEnd))
                    range <- -1
            else
                while token < tree.TokenCount && (tree.Token token).Start < finish do
                    token <- token + 1

                if token < tree.TokenCount then
                    ignoredSingles.Add((tree.Token token).Start) |> ignore

        if range >= 0 then
            ignoredRanges.Add(struct (range, rangeEnd))

    member private this.IgnoreRange(position: int) =
        let mutable lo = 0
        let mutable hi = ignoredRanges.Count

        while lo < hi do
            let mid = lo + (hi - lo) / 2
            let struct (first, _) = ignoredRanges[mid]
            if first <= position then lo <- mid + 1 else hi <- mid

        if lo = 0 then
            -1
        else
            let struct (_, finish) = ignoredRanges[lo - 1]
            if position < finish then finish else -1

    member private this.LiteralIgnoreGap(t: int) =
        t > 0
        && t <> usingEndingsJoin
        && literalUsingEnds.Contains(t - 1)
        && (let finish = this.IgnoreRange treeTokens[t - 1].Start
            finish >= 0 && finish <= (tree.Trivia treeTokens[t].TriviaStart).Start)

    member private this.IgnoreNode
        (n: int, d: DocumentBuffer, [<Optional; DefaultParameterValue(-1)>] firstToken: int)
        =
        let first = if firstToken < 0 then this.First n else firstToken
        let position = (tree.Token first).Start

        if position < ignoreUntil then
            true
        else
            let kind = this.Kind n
            let c = this.Children n

            let range = this.IgnoreRange position
            let single = ignoredSingles.Contains position

            let attributes =
                first = this.First n
                && c.Length > 0
                && this.Kind c[0] = NodeKind.AttributeList
                && (kind = NodeKind.MethodDeclaration
                    || kind = NodeKind.ConstructorDeclaration
                    || kind = NodeKind.DestructorDeclaration
                    || kind = NodeKind.OperatorDeclaration
                    || kind = NodeKind.ConversionOperatorDeclaration)

            let ignoredSingle = single && not attributes && kind <> NodeKind.CompilationUnit

            if not ignoredSingle && (kind = NodeKind.CompilationUnit || range < 0) then
                false
            else
                this.IndexConditionals()
                let leading = tree.Token first
                let mutable markerIndex = -1
                let mutable disabledPrefix = false
                let mutable depth = 0
                let mutable opening = -1
                let mutable openingIndex = -1
                let mutable firstKind = TriviaKind.None
                let mutable alternatePrefix = false
                let mutable markerBranch = TriviaKind.None
                let mutable printablePrefix = true
                let mutable nestedAfterMarker = false
                let mutable markerDepth = 0
                let mutable verbatimPrefix = false
                let mutable closedPrefix = false

                for i = leading.TriviaStart to leading.TriviaStart + leading.LeadingCount - 1 do
                    let item = tree.Trivia i

                    if
                        firstKind = TriviaKind.None
                        && item.Kind <> TriviaKind.WhitespaceTrivia
                        && item.Kind <> TriviaKind.EndOfLineTrivia
                    then
                        firstKind <- item.Kind

                    if item.Kind = TriviaKind.IfDirectiveTrivia then
                        nestedAfterMarker <-
                            nestedAfterMarker || (markerIndex >= 0 && depth >= markerDepth)

                        if opening < 0 then
                            opening <- item.Start
                            openingIndex <- i

                        depth <- depth + 1
                    elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                        depth <- max 0 (depth - 1)
                        closedPrefix <- true

                    if markerIndex < 0 then
                        if
                            item.Kind = TriviaKind.IfDirectiveTrivia
                            || item.Kind = TriviaKind.ElifDirectiveTrivia
                            || item.Kind = TriviaKind.ElseDirectiveTrivia
                        then
                            markerBranch <- item.Kind

                        if
                            item.Kind = TriviaKind.ElifDirectiveTrivia
                            || item.Kind = TriviaKind.ElseDirectiveTrivia
                        then
                            alternatePrefix <- true

                        if item.Kind = TriviaKind.DisabledTextTrivia then
                            disabledPrefix <- true
                            printablePrefix <- printablePrefix && this.PrintableDisabled item

                            verbatimPrefix <-
                                verbatimPrefix
                                || source
                                    .AsSpan(item.Start, item.Length)
                                    .Contains("@\"".AsSpan(), StringComparison.Ordinal)
                        elif
                            item.Kind = TriviaKind.SingleLineCommentTrivia
                            && SyntaxFacts.ignoreMarker (
                                source.AsSpan(item.Start, item.Length).Trim()
                            )
                                >
                                0
                        then
                            markerIndex <- i
                            markerDepth <- depth

                if
                    single
                    && nestedAfterMarker
                    && firstKind = TriviaKind.IfDirectiveTrivia
                    && not disabledPrefix
                    && closedConditionals.Contains opening
                    && not (this.ConditionalPrefixAt(first, openingIndex, true))
                then
                    this.Trivia(first, true, d, markerIndex)

                let pending =
                    Array.init leading.LeadingCount (fun i -> not seen[leading.TriviaStart + i])

                let consumed = ResizeArray<struct (int * int)>()
                let mutable head = -1

                for i = leading.TriviaStart to leading.TriviaStart + leading.LeadingCount - 1 do
                    let item = tree.Trivia i

                    if not seen[i] then
                        if
                            head < 0
                            && item.Kind <> TriviaKind.WhitespaceTrivia
                            && item.Kind <> TriviaKind.EndOfLineTrivia
                        then
                            head <- item.Start

                        seen[i] <- true
                    else
                        consumed.Add(struct (item.Start, item.Start + item.Length))

                if head >= 0 then
                    if
                        d.Count = 0
                        || d.Storage[d.Count - 1].Kind <> ElementKind.Line
                        || d.Storage[d.Count - 1].A <> int LineKind.Hard
                        || d.Storage[d.Count - 1].Flags &&& ElementFlags.SkipBreakIfFirst <> 0uy
                    then
                        this.Hard d

                    let mutable finish = leading.Start

                    while finish > head
                          && Char.IsWhiteSpace source[finish - 1]
                          && not (this.LiteralLine(finish - 1)) do
                        finish <- finish - 1

                    let mutable cursor = head
                    let mutable consumedIndex = 0

                    let copyLeading first last =
                        let mutable cursor = first

                        while consumedIndex < consumed.Count
                              && (let struct (_, ending) = consumed[consumedIndex] in
                                  ending <= cursor) do
                            consumedIndex <- consumedIndex + 1

                        while consumedIndex < consumed.Count
                              && cursor < last
                              && (let struct (start, _) = consumed[consumedIndex] in start < last) do
                            let struct (start, ending) = consumed[consumedIndex]

                            if cursor < start then
                                this.Verbatim(cursor, min last start, d)

                            cursor <- max cursor (min last ending)

                            if ending <= last then
                                consumedIndex <- consumedIndex + 1

                        if cursor < last then
                            this.Verbatim(cursor, last, d)

                    if
                        head = opening
                        && ((not single
                             && depth = 0
                             && markerDepth = 1
                             && closedConditionals.Contains opening
                             && (this.ScannedComment(opening, 1)
                                 || bodyMarkedConditionals.Contains opening)
                             && (not recoveredWitness || bodyMarkedConditionals.Contains opening))
                            || (not single
                                && depth > 0
                                && not disabledPrefix
                                && ((not alternatePrefix
                                     && alternateConditionals.Contains opening
                                     && closedConditionals.Contains opening
                                     && ((recoveringConditionals
                                          && this.ConditionalPrefixAt(first, openingIndex, true))
                                         || ((commentConditionals.Contains opening
                                              || (kind = NodeKind.Block && closedPrefix))
                                             && this.ScannedComment(opening, 1))))
                                    || (alternatePrefix
                                        && not (closedConditionals.Contains opening)
                                        && recoveringConditionals
                                        && depth > 1)))
                            || (recoveringConditionals
                                && disabledPrefix
                                && depth = 0
                                && markerBranch = TriviaKind.ElseDirectiveTrivia
                                && closedConditionals.Contains opening)
                            || (single
                                && depth > 0
                                && alternatePrefix
                                && closedPrefix
                                && markerDepth > depth)
                            || (single
                                && kind = NodeKind.LocalDeclarationStatement
                                && markerDepth > 0
                                && markerBranch = TriviaKind.ElseDirectiveTrivia
                                && (not disabledPrefix || printablePrefix)
                                && closedConditionals.Contains opening)
                            || (not single
                                && disabledPrefix
                                && closedPrefix
                                && depth > 0
                                && ((printablePrefix
                                     && not alternatePrefix
                                     && not (closedConditionals.Contains opening))
                                    || (not printablePrefix
                                        && not verbatimPrefix
                                        && closedConditionals.Contains opening)))
                            || ((depth > 2 && markerDepth >= depth
                                 || (depth > 1 && markerDepth > depth))
                                && not (closedConditionals.Contains opening))
                            || ((recoveringConditionals
                                 || (range >= 0
                                     && markerDepth > 0
                                     && closedConditionals.Contains opening))
                                && disabledPrefix
                                && verbatimPrefix
                                && not printablePrefix
                                && closedPrefix
                                && depth > 0))
                    then
                        while cursor > 0 && (source[cursor - 1] = ' ' || source[cursor - 1] = '\t') do
                            cursor <- cursor - 1

                        d.AddTrim()

                    for i = leading.TriviaStart to leading.TriviaStart + leading.LeadingCount - 1 do
                        let item = tree.Trivia i

                        if
                            (item.Kind = TriviaKind.DisabledTextTrivia
                             || item.Kind = TriviaKind.MultiLineCommentTrivia
                             || item.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                            && item.Start >= head
                            && pending[i - leading.TriviaStart]
                        then
                            copyLeading cursor item.Start
                            let ending = min finish (item.Start + item.Length)

                            this.Verbatim(
                                item.Start,
                                ending,
                                d,
                                trimLines = true,
                                preserveTokens = (item.Kind = TriviaKind.DisabledTextTrivia),
                                trimEnd = true,
                                trailingLine =
                                    (ending < finish && item.Kind = TriviaKind.DisabledTextTrivia)
                            )

                            cursor <- ending

                    copyLeading cursor finish
                    this.Hard d

                    for i = leading.TriviaStart to leading.TriviaStart + leading.LeadingCount - 1 do
                        let item = tree.Trivia i

                        if
                            item.Start >= head
                            && item.Start < finish
                            && pending[i - leading.TriviaStart]
                        then
                            if item.Kind = TriviaKind.RegionDirectiveTrivia then
                                d.AddRegion(source, item.Start, 0, false)
                            elif
                                item.Kind = TriviaKind.EndRegionDirectiveTrivia
                                && not ignoredSingle
                                && (markerIndex < 0 || i > markerIndex)
                            then
                                d.AddRegion(source, item.Start, 0, true)

                let endToken = tree.Token(this.Last n)
                let mutable finish = endToken.End
                let mutable extendedSeparator = false

                if range >= 0 then
                    let parent = (tree.Node n).Parent

                    if parent >= 0 then
                        let struct (closing, boundary) =
                            match closingPositions.TryGetValue parent with
                            | true, positions -> positions
                            | _ ->
                                let siblings = this.Children parent
                                let mutable position = -1
                                let mutable boundary = -1
                                let mutable index = siblings.Length - 1

                                while position < 0 && index >= 0 do
                                    memberProbes <- memberProbes + 1L
                                    let child = siblings[index]

                                    if
                                        this.At(child, TokenKind.CloseBraceToken)
                                        || this.At(child, TokenKind.EndOfFileToken)
                                    then
                                        let token = tree.Token(this.First child)
                                        position <- token.Start

                                        boundary <-
                                            if token.LeadingCount > 0 then
                                                (tree.Trivia token.TriviaStart).Start
                                            else
                                                position

                                    index <- index - 1

                                let positions = struct (position, boundary)
                                closingPositions[parent] <- positions
                                positions

                        let spans =
                            match siblingSpans.TryGetValue parent with
                            | true, spans -> spans
                            | _ ->
                                let siblings = this.Children parent

                                let spans =
                                    Array.init siblings.Length (fun i ->
                                        let first = tree.Token(this.First siblings[i])
                                        let last = tree.Token(this.Last siblings[i])
                                        struct (first.Start, last.End))

                                siblingSpans[parent] <- spans
                                spans

                        let mutable lo = 0
                        let mutable hi = spans.Length

                        while lo < hi do
                            let mid = lo + (hi - lo) / 2
                            let struct (first, _) = spans[mid]
                            if first < range then lo <- mid + 1 else hi <- mid

                        let swallowed =
                            lo > 0 && (let struct (_, last) = spans[lo - 1] in range < last)

                        if closing >= 0 then
                            finish <- if swallowed then boundary else min range boundary
                        else
                            finish <- min range finish

                elif this.Kind (tree.Node n).Parent = NodeKind.EnumDeclaration then
                    let next = this.Last n + 1

                    if next < tree.TokenCount && (tree.Token next).Kind = TokenKind.CommaToken then
                        let separator = tree.Token next in
                        finish <- separator.End
                        extendedSeparator <- true

                        for i = separator.TriviaStart + separator.LeadingCount to separator
                                                                                      .TriviaStart
                                                                                  + separator
                                                                                      .LeadingCount
                                                                                  + separator
                                                                                      .TrailingCount
                                                                                  - 1 do
                            let item = tree.Trivia i

                            if item.Kind <> TriviaKind.EndOfLineTrivia then
                                finish <- item.Start + item.Length

                while finish > position && Char.IsWhiteSpace source[finish - 1] do
                    finish <- finish - 1

                let mutable start = position

                while start > 0 && (source[start - 1] = ' ' || source[start - 1] = '\t') do
                    start <- start - 1

                d.AddTrim()
                this.Verbatim(start, finish, d)

                ignoreUntil <- finish
                let mutable token = first

                let transition (i: int) =
                    let item = tree.Trivia i

                    if item.Start >= position && item.Start < finish then
                        if item.Kind = TriviaKind.RegionDirectiveTrivia then
                            d.AddRegion(source, item.Start, 0, false)
                        elif item.Kind = TriviaKind.EndRegionDirectiveTrivia then
                            d.AddRegion(source, item.Start, 0, true)

                while token < tree.TokenCount && (tree.Token token).Start < finish do
                    let t = tree.Token token

                    for i = t.TriviaStart to t.TriviaStart + t.LeadingCount + t.TrailingCount - 1 do
                        if (tree.Trivia i).Start < finish then
                            seen[i] <- true
                            transition i

                    token <- token + 1

                if token < tree.TokenCount then
                    let t = tree.Token token

                    for i = t.TriviaStart to t.TriviaStart + t.LeadingCount - 1 do
                        if (tree.Trivia i).Start < finish then
                            seen[i] <- true
                            transition i

                if ignoredSingle && not extendedSeparator then
                    this.Trivia(this.Last n, false, d)

                true

    member private this.ForeignNode(n: int, d: DocumentBuffer) =
        let first = tree.Token(this.First n)
        let last = tree.Token(this.Last n)

        if preserveForeignCode then
            this.LiteralLine first.Start |> ignore

        if
            not preserveForeignCode
            || first.Start >= literalLength
            || not literalInteriors[first.Start]
            || last.End <= first.Start
            || not literalInteriors[last.End - 1]
        then
            false
        else
            let buffer = tree.LexerBuffer
            let mutable lo = 0
            let mutable hi = buffer.TokenCount

            while lo < hi do
                let mid = lo + (hi - lo) / 2

                if (buffer.Token mid).Start <= first.Start then
                    lo <- mid + 1
                else
                    hi <- mid

            let mutable foreign = lo > 0 && (buffer.Token(lo - 1)).Start = first.Start
            let mutable cursor = first.Start

            while foreign && cursor < last.End do
                foreign <- literalInteriors[cursor]
                cursor <- cursor + 1

            if foreign then
                this.Trivia(this.First n, true, d)
                let mutable start = first.Start

                while start > 0 && (source[start - 1] = ' ' || source[start - 1] = '\t') do
                    start <- start - 1

                d.AddTrim()
                this.Verbatim(start, last.End, d)
                this.Trivia(this.Last n, false, d)

            foreign

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintIgnoredOrForeign(n: int, d: DocumentBuffer) : bool =
        if
            (hasIgnores && this.IgnoreNode(n, d))
            || (preserveForeignCode && this.ForeignNode(n, d))
        then
            true
        elif hasIgnores then
            let c = this.Children n
            let mutable first = 0

            while first < c.Length && this.Kind c[first] = NodeKind.AttributeList do
                first <- first + 1

            if
                first > 0
                && first < c.Length
                && ignoredSingles.Contains((tree.Token(this.First c[first])).Start)
            then
                for i = 0 to first - 1 do
                    this.Emit(c[i], d)
                    this.Hard d

                this.IgnoreNode(n, d, this.First c[first]) |> ignore
                true
            else
                false
        else
            false

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member private this.Print(n: int, d: DocumentBuffer) : unit = this.PrintCore(n, d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.ShouldSkipCompilationUnitLeading(first: int, c: IntSlice) : bool =
        (hasIgnores
         && (ignoredSingles.Contains(treeTokens[first].Start)
             || (this.IgnoreRange(treeTokens[first].Start) >= 0
                 && (let mutable found = false
                     let mutable i = 0

                     while not found && i < c.Length do
                         let child = c[i]

                         if this.Kind child = NodeKind.UsingDirective then
                             let position = treeTokens[this.First child].Start

                             if
                                 this.IgnoreRange position < 0
                                 && not (ignoredSingles.Contains position)
                             then
                                 found <- true

                         i <- i + 1

                     found))))
        || (c.Length > 0
            && this.Kind c[0] = NodeKind.UsingDirective
            && (not hasIgnores
                || (let position = treeTokens[this.First c[0]].Start in

                    this.IgnoreRange position < 0 && not (ignoredSingles.Contains position))))

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintVariableDeclarationCold(n: int, c: IntSlice, d: DocumentBuffer) =
        let generic = this.ContainsLessThan c[0]

        let mutable callInitializer = false

        if generic then
            let mutable i = 0

            while not callInitializer && i < c.Length do
                let child = c[i]

                if this.Kind child = NodeKind.VariableDeclarator then
                    let declChildren = this.Children child
                    let mutable j = 0

                    while not callInitializer && j < declChildren.Length do
                        let value = declChildren[j]

                        if this.Kind value = NodeKind.EqualsValueClause then
                            let values = this.Children value
                            let rhs = this.Kind values[values.Length - 1]

                            if
                                rhs = NodeKind.InvocationExpression
                                || rhs = NodeKind.SimpleMemberAccessExpression
                                || rhs = NodeKind.ConditionalAccessExpression
                                || rhs = NodeKind.ObjectCreationExpression
                                || rhs = NodeKind.ImplicitObjectCreationExpression
                                || rhs = NodeKind.ArrayCreationExpression
                                || rhs = NodeKind.ImplicitArrayCreationExpression
                                || rhs = NodeKind.StackAllocArrayCreationExpression
                                || rhs = NodeKind.ImplicitStackAllocArrayCreationExpression
                                || rhs = NodeKind.AwaitExpression
                            then
                                callInitializer <- true

                        j <- j + 1

                i <- i + 1

        let inline tail () =
            this.Space d
            this.Emit(c[1], d)

            if c.Length > 2 then
                if this.Kind(this.Parent n) = NodeKind.ForStatement then
                    this.Spaced(c.SliceFrom 2, d)
                else
                    d.AddTag Tag.StartIndent

                    for i = 2 to c.Length - 1 do
                        if this.At(c[i], TokenKind.CommaToken) then
                            this.Emit(c[i], d)
                            this.Hard d
                        else
                            this.Emit(c[i], d)

                    d.AddTag Tag.EndIndent

        if callInitializer then
            let id = d.NewGroupId()
            d.AddTag(Tag.StartConditionalGroup, id)
            d.AddTag Tag.StartAlternative
            d.AddTag Tag.StartForceFlat
            let typeStart = d.Count
            this.Emit(c[0], d)
            let typeLength = d.Count - typeStart
            d.AddTag Tag.EndForceFlat
            let tailStart = d.Count
            tail ()
            let tailLength = d.Count - tailStart
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.StartAlternative
            d.AddShared(typeStart, typeLength)
            d.AddShared(tailStart, tailLength)
            d.AddTag Tag.EndAlternative
            d.AddTag Tag.EndConditionalGroup
        else
            this.Emit(c[0], d)
            tail ()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintCreation(n: int, c: IntSlice, d: DocumentBuffer) =
        d.StartGroup() |> ignore

        for i = 0 to c.Length - 1 do
            if i > 0 then
                if SyntaxFacts.initializer (this.Kind c[i]) then
                    if
                        this.Kind c[i] = NodeKind.ObjectInitializerExpression
                        || this.Kind c[i] = NodeKind.CollectionInitializerExpression
                    then
                        let initChildren = this.Children c[i]
                        let owner = this.Parent n
                        let ownerKind = this.Kind owner

                        let propertyInitializer =
                            ownerKind = NodeKind.EqualsValueClause
                            && this.Kind(this.Parent owner) = NodeKind.PropertyDeclaration

                        if
                            (this.Kind c[i] = NodeKind.ObjectInitializerExpression
                             || (this.BraceRows initChildren
                                 && not propertyInitializer
                                 && ownerKind <> NodeKind.Argument
                                 && ownerKind <> NodeKind.EqualsValueClause
                                 && ownerKind <> NodeKind.SimpleAssignmentExpression))
                            && (initChildren.Length > 2
                                || this.HasTrivia(this.First initChildren[0], false)
                                || this.HasTrivia(
                                    this.First initChildren[initChildren.Length - 1],
                                    true
                                ))
                        then
                            this.Hard d
                        else
                            d.AddLine LineKind.Normal
                    else
                        d.AddLine LineKind.Normal
                elif
                    i = 1
                    && this.Kind c[i] <> NodeKind.ArgumentList
                    && not (this.At(c[i], TokenKind.OpenBracketToken))
                then
                    this.Space d

            this.Emit(c[i], d)

        d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintAttributedParameter
        (c: IntSlice, afterAttributes: int, d: DocumentBuffer)
        =
        d.StartGroup() |> ignore

        for i = 0 to afterAttributes - 1 do
            if i > 0 then
                d.AddLine LineKind.Normal

            this.Emit(c[i], d)

        if afterAttributes < c.Length then
            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal
            this.Spaced(c.SliceFrom afterAttributes, d)
            d.AddTag Tag.EndIndent

        d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintReturnStatementCold(c: IntSlice, d: DocumentBuffer) =
        if this.CollectionReceiver c[1] then
            d.StartGroup() |> ignore
            this.Emit(c[0], d)
            d.AddLine LineKind.Normal
            this.Emit(c[1], d)
            this.Emit(c[2], d)
            d.EndGroup()
        elif
            this.Kind c[1] = NodeKind.ConditionalExpression
            && (let conditional = this.Children c[1] in
                conditional.Length = 5 && SyntaxFacts.binary (this.Kind conditional[0]))
        then
            d.StartGroup() |> ignore
            this.Emit(c[0], d)
            let first = (tree.Token(this.First c[1])).Start
            let conditional = this.Children c[1]

            if
                this.Kind conditional[4] = NodeKind.ConditionalExpression
                && not (ignoredSingles.Contains first)
                && this.IgnoreRange first < 0
            then
                this.Space d
                d.AddTag Tag.StartIndent
                this.Emit(c[1], d)
                d.AddTag Tag.EndIndent
            elif
                not (this.InlineReturnCondition c[1])
                || ignoredSingles.Contains first
                || this.IgnoreRange first >= 0
            then
                d.AddTag Tag.StartIndent
                d.AddLine LineKind.Normal
                this.Emit(c[1], d)
                d.AddTag Tag.EndIndent
            else
                this.Emit(c[1], d)

            this.Emit(c[2], d)
            d.EndGroup()
        else
            d.StartGroup() |> ignore
            this.Spaced(c, d)
            d.EndGroup()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintColdStatementsAndQueries
        (n: int, kind: NodeKind, c: IntSlice, d: DocumentBuffer)
        : unit =
        match kind with
        | NodeKind.CatchClause ->
            let body = this.SliceFindKind(c, NodeKind.Block)
            let header = d.StartGroup()

            for i = 0 to body - 1 do
                if this.Kind c[i] = NodeKind.CatchFilterClause then
                    d.AddTag Tag.StartIndent
                    d.AddLine LineKind.Normal
                    this.Emit(c[i], d)
                    d.AddTag Tag.EndIndent
                else
                    if i > 0 then
                        this.Space d

                    this.Emit(c[i], d)

            d.EndGroup()
            let block = this.Children c[body]

            if
                this.SliceContainsKind(c, NodeKind.CatchFilterClause)
                && block.Length = 2
                && not (this.HasTrivia(this.First block[0], false))
                && not (this.HasTrivia(this.First block[1], true))
            then
                d.AddTag(Tag.StartIfBreak, header)
                this.Space d
                let start = d.Count
                this.Block(c[body], d, false)
                let length = d.Count - start
                d.AddTag Tag.Else
                d.AddTag Tag.StartAlwaysFits
                d.StartGroup() |> ignore
                d.AddLine LineKind.Normal
                d.AddShared(start, length)
                d.EndGroup()
                d.AddTag Tag.EndAlwaysFits
                d.AddTag Tag.EndIfBreak
            else
                this.Block(c[body], d, true)
        | NodeKind.CheckedStatement
        | NodeKind.UncheckedStatement
        | NodeKind.UnsafeStatement
        | NodeKind.TryStatement
        | NodeKind.FinallyClause ->
            for i = 0 to c.Length - 1 do
                if this.Kind c[i] = NodeKind.Block then
                    this.Block(c[i], d, true)
                else
                    if i > 0 then
                        if
                            this.Kind c[i] = NodeKind.CatchClause
                            || this.Kind c[i] = NodeKind.FinallyClause
                        then
                            this.Hard d
                        else
                            this.Space d

                    this.Emit(c[i], d)
        | NodeKind.CatchDeclaration -> this.Spaced(c, d)
        | NodeKind.CatchFilterClause ->
            this.Emit(c[0], d)
            this.Space d
            d.StartGroup() |> ignore
            this.Emit(c[1], d)
            d.AddTag Tag.StartIndent
            this.All(c.SliceRange(2, c.Length - 2), d)
            d.AddTag Tag.EndIndent
            d.AddLine LineKind.Soft
            this.Emit(c[c.Length - 1], d)
            d.EndGroup()
        | NodeKind.DoStatement ->
            this.Emit(c[0], d)

            if this.Kind c[1] = NodeKind.Block then
                this.Block(c[1], d, true)
                this.Space d
            else
                this.Space d
                this.Emit(c[1], d)
                this.Hard d

            this.Emit(c[2], d)
            this.Space d
            this.Delimited(c.SliceRange(3, c.Length - 2), d, false, false, false)
            this.Emit(c[c.Length - 1], d)
        | NodeKind.LabeledStatement ->
            this.All(c.SliceRange(0, 1), d)
            this.Hard d

            if c.Length > 2 then
                blankSibling <- this.First c[2]

            this.All(c.SliceFrom 2, d)
        | NodeKind.SwitchStatement -> this.Switch(n, d)
        | NodeKind.SwitchSection ->
            let mutable labelCount = 0

            while labelCount < c.Length
                  && (let k = this.Kind c[labelCount] in

                      k = NodeKind.CaseSwitchLabel
                      || k = NodeKind.CasePatternSwitchLabel
                      || k = NodeKind.DefaultSwitchLabel) do
                labelCount <- labelCount + 1

            let labels = c.SliceRange(0, labelCount - 1)

            for i = 0 to labels.Length - 1 do
                if i > 0 then
                    this.Hard d
                    blankSibling <- this.First labels[i]

                this.Emit(labels[i], d)

            let body = c.SliceFrom labels.Length

            if body.Length = 1 && this.Kind body[0] = NodeKind.Block then
                if labels.Length = 0 then this.Blank d else this.Hard d
                this.Emit(body[0], d)
            elif
                labels.Length = 0
                && body.Length > 1
                && (let mutable allBlocks = true
                    let mutable i = 0

                    while allBlocks && i < body.Length do
                        if this.Kind body[i] <> NodeKind.Block then
                            allBlocks <- false

                        i <- i + 1

                    allBlocks)
            then
                d.AddTag Tag.StartIndent

                for idx = 0 to body.Length - 1 do
                    let child = body[idx]
                    this.Blank d
                    suppressBlank <- this.First child
                    this.Emit(child, d)

                d.AddTag Tag.EndIndent
            else
                if labels.Length = 0 then
                    this.Blank d

                d.AddTag Tag.StartIndent
                this.Hard d

                this.Members(
                    body,
                    d,
                    false,
                    false,
                    preserveLeadingBlank =
                        (labels.Length > 0 && body.Length > 0 && this.Kind body[0] <> NodeKind.Block)
                )

                d.AddTag Tag.EndIndent
        | NodeKind.CaseSwitchLabel
        | NodeKind.CasePatternSwitchLabel
        | NodeKind.DefaultSwitchLabel ->
            d.StartGroup() |> ignore

            for i = 0 to c.Length - 1 do
                if this.Kind c[i] = NodeKind.WhenClause then
                    let isCombinator =
                        i > 0
                        && (this.Kind c[i - 1] = NodeKind.AndPattern
                            || this.Kind c[i - 1] = NodeKind.OrPattern)

                    if isCombinator then
                        d.StartGroup() |> ignore

                    d.AddTag Tag.StartIndent
                    d.AddLine LineKind.Normal
                    this.Emit(c[i], d)
                    d.AddTag Tag.EndIndent

                    if isCombinator then
                        d.EndGroup()
                else
                    if
                        i > 0
                        && (this.WordBoundary(c[i - 1], c[i])
                            || this.At(c[i - 1], TokenKind.CaseKeyword))
                    then
                        this.Space d

                    this.Emit(c[i], d)

            d.EndGroup()
        | NodeKind.WhenClause -> this.Spaced(c, d)
        | NodeKind.QueryExpression ->
            let parent = this.Kind(this.Parent n)
            let returned = parent = NodeKind.ReturnStatement

            let grouped = returned || parent = NodeKind.ExpressionStatement

            if grouped then
                d.StartGroup() |> ignore

            this.Emit(c[0], d)

            if returned then
                d.AddTag Tag.StartIndent

            d.AddLine LineKind.Normal
            this.All(c.SliceFrom 1, d)

            if returned then
                d.AddTag Tag.EndIndent

            if grouped then
                d.EndGroup()
        | NodeKind.QueryBody ->
            for i = 0 to c.Length - 1 do
                if i > 0 && this.Kind c[i] <> NodeKind.QueryContinuation then
                    d.AddLine LineKind.Normal

                this.Emit(c[i], d)
        | NodeKind.QueryContinuation ->
            this.Space d
            this.Spaced(c.SliceRange(0, 1), d)
            d.AddLine LineKind.Normal
            this.All(c.SliceFrom 2, d)
        | NodeKind.JoinClause ->
            d.StartGroup() |> ignore
            let on = this.SliceFindToken(c, TokenKind.OnKeyword)
            this.Spaced(c.SliceRange(0, on - 1), d)

            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal

            let into = this.SliceFindKind(c, NodeKind.JoinIntoClause)
            let finish = if into >= 0 then into else c.Length
            this.Spaced(c.SliceRange(on, finish - 1), d)

            if into >= 0 then
                d.AddLine LineKind.Normal
                this.Emit(c[into], d)

            d.AddTag Tag.EndIndent
            d.EndGroup()
        | NodeKind.FromClause
        | NodeKind.LetClause
        | NodeKind.JoinIntoClause
        | NodeKind.OrderByClause
        | NodeKind.AscendingOrdering
        | NodeKind.DescendingOrdering
        | NodeKind.SelectClause
        | NodeKind.GroupClause ->
            d.StartGroup() |> ignore
            this.Spaced(c, d)
            d.EndGroup()
        | NodeKind.WhereClause ->
            d.StartGroup() |> ignore
            this.Emit(c[0], d)
            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal
            this.Spaced(c.SliceFrom 1, d)
            d.AddTag Tag.EndIndent
            d.EndGroup()
        | NodeKind.EnumMemberDeclaration ->
            let mutable first = 0

            while first < c.Length && this.Kind c[first] = NodeKind.AttributeList do
                this.Emit(c[first], d)
                this.Hard d
                first <- first + 1

            d.StartGroup() |> ignore
            this.Spaced(c.SliceFrom first, d)
            d.EndGroup()
        | NodeKind.ExpressionStatement ->
            let first, last = this.First n, this.Last n
            let firstToken, lastToken = tree.Token first, tree.Token last
            let start, finish = firstToken.Start, lastToken.End
            this.Verbatim(start, finish, d)

            for t = first to last do
                let token = tree.Token t

                for i = token.TriviaStart to token.TriviaStart
                                             + token.LeadingCount
                                             + token.TrailingCount
                                             - 1 do
                    let item = tree.Trivia i

                    if item.Start < finish then
                        seen[i] <- true

                        if item.Start >= start then
                            if item.Kind = TriviaKind.RegionDirectiveTrivia then
                                d.AddRegion(source, item.Start, 0, false)
                            elif item.Kind = TriviaKind.EndRegionDirectiveTrivia then
                                d.AddRegion(source, item.Start, 0, true)

            this.Trivia(last, false, d)
        | _ ->
            if SyntaxFacts.binary kind then
                if cascadeKind = kind then
                    SyntaxFacts.learnFallthrough kind SyntaxFacts.FallsToBinary

                this.BinaryFallthrough(n, d)
            else
                if cascadeKind = kind then
                    SyntaxFacts.learnFallthrough kind SyntaxFacts.FallsToAll

                this.All(c, d)

    member private this.BinaryFallthrough(n: int, d: DocumentBuffer) : unit =
        let parent = this.Kind(this.Parent n)

        this.Binary(
            n,
            d,
            parent <> NodeKind.ParenthesizedExpression
            && parent <> NodeKind.CheckedExpression
            && parent <> NodeKind.UncheckedExpression
            && parent <> NodeKind.CatchFilterClause
            && parent <> NodeKind.DoStatement
        )

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintColdExpressions
        (n: int, kind: NodeKind, c: IntSlice, d: DocumentBuffer)
        : unit =
        match kind with
        | NodeKind.IsPatternExpression ->
            let parent = this.Kind(this.Parent n)
            let binaryPatternOperand = this.BinaryPatternOperand n

            if
                c.Length = 3
                && parent <> NodeKind.Argument
                && not binaryPatternOperand
                && (this.Kind c[2] = NodeKind.DeclarationPattern
                    || this.Kind c[2] = NodeKind.TypePattern
                    || (this.Kind c[2] = NodeKind.RecursivePattern
                        && let pattern = this.Children c[2] in

                           pattern.Length > 0
                           && pattern[0] >= 0
                           && this.Kind pattern[0] <> NodeKind.PropertyPatternClause
                           && this.Kind pattern[0] <> NodeKind.PositionalPatternClause))
            then
                d.StartGroup() |> ignore

                if
                    parent = NodeKind.IfStatement
                    && (this.Kind c[0] = NodeKind.InvocationExpression
                        || this.Kind c[0] = NodeKind.ElementAccessExpression)
                then
                    let wholeReceiver =
                        this.Kind c[0] = NodeKind.ElementAccessExpression
                        || (this.Kind c[0] = NodeKind.InvocationExpression
                            && let call = this.Children c[0] in
                               let arguments = this.Children call[call.Length - 1] in
                               arguments.Length <= 3)

                    if wholeReceiver then
                        d.AddTag Tag.StartForceFlat

                    this.Emit(c[0], d)

                    if wholeReceiver then
                        d.AddTag Tag.EndForceFlat

                    d.AddLine LineKind.Normal
                    this.Spaced(c.SliceFrom 1, d)
                elif SyntaxFacts.memberAccess (this.Kind c[0]) then
                    this.Emit(c[0], d)
                    d.AddTag Tag.StartIndent
                    d.AddLine LineKind.Normal
                    this.Spaced(c.SliceFrom 1, d)
                    d.AddTag Tag.EndIndent
                elif
                    not (
                        this.Kind c[2] = NodeKind.RecursivePattern
                        && this.SliceContainsKind(
                            this.Children c[2],
                            NodeKind.PropertyPatternClause
                        )
                    )
                then
                    this.Emit(c[0], d)

                    let indentTail =
                        parent <> NodeKind.IfStatement
                        && parent <> NodeKind.WhileStatement
                        && parent <> NodeKind.ParenthesizedExpression

                    if indentTail then
                        d.AddTag Tag.StartIndent

                    d.AddLine LineKind.Normal
                    this.Spaced(c.SliceFrom 1, d)

                    if indentTail then
                        d.AddTag Tag.EndIndent
                else
                    this.Spaced(c, d)

                d.EndGroup()
            else
                d.StartGroup() |> ignore

                let wholeBinaryReceiver =
                    binaryPatternOperand
                    && (this.Kind c[0] <> NodeKind.InvocationExpression
                        || (let call = this.Children c[0] in
                            let arguments = this.Children call[call.Length - 1] in
                            arguments.Length <= 3))

                if wholeBinaryReceiver then
                    d.AddTag Tag.StartForceFlat

                this.Emit(c[0], d)

                if wholeBinaryReceiver then
                    d.AddTag Tag.EndForceFlat

                let compound =
                    this.Kind c[2] = NodeKind.NotPattern
                    || this.Kind c[2] = NodeKind.AndPattern
                    || this.Kind c[2] = NodeKind.OrPattern

                let indentTail =
                    not compound
                    || not (
                        parent = NodeKind.IfStatement
                        || parent = NodeKind.ParenthesizedExpression
                        || parent = NodeKind.EqualsValueClause
                        || SyntaxFacts.assignment parent
                    )

                if indentTail then
                    d.AddTag Tag.StartIndent

                d.AddLine LineKind.Normal
                this.Emit(c[1], d)
                this.Space d
                this.Emit(c[2], d)

                if indentTail then
                    d.AddTag Tag.EndIndent

                d.EndGroup()
        | NodeKind.AndPattern
        | NodeKind.OrPattern -> this.Pattern(n, d)
        | NodeKind.FunctionPointerParameterList ->
            d.StartGroup() |> ignore
            this.Emit(c[0], d)

            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Soft

            for i = 1 to c.Length - 2 do
                this.Emit(c[i], d)

                if this.At(c[i], TokenKind.CommaToken) then
                    d.AddLine LineKind.Normal

            d.AddTag Tag.EndIndent

            this.Emit(c[c.Length - 1], d)
            d.EndGroup()
        | NodeKind.CheckedExpression
        | NodeKind.UncheckedExpression ->
            this.Emit(c[0], d)
            this.Delimited(c.SliceFrom 1, d, false, false, false)
        | NodeKind.AnonymousMethodExpression ->
            this.Spaced(c.SliceRange(0, c.Length - 2), d)
            this.Block(c[c.Length - 1], d, true)
        | NodeKind.AnonymousObjectCreationExpression ->
            let parentKind = this.Kind(this.Parent n)

            if
                (parentKind = NodeKind.Argument && this.InsideAnonymousMethodBody n)
                || parentKind = NodeKind.AnonymousObjectMemberDeclarator
            then
                let forced = this.MultilineToken n

                if c.Length > 3 then
                    suppressBlank <- this.First c[2]

                d.StartGroup() |> ignore
                this.Emit(c[0], d)
                d.AddLine LineKind.Normal
                this.Delimited(c.SliceFrom 1, d, true, true, forced, inheritMode = true)
                d.EndGroup()
            else
                this.Emit(c[0], d)
                if c.Length > 3 then this.Hard d else this.Space d
                this.Delimited(c.SliceFrom 1, d, true, true, c.Length > 3)
        | NodeKind.WithExpression ->
            this.Emit(c[0], d)
            this.Space d
            this.Emit(c[1], d)
            d.AddLine LineKind.Normal
            this.Emit(c[2], d)
        | NodeKind.SwitchExpression ->
            this.Emit(c[0], d)
            this.Space d
            this.Emit(c[1], d)
            this.Hard d

            if c.Length = 4 then
                this.Emit(c[2], d)
                this.Blank d
                this.Emit(c[3], d)
            else
                this.Delimited(c.SliceFrom 2, d, true, true, true)
        | NodeKind.SwitchExpressionArm ->
            let guardGroup =
                if
                    c.Length = 4
                    && this.Kind c[1] = NodeKind.WhenClause
                    && (let guard = this.Children c[1] in
                        guard.Length = 2 && SyntaxFacts.binary (this.Kind guard[1]))
                then
                    let id = d.StartGroup()
                    this.Emit(c[0], d)
                    d.AddTag Tag.StartIndent
                    d.AddLine LineKind.Normal
                    this.Emit(c[1], d)
                    this.Space d
                    this.Emit(c[2], d)
                    d.AddTag Tag.EndIndent
                    d.EndGroup()
                    id
                else
                    this.Spaced(c.SliceRange(0, c.Length - 2), d)
                    -1

            let rhs = c[c.Length - 1]
            let kind = this.Kind rhs
            let mutable rhsStart, rhsLength = -1, 0

            let inline value () =
                if rhsStart < 0 then
                    rhsStart <- d.Count
                    this.Emit(rhs, d)
                    rhsLength <- d.Count - rhsStart
                else
                    d.AddShared(rhsStart, rhsLength)

            let inline result () =
                d.StartGroup() |> ignore

                if kind = NodeKind.CollectionExpression then
                    d.AddLine LineKind.Normal
                    value ()
                elif
                    kind = NodeKind.InvocationExpression
                    || kind = NodeKind.ConditionalAccessExpression
                    || SyntaxFacts.memberAccess kind
                    || kind = NodeKind.ThrowExpression
                    || kind = NodeKind.ParenthesizedExpression
                    || kind = NodeKind.TupleExpression
                    || kind = NodeKind.ObjectCreationExpression
                    || kind = NodeKind.ImplicitObjectCreationExpression
                    || kind = NodeKind.CastExpression
                    || kind = NodeKind.ConditionalExpression
                    || SyntaxFacts.binary kind
                    || kind = NodeKind.ArrayCreationExpression
                    || kind = NodeKind.ImplicitArrayCreationExpression
                    || (kind >= NodeKind.UnaryPlusExpression && kind <= NodeKind.AddressOfExpression)
                    || kind = NodeKind.IndexExpression
                then
                    let id = d.NewGroupId()
                    d.AddTag(Tag.StartConditionalGroup, id)
                    d.AddTag Tag.StartAlternative
                    this.Space d
                    let start = d.Count
                    value ()
                    let length = d.Count - start
                    d.AddTag Tag.EndAlternative
                    d.AddTag Tag.StartAlternative
                    this.Space d
                    d.AddShared(start, length)
                    d.AddTag Tag.EndAlternative
                    d.AddTag Tag.StartAlternative
                    d.AddTag Tag.StartIndent
                    this.Hard d
                    d.AddShared(start, length)
                    d.AddTag Tag.EndIndent
                    d.AddTag Tag.EndAlternative
                    d.AddTag Tag.EndConditionalGroup
                else
                    d.AddTag Tag.StartIndent
                    d.AddLine LineKind.Normal
                    value ()
                    d.AddTag Tag.EndIndent

                d.EndGroup()

            if guardGroup >= 0 then
                d.AddTag(Tag.StartIfBreak, guardGroup)
                d.AddTag Tag.StartIndent
                this.Hard d
                value ()
                d.AddTag Tag.EndIndent
                d.AddTag Tag.Else
                result ()
                d.AddTag Tag.EndIfBreak
            else
                result ()
        | NodeKind.RecursivePattern ->
            let parent = this.Parent n

            let barePropertyClause =
                c.Length > 0 && this.Kind c[0] = NodeKind.PropertyPatternClause

            let ungrouped =
                not barePropertyClause
                && this.Kind parent = NodeKind.IsPatternExpression
                && this.BinaryPatternOperand parent

            if not ungrouped then
                d.StartGroup() |> ignore

            for i = 0 to c.Length - 1 do
                let clause = i > 0 && this.Kind c[i] = NodeKind.PropertyPatternClause
                let joined = clause && this.JoinsPropertyClause(n, c[i])

                if joined then
                    d.StartGroup() |> ignore

                if clause then
                    d.AddLine LineKind.Normal
                elif i > 0 && this.WordBoundary(c[i - 1], c[i]) then
                    this.Space d

                this.Emit(c[i], d)

                if joined then
                    d.EndGroup()

            if not ungrouped then
                d.EndGroup()
        | NodeKind.RelationalPattern
        | NodeKind.SpreadElement
        | NodeKind.SlicePattern
        | NodeKind.Subpattern ->
            this.Emit(c[0], d)

            if c.Length > 1 then
                this.Space d
                this.All(c.SliceFrom 1, d)
        | NodeKind.TypeParameterConstraintClause ->
            d.AddTag Tag.StartIndent
            this.Hard d

            if c.Length > 0 then
                this.Trivia(this.First c[0], true, d)

            let savedDirectives = headerDirectiveAlwaysFits
            headerDirectiveAlwaysFits <- true
            d.StartGroup() |> ignore

            try
                let colon = this.SliceFindToken(c, TokenKind.ColonToken)
                this.Spaced(c.SliceRange(0, colon - 1), d)
                this.Space d
                this.Emit(c[colon], d)
                this.Space d

                if colon + 1 < c.Length then
                    this.Emit(c[colon + 1], d)

                d.AddTag Tag.StartIndent

                for i = colon + 2 to c.Length - 1 do
                    this.Emit(c[i], d)

                    if this.At(c[i], TokenKind.CommaToken) then
                        d.AddLine LineKind.Normal

                d.AddTag Tag.EndIndent
            finally
                headerDirectiveAlwaysFits <- savedDirectives

            d.EndGroup()
            d.AddTag Tag.EndIndent
        | NodeKind.BaseConstructorInitializer
        | NodeKind.ThisConstructorInitializer ->
            d.AddTag Tag.StartIndent
            this.Hard d

            for i = 0 to c.Length - 1 do
                if i > 0 && this.At(c[i], TokenKind.ColonToken) then
                    this.Space d

                if
                    i > 0
                    && (this.WordBoundary(c[i - 1], c[i])
                        || this.At(c[i - 1], TokenKind.ColonToken)
                        || this.At(c[i - 1], TokenKind.CommaToken))
                then
                    this.Space d

                this.Emit(c[i], d)

            d.AddTag Tag.EndIndent
        | NodeKind.FunctionPointerType ->
            for i = 0 to c.Length - 1 do
                if
                    i > 0
                    && (this.Kind c[i] = NodeKind.FunctionPointerCallingConvention
                        || this.At(c[i - 1], TokenKind.AsteriskToken))
                then
                    this.Space d

                this.Emit(c[i], d)
        | NodeKind.FunctionPointerUnmanagedCallingConventionList -> this.Spaced(c, d)
        | NodeKind.InterpolationAlignmentClause ->
            this.Emit(c[0], d)
            this.Space d
            this.All(c.SliceFrom 1, d)
        | _ -> this.PrintColdStatementsAndQueries(n, kind, c, d)

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PrintCold(n: int, kind: NodeKind, c: IntSlice, d: DocumentBuffer) : unit =
        match kind with
        | NodeKind.CompilationUnit
        | NodeKind.NamespaceDeclaration
        | NodeKind.FileScopedNamespaceDeclaration -> this.Namespace(n, d)
        | NodeKind.ClassDeclaration
        | NodeKind.StructDeclaration
        | NodeKind.InterfaceDeclaration
        | NodeKind.EnumDeclaration
        | NodeKind.RecordDeclaration
        | NodeKind.RecordStructDeclaration
        | NodeKind.UnionDeclaration
        | NodeKind.ExtensionBlockDeclaration
        | NodeKind.DelegateDeclaration -> this.TypeDeclaration(n, d)
        | NodeKind.ConstructorDeclaration
        | NodeKind.DestructorDeclaration
        | NodeKind.OperatorDeclaration
        | NodeKind.ConversionOperatorDeclaration
        | NodeKind.LocalFunctionStatement -> this.Method(n, d)
        | NodeKind.ForStatement
        | NodeKind.ForEachStatement
        | NodeKind.ForEachVariableStatement
        | NodeKind.UsingStatement
        | NodeKind.LockStatement
        | NodeKind.FixedStatement -> this.Control(n, d)
        | NodeKind.EventFieldDeclaration ->
            d.StartGroup() |> ignore
            this.DeclarationHead(n, c, d)
            d.EndGroup()
        | NodeKind.ConditionalExpression -> this.Ternary(n, d)
        | NodeKind.PointerMemberAccessExpression
        | NodeKind.ConditionalAccessExpression -> this.Chain(n, d)
        | NodeKind.TupleExpression -> this.Arguments(n, d)
        | NodeKind.SimpleLambdaExpression
        | NodeKind.ParenthesizedLambdaExpression -> this.Lambda(n, d)
        | NodeKind.ImplicitObjectCreationExpression
        | NodeKind.ArrayCreationExpression
        | NodeKind.ImplicitArrayCreationExpression
        | NodeKind.StackAllocArrayCreationExpression
        | NodeKind.ImplicitStackAllocArrayCreationExpression -> this.PrintCreation(n, c, d)
        | NodeKind.ElseClause ->
            this.Emit(c[0], d)

            if this.Kind c[1] = NodeKind.Block then
                this.Block(c[1], d, true)
            elif this.Kind c[1] = NodeKind.IfStatement then
                this.Space d
                this.Emit(c[1], d)
            else
                d.AddTag Tag.StartIndent
                this.Hard d
                this.Emit(c[1], d)
                d.AddTag Tag.EndIndent
        | NodeKind.GlobalStatement -> this.All(c, d)
        | NodeKind.AddAssignmentExpression
        | NodeKind.SubtractAssignmentExpression
        | NodeKind.MultiplyAssignmentExpression
        | NodeKind.DivideAssignmentExpression
        | NodeKind.ModuloAssignmentExpression
        | NodeKind.AndAssignmentExpression
        | NodeKind.OrAssignmentExpression
        | NodeKind.ExclusiveOrAssignmentExpression
        | NodeKind.LeftShiftAssignmentExpression
        | NodeKind.RightShiftAssignmentExpression
        | NodeKind.CoalesceAssignmentExpression
        | NodeKind.UnsignedRightShiftAssignmentExpression -> this.Assignment(c, d, false)
        | NodeKind.ElementAccessExpression ->
            d.StartGroup() |> ignore
            this.All(c, d)
            d.EndGroup()
        | NodeKind.BracketedArgumentList
        | NodeKind.BracketedParameterList
        | NodeKind.TupleType
        | NodeKind.PositionalPatternClause
        | NodeKind.ParenthesizedVariableDesignation
        | NodeKind.ParenthesizedPattern -> this.Delimited(c, d, false, false, false)
        | NodeKind.TypeParameterList ->
            let savedDirectives = headerDirectiveAlwaysFits
            headerDirectiveAlwaysFits <- false

            try
                if c.Length = 3 && not (this.HasChildOfKind(c[1], NodeKind.AttributeList)) then
                    this.All(c, d)
                else
                    this.Delimited(c, d, false, false, false)
            finally
                headerDirectiveAlwaysFits <- savedDirectives
        | NodeKind.AttributeArgumentList ->
            this.Delimited(c, d, false, false, this.MultilineToken n)
        | NodeKind.TypeArgumentList ->
            let mutable allOmitted = true
            let mutable i = 0

            while allOmitted && i < c.Length do
                if c[i] >= 0 && this.Kind c[i] <> NodeKind.OmittedTypeArgument then
                    allOmitted <- false

                i <- i + 1

            if allOmitted then
                this.All(c, d)
            else
                this.TypeArguments(n, d)
        | NodeKind.ArrayRankSpecifier ->
            let mutable hasSize = false
            let mutable i = 0

            while not hasSize && i < c.Length do
                if c[i] >= 0 && this.Kind c[i] <> NodeKind.OmittedArraySizeExpression then
                    hasSize <- true

                i <- i + 1

            if hasSize then
                this.Delimited(c, d, false, false, false)
            else
                this.All(c, d)
        | NodeKind.UnaryPlusExpression
        | NodeKind.UnaryMinusExpression
        | NodeKind.AddressOfExpression ->
            this.Emit(c[0], d)

            if c.Length > 1 then
                let firstTok = &treeTokens[this.First c[1]]
                let op = &treeTokens[this.First c[0]]

                if
                    firstTok.Length > 0
                    && op.Length > 0
                    && source[firstTok.Start] = source[op.Start]
                then
                    this.Space d

                this.Emit(c[1], d)
        | NodeKind.ParenthesizedExpression ->
            let parent = this.Parent n

            if
                this.Kind parent = NodeKind.ConditionalExpression
                && (let conditional = this.Children parent in conditional[0] = n)
            then
                let operand = c[1]
                let operands = this.Children operand

                if
                    SyntaxFacts.binary (this.Kind operand)
                    && operands.Length = 3
                    && (this.Kind operands[0] = this.Kind operand
                        || this.Kind operand = NodeKind.LogicalAndExpression
                        || this.Kind operand = NodeKind.LogicalOrExpression)
                then
                    this.Delimited(c, d, false, false, false)
                else
                    this.All(c, d)
            else
                this.Delimited(c, d, false, false, false)
        | NodeKind.ObjectInitializerExpression
        | NodeKind.CollectionInitializerExpression
        | NodeKind.ArrayInitializerExpression
        | NodeKind.ComplexElementInitializerExpression
        | NodeKind.WithInitializerExpression
        | NodeKind.CollectionExpression
        | NodeKind.PropertyPatternClause
        | NodeKind.ListPattern -> this.Initializer(n, d)
        | NodeKind.RefValueExpression
        | NodeKind.RefExpression
        | NodeKind.ThrowExpression
        | NodeKind.NotPattern
        | NodeKind.VarPattern
        | NodeKind.DeclarationPattern
        | NodeKind.DeclarationExpression
        | NodeKind.RefType
        | NodeKind.ScopedType
        | NodeKind.TupleElement
        | NodeKind.AttributeArgument
        | NodeKind.AnonymousObjectMemberDeclarator
        | NodeKind.FunctionPointerParameter
        | NodeKind.ExternAliasDirective
        | NodeKind.UsingDirective
        | NodeKind.RefStructConstraint
        | NodeKind.AllowsConstraintClause
        | NodeKind.NameColon
        | NodeKind.ExpressionColon
        | NodeKind.NameEquals -> this.Spaced(c, d)
        | NodeKind.TypeParameter ->
            if c.Length > 0 && this.Kind c[0] <> NodeKind.AttributeList then
                this.Spaced(c, d)
            else
                let mutable firstAttr = 0

                while firstAttr < c.Length && this.Kind c[firstAttr] = NodeKind.AttributeList do
                    firstAttr <- firstAttr + 1

                if firstAttr = 0 then
                    this.Spaced(c, d)
                else
                    this.PrintAttributedParameter(c, firstAttr, d)
        | NodeKind.ThrowStatement
        | NodeKind.YieldReturnStatement
        | NodeKind.YieldBreakStatement
        | NodeKind.GotoStatement
        | NodeKind.GotoCaseStatement
        | NodeKind.GotoDefaultStatement
        | NodeKind.BreakStatement
        | NodeKind.ContinueStatement ->
            d.StartGroup() |> ignore
            this.Spaced(c, d)
            d.EndGroup()
        | NodeKind.InterpolatedStringExpression -> this.Interpolated(n, d)
        | NodeKind.StringLiteralExpression
        | NodeKind.Utf8StringLiteralExpression ->
            if
                c.Length = 1
                && (this.TokenKind c[0] = TokenKind.MultiLineRawStringLiteralToken
                    || this.TokenKind c[0] = TokenKind.Utf8MultiLineRawStringLiteralToken)
            then
                let parentKind = this.Kind(this.Parent n)

                if parentKind = NodeKind.ExpressionStatement then
                    d.AddTag Tag.StartIndent
                    this.Raw(-c[0] - 1, d)
                    d.AddTag Tag.EndIndent
                else
                    this.Raw(-c[0] - 1, d, attribute = (parentKind = NodeKind.AttributeArgument))
            else
                this.All(c, d)
        | NodeKind.IndexerDeclaration
        | NodeKind.EventDeclaration -> this.Property(n, d)
        | NodeKind.InitAccessorDeclaration
        | NodeKind.AddAccessorDeclaration
        | NodeKind.RemoveAccessorDeclaration -> this.Accessor(n, d)
        | NodeKind.CastExpression ->
            d.StartGroup() |> ignore
            this.All(c.SliceRange(0, c.Length - 2), d)
            let typ = c[1]
            let operand = c[c.Length - 1]
            let head = this.WithoutNullForgiving operand
            let operandKind = this.Kind head

            let compact =
                operandKind = NodeKind.IdentifierName
                || operandKind = NodeKind.ParenthesizedExpression

            let generic = this.ContainsLessThan typ

            if
                (this.Kind typ = NodeKind.TupleType || generic)
                && this.Kind operand = NodeKind.SuppressNullableWarningExpression
            then
                d.AddTag Tag.StartIndent
                d.AddLine LineKind.Soft
                this.Emit(operand, d)
                d.AddTag Tag.EndIndent
            elif compact then
                this.Emit(operand, d)
            else if
                (generic && this.Kind typ <> NodeKind.FunctionPointerType)
                || operandKind = NodeKind.CastExpression
            then
                d.AddTag Tag.StartIndent
                d.AddLine LineKind.Soft
                this.Emit(operand, d)
                d.AddTag Tag.EndIndent
            else
                let simpleHead =
                    operandKind = NodeKind.InvocationExpression
                    && let children = this.Children head in
                       this.Kind children[0] = NodeKind.IdentifierName

                let id = d.NewGroupId()
                d.AddTag(Tag.StartConditionalGroup, id)
                d.AddTag Tag.StartAlternative
                let start = d.Count
                this.Emit(operand, d)
                let length = d.Count - start
                d.AddTag Tag.EndAlternative
                d.AddTag Tag.StartAlternative

                if not simpleHead then
                    d.AddTag Tag.StartIndent
                    d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                    d.AddShared(start, length)
                    d.AddTag Tag.EndIndent
                else
                    d.AddShared(start, length)

                d.AddTag Tag.EndAlternative
                d.AddTag Tag.EndConditionalGroup

            d.EndGroup()
        | NodeKind.AttributeList ->
            let id = d.StartGroup()

            let targeted = c.Length > 2 && this.Kind c[1] = NodeKind.AttributeTargetSpecifier

            let first = if targeted then 2 else 1
            let multiple = c.Length - first > 2

            this.Emit(c[0], d)

            if targeted then
                this.All(this.Children c[1], d)

            if multiple then
                d.AddTag Tag.StartIndent
                d.AddLine(if targeted then LineKind.Normal else LineKind.Soft)
            elif targeted then
                this.Space d

            for i = first to c.Length - 2 do
                if i > first && this.At(c[i - 1], TokenKind.CommaToken) then
                    d.AddLine LineKind.Normal

                if
                    i = c.Length - 2
                    && i > first
                    && this.At(c[i], TokenKind.CommaToken)
                    && (ignoreUntil < 0 || treeTokens[-c[i] - 1].Start >= ignoreUntil)
                then
                    this.TrailingComma(-c[i] - 1, this.Last c[i - 1], id, d)
                else
                    this.Emit(c[i], d)

            if multiple then
                d.AddTag Tag.EndIndent
                d.AddLine LineKind.Soft

            this.Emit(c[c.Length - 1], d)
            d.EndGroup()
        | NodeKind.AttributeTargetSpecifier ->
            this.All(c, d)
            this.Space d
        | NodeKind.BaseList ->
            let parent = this.Parent n
            let parentKind = this.Kind parent

            let primaryParameters =
                (parentKind = NodeKind.ClassDeclaration
                 || parentKind = NodeKind.StructDeclaration
                 || parentKind = NodeKind.RecordDeclaration
                 || parentKind = NodeKind.RecordStructDeclaration)
                && (this.HasChildOfKind(parent, NodeKind.ParameterList)
                    || this.HasChildOfKind(parent, NodeKind.TypeParameterList))

            let splitBaseGroup = c.Length > 2 && this.HasLeadingDirective(this.First c[1])

            if primaryParameters then
                d.StartGroup() |> ignore

            d.AddTag Tag.StartIndent
            d.AddLine LineKind.Normal
            this.Emit(c[0], d)
            this.Space d

            if splitBaseGroup then
                this.Trivia(this.First c[1], true, d)
                d.StartGroup() |> ignore

            if c.Length > 1 then
                this.Emit(c[1], d)

            d.AddTag Tag.StartIndent

            for i = 2 to c.Length - 1 do
                this.Emit(c[i], d)

                if this.At(c[i], TokenKind.CommaToken) then
                    d.AddLine LineKind.Normal

            d.AddTag Tag.EndIndent

            if splitBaseGroup then
                d.EndGroup()

            d.AddTag Tag.EndIndent

            if primaryParameters then
                d.EndGroup()
        | _ -> this.PrintColdExpressions(n, kind, c, d)

    member private this.PrintCore(n: int, d: DocumentBuffer) : unit =
        this.EnsureStack()

        if stats then
            statNodes <- statNodes + 1

        if (hasIgnores || preserveForeignCode) && this.PrintIgnoredOrForeign(n, d) then
            ()
        else
            let node = &treeNodes[n]
            let kind = node.Kind
            let first = node.TokenStart
            let c = IntSlice(treeChildren, node.ChildStart, node.ChildCount)

            if
                first <> lastDeclinedLeadingToken
                && kind <> NodeKind.ArrowExpressionClause
                && kind <> NodeKind.BaseList
                && kind <> NodeKind.TypeParameterConstraintClause
                && not (SyntaxFacts.binary kind && this.Kind node.Parent = NodeKind.ReturnStatement)
                && not (
                    kind = NodeKind.CompilationUnit
                    && this.ShouldSkipCompilationUnitLeading(first, c)
                )
            then
                if not (this.DeclinedLeading first) then
                    this.Trivia(first, true, d)

                lastDeclinedLeadingToken <- first

            match SyntaxFacts.fallthroughOf kind with
            | SyntaxFacts.FallsToAll -> this.All(c, d)
            | SyntaxFacts.FallsToBinary -> this.BinaryFallthrough(n, d)
            | _ ->
                match kind with
                | NodeKind.MethodDeclaration -> this.Method(n, d)
                | NodeKind.Block -> this.Block(n, d, false)
                | NodeKind.IfStatement
                | NodeKind.WhileStatement -> this.Control(n, d)
                | NodeKind.ExpressionStatement ->
                    if
                        c.Length > 2
                        && (let firstTok = &treeTokens[this.First n] in

                            firstTok.Kind = TokenKind.AsteriskToken
                            && firstTok.Start + 1 < source.Length
                            && source[firstTok.Start + 1] = '/')
                    then
                        this.PrintCold(n, kind, c, d)
                    else
                        this.All(c, d)
                | NodeKind.FieldDeclaration
                | NodeKind.LocalDeclarationStatement ->
                    d.StartGroup() |> ignore
                    this.DeclarationHead(n, c, d)
                    d.EndGroup()
                | NodeKind.VariableDeclaration ->
                    if c.Length <= 2 && not (this.ContainsLessThan c[0]) then
                        this.Emit(c[0], d)
                        this.Space d
                        this.Emit(c[1], d)
                    else
                        this.PrintVariableDeclarationCold(n, c, d)
                | NodeKind.VariableDeclarator ->
                    for i = 0 to c.Length - 1 do
                        if this.Kind c[i] = NodeKind.EqualsValueClause then
                            this.Space d

                        this.Emit(c[i], d)
                | NodeKind.EqualsValueClause -> this.Assignment(c, d, true)
                | NodeKind.SimpleAssignmentExpression ->
                    if c.Length = 3 && this.Kind c[2] = NodeKind.SimpleAssignmentExpression then
                        this.ChainedAssignment(c, d)
                    else
                        this.Assignment(c, d, false)
                | NodeKind.InvocationExpression
                | NodeKind.SimpleMemberAccessExpression -> this.Chain(n, d)
                | NodeKind.ArgumentList -> this.Arguments(n, d)
                | NodeKind.ParameterList ->
                    let savedDirectives = headerDirectiveAlwaysFits
                    headerDirectiveAlwaysFits <- false

                    try
                        this.Delimited(c, d, false, false, false)
                    finally
                        headerDirectiveAlwaysFits <- savedDirectives
                | NodeKind.ObjectCreationExpression -> this.PrintCreation(n, c, d)
                | NodeKind.Argument ->
                    if c.Length = 1 then
                        this.Emit(c[0], d)
                    else
                        this.Spaced(c, d)
                | NodeKind.AwaitExpression -> this.Spaced(c, d)
                | NodeKind.Parameter ->
                    if c.Length > 0 && this.Kind c[0] <> NodeKind.AttributeList then
                        this.Spaced(c, d)
                    else
                        let mutable firstAttr = 0

                        while firstAttr < c.Length
                              && this.Kind c[firstAttr] = NodeKind.AttributeList do
                            firstAttr <- firstAttr + 1

                        if firstAttr = 0 then
                            this.Spaced(c, d)
                        else
                            this.PrintAttributedParameter(c, firstAttr, d)
                | NodeKind.ArrowExpressionClause ->
                    let trivia = this.HasTrivia(this.First n, true)
                    d.StartGroup(if trivia then ElementFlags.Break else 0uy) |> ignore

                    d.AddTag Tag.StartIndent
                    this.Trivia(this.First n, true, d)

                    if not trivia then
                        this.Space d

                    this.Emit(c[0], d)
                    d.AddLine LineKind.Normal

                    if SyntaxFacts.binary (this.Kind c[1]) then
                        this.Binary(c[1], d, false)
                    else
                        this.Emit(c[1], d)

                    d.AddTag Tag.EndIndent
                    d.EndGroup()
                | NodeKind.ReturnStatement ->
                    if
                        c.Length = 3
                        && (this.Kind c[1] = NodeKind.ConditionalExpression
                            || this.CollectionReceiver c[1])
                    then
                        this.PrintReturnStatementCold(c, d)
                    else
                        d.StartGroup() |> ignore
                        this.Spaced(c, d)
                        d.EndGroup()
                | NodeKind.StringLiteralExpression ->
                    if
                        c.Length = 1
                        && this.TokenKind c[0] <> TokenKind.MultiLineRawStringLiteralToken
                    then
                        this.All(c, d)
                    else
                        this.PrintCold(n, kind, c, d)
                | NodeKind.PropertyDeclaration -> this.Property(n, d)
                | NodeKind.AccessorList -> this.Accessors(n, d)
                | NodeKind.GetAccessorDeclaration
                | NodeKind.SetAccessorDeclaration -> this.Accessor(n, d)
                | _ ->
                    cascadeKind <- kind
                    this.PrintCold(n, kind, c, d)

            this.EnsureStack()

    member private this.SimpleAccessors(ac: IntSlice) =
        let mutable ok = true
        let mutable i = 0

        while ok && i < ac.Length do
            let x = ac[i]

            if x >= 0 then
                let children = this.Children x
                let mutable j = 0

                while ok && j < children.Length do
                    let k = this.Kind children[j]

                    if k = NodeKind.ArrowExpressionClause || k = NodeKind.Block then
                        ok <- false

                    j <- j + 1

            i <- i + 1

        ok

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.PropertyAccessorList(n: int, c: IntSlice, i: int, d: DocumentBuffer) =
        let ac = this.Children c[i]
        let simple = this.SimpleAccessors ac

        if simple then
            let mutable first = 0

            while first < i && this.Kind c[first] = NodeKind.AttributeList do
                this.Emit(c[first], d)
                this.Hard d
                first <- first + 1

            let first = first
            let opening = tree.Token(this.First n)
            let closing = tree.Token(this.Last c[i])

            let mutable bare = true
            let mutable ai = 0

            while bare && ai < ac.Length do
                let accessor = ac[ai]

                if accessor >= 0 && this.ChildCount accessor <> 2 then
                    bare <- false

                ai <- ai + 1

            let compact = bare && not (this.HeadHasTrivia(opening.Start, closing.End))

            d.StartGroup() |> ignore
            this.DeclarationHead(n, c.SliceRange(first, i - 1), d)

            if compact then
                this.Space d
                d.AddTag Tag.StartForceFlat
                this.Emit(c[i], d)
                d.AddTag Tag.EndForceFlat
            else
                d.AddLine LineKind.Normal
                this.Emit(c[i], d)

            d.EndGroup()
        else
            d.StartGroup() |> ignore
            this.DeclarationHead(n, c.SliceRange(0, i - 1), d)
            d.EndGroup()
            this.Hard d
            this.Emit(c[i], d)

    member private this.Property(n: int, d: DocumentBuffer) =
        let c = this.Children n

        let mutable i = -1
        let mutable k = 0

        while i < 0 && k < c.Length do
            let ck = this.Kind c[k]

            if ck = NodeKind.AccessorList || ck = NodeKind.ArrowExpressionClause then
                i <- k

            k <- k + 1

        if i < 0 then
            this.DeclarationHead(n, c, d)
        else
            if this.Kind c[i] = NodeKind.ArrowExpressionClause then
                d.StartGroup() |> ignore
                this.DeclarationHead(n, c.SliceRange(0, i - 1), d)
                d.EndGroup()
                this.Emit(c[i], d)
            else
                this.PropertyAccessorList(n, c, i, d)

            for j = i + 1 to c.Length - 1 do
                if this.Kind c[j] = NodeKind.EqualsValueClause then
                    this.Space d

                this.Emit(c[j], d)

    member private this.Accessor(n: int, d: DocumentBuffer) =
        let c = this.Children n

        let mutable bodyIdx = -1
        let mutable k = 0

        while bodyIdx < 0 && k < c.Length do
            let ck = this.Kind c[k]

            if ck = NodeKind.Block || ck = NodeKind.ArrowExpressionClause then
                bodyIdx <- k

            k <- k + 1

        let mutable first = 0

        while first < c.Length && this.Kind c[first] = NodeKind.AttributeList do
            this.Emit(c[first], d)

            if bodyIdx < 0 then
                d.AddLine LineKind.Normal
            else
                this.Hard d

            first <- first + 1

        first <- this.Modifiers(n, c, first, d)

        if bodyIdx < 0 then
            for i = first to c.Length - 1 do
                if i > first && this.WordBoundary(c[i - 1], c[i]) then
                    this.Space d

                this.Emit(c[i], d)
        else
            let i = bodyIdx
            this.Spaced(c.SliceRange(first, i - 1), d)

            if this.Kind c[i] = NodeKind.ArrowExpressionClause then
                this.Emit(c[i], d)
            else
                let bc = this.Children c[i]

                let forced = bc.Length > 3 || this.Kind n = NodeKind.InitAccessorDeclaration
                d.StartGroup(if forced then ElementFlags.Break else 0uy) |> ignore

                d.AddLine LineKind.Normal
                this.Emit(bc[0], d)

                d.AddTag Tag.StartIndent

                if bc.Length > 2 then
                    d.AddLine LineKind.Normal
                    this.Members(bc.SliceRange(1, bc.Length - 2), d, false, false, true)

                let closing = bc[bc.Length - 1]

                if
                    bc.Length > 1
                    && this.At(closing, TokenKind.CloseBraceToken)
                    && this.HasTrivia(this.First closing, true)
                then
                    if bc.Length = 2 then
                        this.Hard d

                    this.ClosingTrivia(this.First closing, d)

                d.AddTag Tag.EndIndent

                d.AddLine LineKind.Normal
                this.Emit(bc[bc.Length - 1], d)

                d.EndGroup()

            this.All(c.SliceFrom(i + 1), d)

    member private this.Accessors(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let simple = this.SimpleAccessors c

        if simple then
            this.Emit(c[0], d)

            d.AddTag Tag.StartIndent

            for i = 1 to c.Length - 2 do
                d.AddLine LineKind.Normal
                this.Emit(c[i], d)

            let closing = c[c.Length - 1]

            if
                c.Length > 1
                && this.At(closing, TokenKind.CloseBraceToken)
                && this.HasTrivia(this.First closing, true)
            then
                if c.Length = 2 then
                    this.Hard d

                this.ClosingTrivia(this.First closing, d)

            d.AddTag Tag.EndIndent

            d.AddLine LineKind.Normal
            this.Emit(c[c.Length - 1], d)
        else
            this.Emit(c[0], d)

            d.AddTag Tag.StartIndent
            this.Hard d
            this.Members(c.SliceRange(1, c.Length - 2), d, false, false)

            let closing = c[c.Length - 1]

            if
                c.Length > 1
                && this.At(closing, TokenKind.CloseBraceToken)
                && this.HasTrivia(this.First closing, true)
            then
                this.ClosingTrivia(this.First closing, d)

            d.AddTag Tag.EndIndent

            this.Hard d
            this.Emit(c[c.Length - 1], d)

    member private this.Switch(n: int, d: DocumentBuffer) =
        let c = this.Children n
        let first = this.SliceFindToken(c, TokenKind.OpenBraceToken)

        d.StartGroup() |> ignore
        this.Emit(c[0], d)
        this.Space d
        this.Delimited(c.SliceRange(1, first - 1), d, false, false, false)
        d.EndGroup()

        if
            c.Length = first + 2
            && not (this.HasTrivia(this.First c[first], false))
            && not (this.HasTrivia(this.First c[c.Length - 1], true))
        then
            this.Space d
            this.Delimited(c.SliceFrom first, d, true, false, false)
        else
            this.Hard d
            this.Emit(c[first], d)

            d.AddTag Tag.StartIndent
            this.Hard d

            if first + 1 < c.Length then
                suppressBlank <- this.First c[first + 1]

            this.Members(c.SliceRange(first + 1, c.Length - 2), d, false, false)
            this.ClosingTrivia(this.First c[c.Length - 1], d)
            d.AddTag Tag.EndIndent

            this.Hard d
            this.Emit(c[c.Length - 1], d)

    member this.PrintNode(n: int, d: DocumentBuffer) =
        stackFloor <- StackGuard.entry ()
        treeNodes <- tree.NodeStorage
        treeChildren <- tree.ChildStorage
        treeTokens <- tree.TokenStorage
        treeTrivia <- tree.TriviaStorage

        if seen.Length < tree.TriviaCount then
            growCleared &seen tree.TriviaCount (max 16 tree.TriviaCount)

        if initializedCreations.Length < tree.NodeCount then
            growCleared &initializedCreations tree.NodeCount (max 16 tree.NodeCount)

        this.IndexConditionals()
        this.Print(n, d)

    member internal _.SourceIsAscii = sourceIsAscii

    member internal _.SetOutputLimit(maxOutput: int, maxLine: int, indentStep: int) =
        maxOutputLength <- maxOutput
        maxLineLength <- max 1 maxLine
        unitIndent <- max 1 indentStep

    member this.Build(d: DocumentBuffer) : unit =
        stackFloor <- StackGuard.entry ()
        treeNodes <- tree.NodeStorage
        treeChildren <- tree.ChildStorage
        treeTokens <- tree.TokenStorage
        treeTrivia <- tree.TriviaStorage
        d.SourceForAscii <- source
        d.SourceIsAscii <- sourceIsAscii
        d.EnsureCapacity(tree.TokenCount * 2 + tree.NodeCount + (tree.NodeCount >>> 1) + 64)

        if seen.Length < tree.TriviaCount then
            growCleared &seen tree.TriviaCount (max 16 tree.TriviaCount)

        if initializedCreations.Length < tree.NodeCount then
            growCleared &initializedCreations tree.NodeCount (max 16 tree.NodeCount)

        DocumentStats.event DocumentStats.nWalks

        if tree.RootIndex >= 0 then
            this.IndexConditionals()
            this.Print(tree.RootIndex, d)

        if stats then
            DocumentStats.bump DocumentStats.nElements d.Count
            DocumentStats.bump DocumentStats.nNodes statNodes
            DocumentStats.bump DocumentStats.nTriviaRuns statTriviaRuns
            DocumentStats.bump DocumentStats.nTriviaEntered statTriviaEntered
            DocumentStats.bump DocumentStats.nTextElements (d.TakeTextElements())
            statNodes <- 0
            statTriviaRuns <- 0
            statTriviaEntered <- 0

        let mutable i = 0
        let mutable found = false

        while i < d.Count && not found do
            let e = d.Storage[i]

            if e.Kind = ElementKind.Line then d.Remove i
            elif e.Kind = ElementKind.Tag then i <- i + 1
            else found <- true

    interface IDisposable with
        member _.Dispose() =
            releasePooled &seen
            releasePooled &emptyConditionalPrefixes
            releasePooled &tokenScopes
            releasePooled &literalOwned
            releasePooled &literalLines
            releasePooled &literalInteriors
            releasePooled &literalBoundaries
            releasePooled &remapOwned
            releasePooled &remapInteriors
            releasePooled &remapBoundaries
            releasePooled &initializedCreations

            match triviaTokens with
            | ValueSome buf -> buf.ReleasePooledBuffers()
            | ValueNone -> ()

            match disabledTree with
            | ValueSome dt ->
                dt.ReleasePooledBuffers()
                disabledTree <- ValueNone
            | ValueNone -> ()

[<Sealed>]
type SyntaxDocumentBuilder(?sharedPrinter: Printer, ?sharedAlternate: SyntaxTree) =
    let ownsAlternate = sharedAlternate.IsNone

    let alternate =
        match sharedAlternate with
        | Some tree -> tree
        | None -> SyntaxTree()

    let conditionalTokens = TokenBuffer()
    let syntax = new SyntaxNodePrinter("", alternate, conditionalTokens)
    let ownsPrinter = sharedPrinter.IsNone

    let printer =
        match sharedPrinter with
        | Some instance -> instance
        | None -> new Printer()

    let mutable maxOutputLength = printer.MaxOutputLength
    let mutable disposed = false
    let mutable selectedSets = 0
    let mutable conditionalParses = 0
    let mutable conditionalRenders = 0
    let mutable parsedCharacters = 0L
    let mutable renderedCharacters = 0L
    let mutable triviaRecords = 0
    let mutable triviaQueries = 0
    let mutable triviaComparisons = 0
    let mutable lambdaVisits = 0
    let mutable lastSymbolSets: string array array = null
    let mutable allConfigurationsComplete = false
    let completeSets = ResizeArray<string array>()
    let renderedSets = HashSet<string>(StringComparer.Ordinal)
    let pendingSets = Queue<string array>()
    let usedSets = HashSet<string>(StringComparer.Ordinal)
    let avoidOrdinals = ResizeArray<int>()

    static member private Complete(tree: SyntaxTree) = SyntaxFacts.complete tree

    static member private ScanTrivia(tree: SyntaxTree) =
        let mutable skipped = 0

        let start =
            if tree.LexerBuffer.HasMalformedTrivia then
                0
            else
                tree.LexerBuffer.TriviaCount

        for i = start to tree.TriviaCount - 1 do
            match (tree.Trivia i).Kind with
            | TriviaKind.ConflictMarkerTrivia ->
                invalidOp "Cannot format unresolved merge conflict markers."
            | TriviaKind.SkippedTokensTrivia -> skipped <- skipped + 1
            | _ -> ()

        skipped

    static member private Incompleteness
        (input: string, tree: SyntaxTree)
        : struct (int * int * int) =
        let mutable position = -1
        let mutable fallback = -1
        let mutable owner = -1
        let mutable index = 0

        while position < 0 && index < tree.TokenCount do
            let token = tree.Token index

            if token.Kind = TokenKind.BadToken then
                position <- token.Start
                fallback <- token.Start
            elif
                token.Length = 0
                && token.Kind <> TokenKind.EndOfFileToken
                && token.Kind <> TokenKind.OmittedArraySizeExpressionToken
                && token.Kind <> TokenKind.OmittedTypeArgumentToken
            then
                fallback <-
                    if index > 0 then
                        (tree.Token(index - 1)).Start
                    else
                        token.Start

                let mutable best = fallback
                let mutable bestStart = -1

                for n = 0 to tree.NodeCount - 1 do
                    let node = tree.Node n

                    if
                        node.TokenStart < index
                        && index < node.TokenStart + node.TokenCount
                        && node.TokenStart > bestStart
                        && (tree.Token node.TokenStart).Length > 0
                    then
                        bestStart <- node.TokenStart
                        best <- (tree.Token node.TokenStart).Start

                position <- best
                owner <- best

                let mutable next = index + 1

                while next < tree.TokenCount && (tree.Token next).Length = 0 do
                    next <- next + 1

                let nextKind =
                    if next < tree.TokenCount then
                        (tree.Token next).Kind
                    else
                        TokenKind.None

                if token.Kind = TokenKind.IdentifierToken && nextKind = TokenKind.ClassKeyword then
                    position <- -1
                    fallback <- -1
                    index <- tree.TokenCount
                elif
                    token.Kind = TokenKind.IdentifierToken
                    && (nextKind = TokenKind.CloseBraceToken
                        || nextKind = TokenKind.WhileKeyword
                        || nextKind = TokenKind.DoKeyword
                        || nextKind = TokenKind.OpenBraceToken)
                then
                    let mutable depth = 0

                    for i = 0 to index - 1 do
                        let previous = tree.Token i

                        if previous.Length > 0 then
                            if previous.Kind = TokenKind.OpenBraceToken then
                                depth <- depth + 1
                            elif previous.Kind = TokenKind.CloseBraceToken then
                                depth <- depth - 1

                    if nextKind = TokenKind.CloseBraceToken && depth <= 0 then
                        position <- -1
                        fallback <- -1
                        index <- tree.TokenCount
                    else
                        position <- token.Start
                        fallback <- -1
                elif
                    token.Kind = TokenKind.IdentifierToken
                    && index > 0
                    && (tree.Token(index - 1)).Kind = TokenKind.AsteriskToken
                    && token.Start > 0
                    && token.Start < input.Length
                    && input[token.Start - 1] = '*'
                    && input[token.Start] = '/'
                then
                    position <- -1
                    fallback <- -1
                    index <- tree.TokenCount
                elif token.Kind = TokenKind.WhileKeyword then
                    position <- -1
                    fallback <- -1
                    index <- tree.TokenCount
                elif token.Kind >= TokenKind.BoolKeyword && token.Kind <= TokenKind.SafeKeyword then
                    position <- token.Start
                    fallback <- -1
                elif
                    token.Kind = TokenKind.SemicolonToken
                    && SyntaxDocumentBuilder.EnclosingOrdinal(input, tree, best) <> ValueNone
                then
                    let mutable depth = 0

                    for i = 0 to index - 1 do
                        let previous = tree.Token i

                        if previous.Length > 0 then
                            if previous.Kind = TokenKind.OpenBraceToken then
                                depth <- depth + 1
                            elif previous.Kind = TokenKind.CloseBraceToken then
                                depth <- depth - 1

                    let mutable continuation = next

                    while continuation < tree.TokenCount
                          && ((tree.Token continuation).Length = 0
                              || (tree.Token continuation).Kind = TokenKind.CloseBraceToken) do
                        continuation <- continuation + 1

                    let continuationKind =
                        if continuation < tree.TokenCount then
                            (tree.Token continuation).Kind
                        else
                            TokenKind.None

                    let branchContinuation =
                        if
                            continuation < tree.TokenCount
                            && continuationKind <> TokenKind.OpenBraceToken
                        then
                            match
                                SyntaxDocumentBuilder.EnclosingBranch(input, tree, best),
                                SyntaxDocumentBuilder.EnclosingBranch(
                                    input,
                                    tree,
                                    (tree.Token continuation).Start
                                )
                            with
                            | ValueSome(struct (owner, parent)),
                              ValueSome(struct (continuation, nextParent)) ->
                                owner <> continuation
                                && (parent = nextParent
                                    || (parent = continuation
                                        && continuationKind <> TokenKind.WhileKeyword))
                            | _ -> false
                        else
                            false

                    if depth > 0 && not branchContinuation then
                        position <- -1
                        fallback <- -1
                        index <- tree.TokenCount

            index <- index + 1

        index <- 0

        while position < 0 && index < tree.NodeCount do
            let node = tree.Node index

            if node.Kind = NodeKind.IncompleteMember && node.TokenCount > 0 then
                position <- (tree.Token node.TokenStart).Start
                fallback <- position

            index <- index + 1

        struct (position, fallback, owner)

    static member private EnclosingBranch
        (input: string, tree: SyntaxTree, position: int)
        : struct (int * int) voption =
        if position < 0 then
            ValueNone
        else
            let ordinals = Dictionary<int, int>()
            let mutable count = -1

            for struct (start, kind) in Preprocessor.directiveLines input do
                if kind < 3 then
                    count <- count + 1
                    ordinals[start] <- count

            let directives =
                [|
                    for index = 0 to min tree.TriviaCount tree.LexerBuffer.TriviaCount - 1 do
                        let item = tree.Trivia index

                        if
                            item.Start <= position
                            && (item.Kind = TriviaKind.IfDirectiveTrivia
                                || item.Kind = TriviaKind.ElifDirectiveTrivia
                                || item.Kind = TriviaKind.ElseDirectiveTrivia
                                || item.Kind = TriviaKind.EndIfDirectiveTrivia)
                        then
                            yield item
                |]
                |> Array.distinctBy (fun item -> item.Start)
                |> Array.sortBy (fun item -> item.Start)

            let frames = Stack<int>()

            let ordinalOf (item: Trivia) =
                match ordinals.TryGetValue item.Start with
                | true, known -> known
                | _ -> -1

            for item in directives do
                match item.Kind with
                | TriviaKind.IfDirectiveTrivia -> frames.Push(ordinalOf item)
                | TriviaKind.ElifDirectiveTrivia
                | TriviaKind.ElseDirectiveTrivia ->
                    if frames.Count > 0 then
                        frames.Pop() |> ignore

                    frames.Push(ordinalOf item)
                | _ ->
                    if frames.Count > 0 then
                        frames.Pop() |> ignore

            if frames.Count = 0 || frames.Peek() < 0 then
                ValueNone
            else
                let branch = frames.Pop()
                let parent = if frames.Count > 0 then frames.Peek() else -1
                ValueSome(struct (branch, parent))

    static member private EnclosingOrdinal(input: string, tree: SyntaxTree, position: int) =
        match SyntaxDocumentBuilder.EnclosingBranch(input, tree, position) with
        | ValueSome(struct (branch, _)) -> ValueSome branch
        | ValueNone -> ValueNone

    static member private RecoveryScope(tree: SyntaxTree, position: int) =
        let scopes = Stack<int>()
        let mutable index = 0

        while index < tree.TokenCount && (tree.Token index).Start < position do
            let token = tree.Token index

            if token.Length > 0 then
                if token.Kind = TokenKind.OpenBraceToken then
                    scopes.Push token.Start
                elif token.Kind = TokenKind.CloseBraceToken && scopes.Count > 0 then
                    scopes.Pop() |> ignore

            index <- index + 1

        if scopes.Count = 0 then position else scopes.Peek()

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    static member private BatchIndependentPasses(sets: string array array) =
        [|
            [|
                for index in 0..2 .. sets.Length - 1 do
                    yield! sets[index]
            |]
            [|
                for index in 1..2 .. sets.Length - 1 do
                    yield! sets[index]
            |]
        |]

    member val internal BatchIndependentRegions = true with get, set

    member _.MaxOutputLength
        with get () = maxOutputLength
        and set value =
            maxOutputLength <- value

            if ownsPrinter then
                printer.MaxOutputLength <- value

    member _.WhitespaceOnly
        with get () = syntax.WhitespaceOnly
        and set value = syntax.WhitespaceOnly <- value

    member internal _.ConditionalWork =
        struct (selectedSets,
                conditionalParses,
                conditionalRenders,
                parsedCharacters,
                renderedCharacters)

    member internal _.HeadTriviaWork = syntax.HeadTriviaWork
    member internal _.LambdaBodyVisits = syntax.LambdaBodyVisits

    member internal _.HeadTriviaWorkTotal =
        struct (triviaRecords, triviaQueries, triviaComparisons)

    member internal _.LambdaBodyVisitsTotal = lambdaVisits

    member private _.Accumulate() =
        let struct (records, queries, comparisons) = syntax.HeadTriviaWork
        triviaRecords <- triviaRecords + records
        triviaQueries <- triviaQueries + queries
        triviaComparisons <- triviaComparisons + comparisons
        lambdaVisits <- lambdaVisits + syntax.LambdaBodyVisits

    member _.Transformations: TransformationWitness =
        {
            SortedUsings = syntax.SortedUsings
            SortedModifiers = syntax.SortedModifiers
            ChangedTrailingCommas = syntax.ChangedTrailingCommas
            ReindentedRawStrings = syntax.ReindentedRawStrings
            SymbolSets = lastSymbolSets
            AllConfigurationsComplete = allConfigurationsComplete
        }

    member this.Build
        (source: string, tree: SyntaxTree, document: DocumentBuffer, options: PrinterOptions)
        =
        this.BuildCore(source, tree, document, options, false, ValueNone)

    member this.BuildAndPrint
        (source: string, tree: SyntaxTree, document: DocumentBuffer, options: PrinterOptions)
        =
        this.BuildCore(source, tree, document, options, true, ValueNone)

    member this.BuildAndPrint
        (
            source: string,
            tree: SyntaxTree,
            document: DocumentBuffer,
            options: PrinterOptions,
            knownAscii: bool voption
        ) =
        this.BuildCore(source, tree, document, options, true, knownAscii)

    member private this.BuildCore
        (
            source: string,
            tree: SyntaxTree,
            document: DocumentBuffer,
            options: PrinterOptions,
            renderFinal: bool,
            knownAscii: bool voption
        ) =
        ObjectDisposedException.ThrowIf(disposed, typeof<SyntaxDocumentBuilder>)
        syntax.ClearWitness()
        let built = DocumentStats.enter ()
        DocumentStats.event DocumentStats.nFiles
        let found = DocumentStats.enter ()

        let struct (initialSets, sets, independent, discovery) =
            Preprocessor.symbolSetsWithInitial source tree (ValueSome conditionalTokens)

        lastSymbolSets <- if tree.LexerBuffer.HasSeededSymbols then null else sets

        let literalSets = sets
        let sets = if syntax.WhitespaceOnly then Array.empty else sets

        allConfigurationsComplete <- false
        DocumentStats.lapse DocumentStats.tDiscovery found

        let passes =
            if this.BatchIndependentRegions && independent then
                SyntaxDocumentBuilder.BatchIndependentPasses sets
            else
                sets

        selectedSets <- sets.Length
        conditionalParses <- 0
        conditionalRenders <- 0
        parsedCharacters <- 0L
        renderedCharacters <- 0L
        triviaRecords <- 0
        triviaQueries <- 0
        triviaComparisons <- 0
        lambdaVisits <- 0
        let initialComplete = SyntaxDocumentBuilder.Complete tree

        if sets.Length = 0 then
            allConfigurationsComplete <- not tree.LexerBuffer.HasSeededSymbols && initialComplete

            syntax.ResetCore(
                source,
                tree,
                ValueNone,
                ValueNone,
                not initialComplete,
                false,
                ValueSome(if syntax.WhitespaceOnly then literalSets else passes),
                false,
                ValueNone,
                knownAscii
            )

            let savedMaxOutputLength = printer.MaxOutputLength
            let singleMaxOutputLength = min savedMaxOutputLength maxOutputLength

            if not options.TrimInitialLines && singleMaxOutputLength < Array.MaxLength then
                syntax.SetOutputLimit(
                    singleMaxOutputLength,
                    options.Width,
                    (if options.UseTabs then 1 else options.IndentSize)
                )

            let walked = DocumentStats.enter ()
            syntax.Build(document)
            DocumentStats.lapse DocumentStats.tWalk walked
            DocumentStats.lapse DocumentStats.tBuild built
            this.Accumulate()

            if renderFinal then
                printer.TrackSourceMappings <- false
                printer.MaxOutputLength <- singleMaxOutputLength

                try
                    printer.Print(source, document, options)
                finally
                    printer.MaxOutputLength <- savedMaxOutputLength
        else
            this.BuildMultiConfiguration(
                source,
                tree,
                document,
                options,
                renderFinal,
                knownAscii,
                built,
                initialSets,
                passes,
                independent,
                discovery,
                initialComplete
            )

    [<MethodImpl(MethodImplOptions.NoInlining)>]
    member private this.BuildMultiConfiguration
        (
            source,
            tree,
            document,
            options,
            renderFinal,
            knownAscii,
            built,
            initialSets,
            passes,
            independent,
            discovery,
            initialComplete
        ) =
        let savedMaxOutputLength = printer.MaxOutputLength

        let pass1MaxOutputLength =
            if savedMaxOutputLength < maxOutputLength && initialComplete then
                let trivia = tree.LexerBuffer.TriviaSpan()
                let mutable depth = 0
                let mutable branchStart = 0
                let mutable disabledLength = 0L
                let mutable hasActiveDelimiter = false

                for i = 0 to trivia.Length - 1 do
                    let item = &trivia[i]

                    match item.Kind with
                    | TriviaKind.DisabledTextTrivia ->
                        disabledLength <- disabledLength + int64 item.Length

                        if depth > 0 then
                            branchStart <- item.Start + item.Length
                    | TriviaKind.IfDirectiveTrivia
                    | TriviaKind.ElifDirectiveTrivia
                    | TriviaKind.ElseDirectiveTrivia
                    | TriviaKind.EndIfDirectiveTrivia ->
                        if depth > 0 && item.Start > branchStart && not hasActiveDelimiter then
                            if
                                source
                                    .AsSpan(branchStart, item.Start - branchStart)
                                    .IndexOfAny('{', '(')
                                >= 0
                            then
                                hasActiveDelimiter <- true

                        if item.Kind = TriviaKind.IfDirectiveTrivia then
                            depth <- depth + 1
                        elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                            depth <- max 0 (depth - 1)

                        branchStart <- item.Start + item.Length
                    | _ -> ()

                if hasActiveDelimiter then
                    maxOutputLength
                else
                    int (min (int64 maxOutputLength) (int64 savedMaxOutputLength + disabledLength))
            else
                maxOutputLength

        printer.MaxOutputLength <- pass1MaxOutputLength

        try
            let initialSkipped = SyntaxDocumentBuilder.ScanTrivia tree

            let trackOwnership =
                SyntaxFacts.literalOwnershipNeededCore
                    true
                    source
                    tree
                    initialComplete
                    independent
                    discovery
                    (ValueSome conditionalTokens)

            let emptyOwnership =
                ValueSome(struct (Array.empty<bool>, Array.empty<bool>, Array.empty<int>, 0))

            syntax.ResetCore(
                source,
                tree,
                ValueNone,
                ValueNone,
                not initialComplete,
                false,
                ValueSome passes,
                false,
                (if trackOwnership then ValueNone else emptyOwnership),
                knownAscii
            )

            let initialSourceIsAscii = syntax.SourceIsAscii

            document.Reset()

            DocumentStats.event DocumentStats.nConditionalFiles
            let prepared = DocumentStats.enter ()

            let mutable trackSourceMappings = false

            let initialOwnership =
                if trackOwnership then
                    let initial = syntax.PrepareLiteralOwnership()
                    let struct (_, _, _, initialLen) = initial
                    trackSourceMappings <- initialLen > 0
                    printer.TrackSourceMappings <- trackSourceMappings && initialComplete
                    if initialLen > 0 then ValueSome initial else emptyOwnership
                else
                    printer.TrackSourceMappings <- false
                    emptyOwnership

            DocumentStats.lapse DocumentStats.tOwnership prepared

            if not options.TrimInitialLines && printer.MaxOutputLength < Array.MaxLength then
                syntax.SetOutputLimit(
                    printer.MaxOutputLength,
                    options.Width,
                    (if options.UseTabs then 1 else options.IndentSize)
                )

            let walked = DocumentStats.enter ()
            syntax.Build(document)
            DocumentStats.lapse DocumentStats.tWalk walked
            let rendered = DocumentStats.enter ()
            printer.Print(source, document, options)
            DocumentStats.lapse DocumentStats.tPassRender rendered
            printer.MaxOutputLength <- maxOutputLength
            printer.TrackSourceMappings <- trackSourceMappings
            conditionalRenders <- 1
            renderedCharacters <- int64 source.Length

            let mutable formatted =
                if not initialComplete && renderFinal then
                    source
                else
                    printer.OutputText

            let mutable printerMatchesFormatted = true

            let remapped = DocumentStats.enter ()

            let mutable ownership =
                if trackSourceMappings then
                    if not initialComplete || Object.ReferenceEquals(formatted, source) then
                        initialOwnership
                    else
                        ValueSome(
                            syntax.RemapLiteralOwnership(formatted.Length, printer.SourceMappings)
                        )
                else
                    emptyOwnership

            DocumentStats.lapse DocumentStats.tOwnership remapped

            let mutable pendingDirectives = ValueNone

            let indexDirectives (symbols: string array) = pendingDirectives <- ValueSome symbols

            if initialComplete then
                indexDirectives Array.empty

            let complete = completeSets
            complete.Clear()
            renderedSets.Clear()
            let pending = pendingSets
            pending.Clear()

            for pass in passes do
                pending.Enqueue pass

            let used = usedSets
            used.Clear()
            let avoids = avoidOrdinals
            avoids.Clear()
            let mutable reselects = 0
            let mutable rejectedConfiguration = false
            let mutable searching = true

            let parse (symbols: string array) =
                let input =
                    if conditionalRenders = 1 && not initialComplete then
                        source
                    else
                        formatted

                let parsed = DocumentStats.enter ()
                let baseBuf = tree.LexerBuffer
                let tokHint = baseBuf.TokenCount + (baseBuf.TokenCount >>> 4) + 32

                let trivHint =
                    max
                        (baseBuf.TriviaCount + (baseBuf.TriviaCount >>> 4) + 64)
                        (baseBuf.TokenCount + 64)

                Parser.parseWithHinted symbols tokHint trivHint input alternate
                DocumentStats.lapse DocumentStats.tPassParse parsed
                let readable = SyntaxDocumentBuilder.ScanTrivia alternate <= initialSkipped
                conditionalParses <- conditionalParses + 1
                parsedCharacters <- parsedCharacters + int64 input.Length
                struct (input, SyntaxDocumentBuilder.Complete alternate && readable)

            while searching do
                let mutable progress = true
                let mutable rejected = ValueNone

                while progress && pending.Count > 0 do
                    progress <- false
                    rejected <- ValueNone

                    for _ = 1 to pending.Count do
                        let symbols = pending.Dequeue()
                        let struct (firstInput, firstParsed) = parse symbols
                        rejectedConfiguration <- rejectedConfiguration || not firstParsed
                        let mutable input = firstInput
                        let mutable parsed = firstParsed
                        let mutable effective = symbols
                        let mutable index = 0

                        while not parsed && index < complete.Count do
                            let combined = Array.append symbols complete[index] |> Array.distinct

                            let struct (nextInput, nextParsed) = parse combined
                            input <- nextInput
                            parsed <- nextParsed
                            effective <- combined
                            index <- index + 1

                        if not parsed then
                            if rejected = ValueNone then
                                let struct (position, fallback, owner) =
                                    SyntaxDocumentBuilder.Incompleteness(input, alternate)

                                rejected <-
                                    SyntaxDocumentBuilder.EnclosingOrdinal(
                                        input,
                                        alternate,
                                        position
                                    )

                                if rejected = ValueNone && fallback <> position then
                                    rejected <-
                                        SyntaxDocumentBuilder.EnclosingOrdinal(
                                            input,
                                            alternate,
                                            fallback
                                        )

                                if rejected = ValueNone then
                                    rejected <-
                                        SyntaxDocumentBuilder.EnclosingOrdinal(
                                            input,
                                            alternate,
                                            SyntaxDocumentBuilder.RecoveryScope(alternate, owner)
                                        )

                            pending.Enqueue symbols
                        else
                            progress <- true

                            let key =
                                if effective.Length = 1 then
                                    effective[0]
                                else
                                    String.Join("\000", Array.sort effective)

                            used.Add key |> ignore

                            if renderedSets.Add key then
                                complete.Add effective
                                document.Reset()
                                this.Accumulate()

                                let isForeignCode =
                                    not (
                                        initialSets
                                        |> Array.exists (fun symbols -> symbols = effective)
                                    )

                                syntax.ResetCore(
                                    input,
                                    alternate,
                                    ValueNone,
                                    pendingDirectives,
                                    not initialComplete,
                                    rejectedConfiguration,
                                    ValueSome passes,
                                    isForeignCode,
                                    (if conditionalRenders = 1 && not initialComplete then
                                         initialOwnership
                                     else
                                         ownership),
                                    (if initialSourceIsAscii then ValueSome true else ValueNone)
                                )

                                if
                                    not options.TrimInitialLines
                                    && printer.MaxOutputLength < Array.MaxLength
                                then
                                    syntax.SetOutputLimit(
                                        printer.MaxOutputLength,
                                        options.Width,
                                        (if options.UseTabs then 1 else options.IndentSize)
                                    )

                                let walked = DocumentStats.enter ()
                                syntax.Build(document)
                                DocumentStats.lapse DocumentStats.tPassWalk walked

                                if pending.Count = 0 && not isForeignCode then
                                    printer.TrackSourceMappings <- false

                                let rendered = DocumentStats.enter ()
                                printer.Print(input, document, options)
                                DocumentStats.lapse DocumentStats.tPassRender rendered
                                conditionalRenders <- conditionalRenders + 1
                                renderedCharacters <- renderedCharacters + int64 input.Length

                                if
                                    renderFinal
                                    && pending.Count = 0
                                    && not printer.TrackSourceMappings
                                then
                                    printerMatchesFormatted <- true
                                else
                                    let passOutput = printer.OutputText

                                    formatted <-
                                        syntax.PreserveLiteralGaps(
                                            passOutput,
                                            printer.SourceMappings
                                        )

                                    printerMatchesFormatted <-
                                        LanguagePrimitives.PhysicalEquality formatted passOutput

                                    let remapped = DocumentStats.enter ()

                                    if printer.TrackSourceMappings && pending.Count > 0 then
                                        ownership <-
                                            if Object.ReferenceEquals(formatted, input) then
                                                ValueSome syntax.CurrentLiteralOwnership
                                            else
                                                ValueSome(
                                                    syntax.RemapLiteralOwnership(
                                                        formatted.Length,
                                                        printer.SourceMappings
                                                    )
                                                )

                                    DocumentStats.lapse DocumentStats.tOwnership remapped

                                    indexDirectives effective

                searching <- false

                if pending.Count > 0 && reselects < 8 then
                    match rejected with
                    | ValueSome ordinal when not (avoids.Contains ordinal) ->
                        avoids.Add ordinal
                        reselects <- reselects + 1
                        pending.Clear()

                        for symbols in
                            Preprocessor.alternativeSets
                                source
                                tree
                                (avoids.ToArray())
                                (complete.ToArray()) do
                            if
                                used.Add(
                                    if symbols.Length = 1 then
                                        symbols[0]
                                    else
                                        String.Join("\000", Array.sort symbols)
                                )
                            then
                                pending.Enqueue symbols

                        searching <- pending.Count > 0
                    | _ -> ()

            allConfigurationsComplete <-
                not tree.LexerBuffer.HasSeededSymbols
                && initialComplete
                && not rejectedConfiguration
                && pending.Count = 0

            if renderFinal then
                DocumentStats.lapse DocumentStats.tBuild built
                this.Accumulate()
                printer.MaxOutputLength <- min savedMaxOutputLength maxOutputLength
                printer.TrackSourceMappings <- false

                if printerMatchesFormatted then
                    printer.CheckOutputLimit()
                else
                    document.Reset()
                    document.AddGeneratedText(formatted.AsSpan())
                    printer.Print(source, document, options)
            else
                document.Reset()
                document.AddGeneratedText(formatted.AsSpan())
                DocumentStats.lapse DocumentStats.tBuild built
                this.Accumulate()
        finally
            printer.MaxOutputLength <- savedMaxOutputLength
            printer.TrackSourceMappings <- false

    interface IDisposable with
        member _.Dispose() =
            if not disposed then
                disposed <- true
                (syntax :> IDisposable).Dispose()
                conditionalTokens.ReleasePooledBuffers()

                if ownsAlternate then
                    alternate.ReleasePooledBuffers()

                if ownsPrinter then
                    (printer :> IDisposable).Dispose()

module SyntaxPrinter =
    let printNode (source: string) (tree: SyntaxTree) (nodeIndex: int) (document: DocumentBuffer) =
        use syntax = new SyntaxNodePrinter(source, tree)
        syntax.PrintNode(nodeIndex, document)

    let build source tree document options =
        if Array.isEmpty (Preprocessor.symbolSets source tree) then
            use syntax = new SyntaxNodePrinter(source, tree)
            let walked = DocumentStats.enter ()
            syntax.Build(document)
            DocumentStats.lapse DocumentStats.tWalk walked
        else
            use builder = new SyntaxDocumentBuilder()
            builder.Build(source, tree, document, options)
