namespace Csff.Gate

open System
open System.Collections.Generic
open System.Text
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Text

type Category =
    | Structural
    | Directives
    | UsingScope
    | NewSyntaxError

    member this.Name =
        match this with
        | Structural -> "structural"
        | Directives -> "directives"
        | UsingScope -> "using-scope"
        | NewSyntaxError -> "new-syntax-error"

type Finding =
    {
        Category: Category
        Configuration: string
        Detail: string
    }

type Outcome =
    {
        Findings: Finding list
        SourceHadErrors: bool
        Configurations: int
        SymbolsCapped: bool
    }

module Adjudicator =
    let parseOptions =
        CSharpParseOptions(LanguageVersion.Preview, DocumentationMode.Diagnose)
            .WithFeatures([ KeyValuePair("FileBasedProgram", "true") ])

    let internal parse (text: string) (options: CSharpParseOptions) =
        CSharpSyntaxTree.ParseText(text, options).GetRoot()

    let private normalizeNewlines (text: string) =
        if text.IndexOf '\r' < 0 then
            text
        else
            text.Replace("\r\n", "\n").Replace('\r', '\n')

    let private canonicalLayout (text: string) =
        let unified = normalizeNewlines text

        if unified.IndexOf '\n' < 0 then
            unified.TrimStart(' ', '\t')
        else
            let lines = unified.Split '\n'

            for index = 0 to lines.Length - 1 do
                lines[index] <- lines[index].TrimStart(' ', '\t')

            String.Join('\n', lines)

    let private valueBearingLiteral (kind: SyntaxKind) =
        match kind with
        | SyntaxKind.StringLiteralToken
        | SyntaxKind.Utf8StringLiteralToken
        | SyntaxKind.SingleLineRawStringLiteralToken
        | SyntaxKind.MultiLineRawStringLiteralToken
        | SyntaxKind.Utf8SingleLineRawStringLiteralToken
        | SyntaxKind.Utf8MultiLineRawStringLiteralToken
        | SyntaxKind.InterpolatedStringTextToken -> true
        | _ -> false

    let private delimiterOnly (kind: SyntaxKind) =
        match kind with
        | SyntaxKind.InterpolatedSingleLineRawStringStartToken
        | SyntaxKind.InterpolatedMultiLineRawStringStartToken
        | SyntaxKind.InterpolatedRawStringEndToken -> true
        | _ -> false

    let internal textAgrees (left: SyntaxToken) (right: SyntaxToken) =
        if String.Equals(left.Text, right.Text, StringComparison.Ordinal) then
            true
        else
            let kind = left.Kind()

            if delimiterOnly kind then
                canonicalLayout left.Text = canonicalLayout right.Text
            elif valueBearingLiteral kind then
                normalizeNewlines left.ValueText = normalizeNewlines right.ValueText
                && canonicalLayout left.Text = canonicalLayout right.Text
            else
                false

    let private permitsTrailingSeparator (node: SyntaxNode) =
        match node with
        | :? InitializerExpressionSyntax as initializer ->
            not (initializer.IsKind SyntaxKind.ComplexElementInitializerExpression)
        | :? AnonymousObjectCreationExpressionSyntax
        | :? CollectionExpressionSyntax
        | :? ListPatternSyntax
        | :? SwitchExpressionSyntax
        | :? EnumDeclarationSyntax
        | :? PropertyPatternClauseSyntax
        | :? AttributeListSyntax -> true
        | _ -> false

    let private closingTokenKind (node: SyntaxNode) =
        match node with
        | :? InitializerExpressionSyntax as initializer ->
            if initializer.IsKind SyntaxKind.ComplexElementInitializerExpression then
                SyntaxKind.None
            else
                SyntaxKind.CloseBraceToken
        | :? AnonymousObjectCreationExpressionSyntax
        | :? SwitchExpressionSyntax
        | :? EnumDeclarationSyntax
        | :? PropertyPatternClauseSyntax -> SyntaxKind.CloseBraceToken
        | :? CollectionExpressionSyntax
        | :? ListPatternSyntax
        | :? AttributeListSyntax -> SyntaxKind.CloseBracketToken
        | _ -> SyntaxKind.None

    let private isComma (item: SyntaxNodeOrToken) =
        item.IsToken && item.AsToken().IsKind SyntaxKind.CommaToken

    let private isOpener (item: SyntaxNodeOrToken) =
        item.IsToken
        && (let token = item.AsToken()

            token.IsKind SyntaxKind.OpenBraceToken
            || token.IsKind SyntaxKind.OpenBracketToken)

    let private isUsing (item: SyntaxNodeOrToken) =
        item.IsNode && (item.AsNode() :? UsingDirectiveSyntax)

    let private holdsUsings (node: SyntaxNode) =
        node :? CompilationUnitSyntax || node :? BaseNamespaceDeclarationSyntax

    let private isContextDirective (directive: DirectiveTriviaSyntax) =
        directive.IsActive
        && match directive.Kind() with
           | SyntaxKind.DefineDirectiveTrivia
           | SyntaxKind.UndefDirectiveTrivia
           | SyntaxKind.NullableDirectiveTrivia
           | SyntaxKind.LineDirectiveTrivia
           | SyntaxKind.PragmaWarningDirectiveTrivia
           | SyntaxKind.PragmaChecksumDirectiveTrivia -> true
           | _ -> false

    let private hasContextDirective (triviaList: SyntaxTriviaList) =
        triviaList
        |> Seq.exists (fun trivia ->
            trivia.IsDirective
            && match trivia.GetStructure() with
               | :? DirectiveTriviaSyntax as directive -> isContextDirective directive
               | _ -> false)

    let private contextBetweenUsings (left: SyntaxNodeOrToken) (right: SyntaxNodeOrToken) =
        hasContextDirective (left.AsNode().GetTrailingTrivia())
        || hasContextDirective (right.AsNode().GetLeadingTrivia())

    let private trailingSeparatorSlot (node: SyntaxNode) =
        let closingKind = closingTokenKind node

        if closingKind = SyntaxKind.None then
            -1
        else
            let children = node.ChildNodesAndTokens()
            let mutable index = children.Count - 1

            while index >= 0
                  && not (
                      children[index].IsToken
                      && children[index].AsToken().IsKind closingKind
                      && not (children[index].AsToken().IsMissing)
                  ) do
                index <- index - 1

            if
                index >= 3
                && isComma children[index - 1]
                && not (isComma children[index - 2])
                && not (isOpener children[index - 2])
            then
                index - 1
            else
                -1

    let private modifiersOf (node: SyntaxNode) =
        match node with
        | :? MemberDeclarationSyntax as declaration -> declaration.Modifiers
        | :? LocalFunctionStatementSyntax as declaration -> declaration.Modifiers
        | :? AccessorDeclarationSyntax as declaration -> declaration.Modifiers
        | _ -> SyntaxTokenList()

    let private modifierSpan (node: SyntaxNode) =
        let modifiers = modifiersOf node

        if modifiers.Count = 0 then
            TextSpan(0, 0)
        else
            modifiers.Span

    let private modifierKey (node: SyntaxNode) =
        modifiersOf node
        |> Seq.map (fun token -> String.Format("{0} {1}", token.RawKind, token.Text))
        |> Seq.sortWith (fun left right -> String.CompareOrdinal(left, right))
        |> String.concat " "

    let internal directiveKey (node: SyntaxNode) =
        let builder = StringBuilder()

        for token in node.DescendantTokens() do
            builder.Append(token.RawKind).Append(' ').Append(token.Text).Append ' '
            |> ignore

        builder.ToString()

    [<Struct; NoComparison; NoEquality>]
    type private Children =
        {
            List: ChildSyntaxList
            Rewritten: ResizeArray<SyntaxNodeOrToken>
        }

        member this.Count =
            if isNull this.Rewritten then
                this.List.Count
            else
                this.Rewritten.Count

        member this.Item
            with get (index: int) =
                if isNull this.Rewritten then
                    this.List[index]
                else
                    this.Rewritten[index]

    let private prepare (node: SyntaxNode) =
        let list = node.ChildNodesAndTokens()
        let sorts = holdsUsings node
        let separator = trailingSeparatorSlot node

        if not sorts && separator < 0 then
            { List = list; Rewritten = null }
        else
            let items = ResizeArray<SyntaxNodeOrToken>(list.Count)

            for index = 0 to list.Count - 1 do
                items.Add list[index]

            if sorts then
                let mutable start = 0

                while start < items.Count do
                    if isUsing items[start] then
                        let mutable finish = start + 1

                        while finish < items.Count
                              && isUsing items[finish]
                              && not (contextBetweenUsings items[finish - 1] items[finish]) do
                            finish <- finish + 1

                        if finish - start > 1 then
                            let run =
                                Array.init (finish - start) (fun offset ->
                                    struct (directiveKey (items[start + offset].AsNode()),
                                            offset,
                                            items[start + offset]))

                            Array.sortInPlaceWith
                                (fun
                                    (struct (leftKey, leftIndex, _))
                                    (struct (rightKey, rightIndex, _)) ->
                                    let compared = String.CompareOrdinal(leftKey, rightKey)

                                    if compared <> 0 then
                                        compared
                                    else
                                        compare leftIndex rightIndex)
                                run

                            for offset = 0 to run.Length - 1 do
                                let struct (_, _, item) = run[offset]
                                items[start + offset] <- item

                        start <- finish
                    else
                        start <- start + 1

            if separator >= 0 then
                items.RemoveAt separator

            { List = list; Rewritten = items }

    let private describe (item: SyntaxNodeOrToken) =
        if item.IsToken then
            let text = item.AsToken().Text

            let shown =
                (if text.Length > 48 then
                     text.Substring(0, 48) + "..."
                 else
                     text)
                    .Replace("\r", "\\r")
                    .Replace("\n", "\\n")

            String.Format("{0} '{1}' at {2}", item.Kind(), shown, item.SpanStart)
        else
            String.Format("{0} at {1}", item.Kind(), item.SpanStart)

    let internal compareTrees (before: SyntaxNode) (after: SyntaxNode) =
        let pending = Stack<struct (SyntaxNode * SyntaxNode)>()
        pending.Push(struct (before, after))
        let mutable mismatch: string = null

        while isNull mismatch && pending.Count > 0 do
            let struct (left, right) = pending.Pop()

            if left.RawKind <> right.RawKind then
                mismatch <-
                    String.Format(
                        "{0} at {1} vs {2} at {3}",
                        left.Kind(),
                        left.SpanStart,
                        right.Kind(),
                        right.SpanStart
                    )
            else
                let leftModifiers = modifierSpan left
                let rightModifiers = modifierSpan right

                if leftModifiers.Length <> rightModifiers.Length then
                    let leftKey = modifierKey left
                    let rightKey = modifierKey right

                    if leftKey <> rightKey then
                        mismatch <-
                            String.Format(
                                "modifiers '{0}' vs '{1}' on {2} at {3}",
                                leftKey,
                                rightKey,
                                left.Kind(),
                                left.SpanStart
                            )

                if isNull mismatch then
                    let leftChildren = prepare left
                    let rightChildren = prepare right

                    if leftChildren.Count <> rightChildren.Count then
                        mismatch <-
                            String.Format(
                                "{0} at {1}: {2} children vs {3} at {4}",
                                left.Kind(),
                                left.SpanStart,
                                leftChildren.Count,
                                rightChildren.Count,
                                right.SpanStart
                            )
                    else
                        let mutable index = 0

                        while isNull mismatch && index < leftChildren.Count do
                            let a = leftChildren[index]
                            let b = rightChildren[index]

                            if
                                a.IsToken
                                && b.IsToken
                                && leftModifiers.Contains a.SpanStart
                                && rightModifiers.Contains b.SpanStart
                            then
                                let mutable leftEnd = index

                                while leftEnd < leftChildren.Count
                                      && leftChildren[leftEnd].IsToken
                                      && leftModifiers.Contains leftChildren[leftEnd].SpanStart do
                                    leftEnd <- leftEnd + 1

                                let mutable rightEnd = index

                                while rightEnd < rightChildren.Count
                                      && rightChildren[rightEnd].IsToken
                                      && rightModifiers.Contains rightChildren[rightEnd].SpanStart do
                                    rightEnd <- rightEnd + 1

                                if leftEnd <> rightEnd || modifierKey left <> modifierKey right then
                                    mismatch <-
                                        String.Format(
                                            "modifier run {0} vs {1} on {2} at {3}",
                                            leftEnd - index,
                                            rightEnd - index,
                                            left.Kind(),
                                            left.SpanStart
                                        )

                                index <- leftEnd
                            elif a.RawKind <> b.RawKind || a.IsToken <> b.IsToken then
                                mismatch <- String.Format("{0} vs {1}", describe a, describe b)
                            elif a.IsToken then
                                if not (textAgrees (a.AsToken()) (b.AsToken())) then
                                    mismatch <- String.Format("{0} vs {1}", describe a, describe b)

                                index <- index + 1
                            else
                                pending.Push(struct (a.AsNode(), b.AsNode()))
                                index <- index + 1

        mismatch

    type private DirectiveShape =
        {
            Texts: string array
            Anchors: int array
            Frames: string array
        }

    let private frameSeparator = string (char 1)

    let private conditionText (condition: ExpressionSyntax) =
        if isNull (box condition) then
            ""
        else
            let builder = StringBuilder()

            for token in condition.DescendantTokens() do
                builder.Append(token.Text).Append ' ' |> ignore

            builder.ToString()

    let private directiveShape (root: SyntaxNode) =
        let ignored = HashSet<int>()
        let usings = ResizeArray<struct (int * string)>()

        for node in root.DescendantNodesAndSelf() do
            match node with
            | :? UsingDirectiveSyntax ->
                usings.Add(struct (node.SpanStart, directiveKey node))

                for token in node.DescendantTokens() do
                    ignored.Add token.SpanStart |> ignore
            | _ ->
                let separator = trailingSeparatorSlot node

                if separator >= 0 then
                    let children = node.ChildNodesAndTokens()
                    ignored.Add children[separator].SpanStart |> ignore

        let tokens = root.DescendantTokens() |> Seq.toArray

        usings.Sort(fun left right ->
            let struct (leftStart, _) = left
            let struct (rightStart, _) = right
            compare leftStart rightStart)

        let texts = ResizeArray<string>()
        let anchors = ResizeArray<int>()
        let frames = ResizeArray<string>()
        let conditionals = ResizeArray<struct (string * int)>()
        let mutable contextSegment = 0
        let mutable tokenIndex = 0
        let mutable usingIndex = 0
        let mutable preceding = 0

        let frameKey () =
            let builder = StringBuilder()
            builder.Append(contextSegment).Append '|' |> ignore

            for index = 0 to conditionals.Count - 1 do
                let struct (condition, branch) = conditionals[index]
                builder.Append(condition).Append('#').Append(branch).Append '/' |> ignore

            builder.ToString()

        let takeUsingsBefore limit =
            let mutable go = true

            while go && usingIndex < usings.Count do
                let struct (start, key) = usings[usingIndex]

                if start < limit then
                    frames.Add(frameKey () + frameSeparator + key)
                    usingIndex <- usingIndex + 1
                else
                    go <- false

        let enter (directive: DirectiveTriviaSyntax) =
            match directive with
            | :? IfDirectiveTriviaSyntax as opening ->
                conditionals.Add(struct (conditionText opening.Condition, 0))
            | :? ElifDirectiveTriviaSyntax
            | :? ElseDirectiveTriviaSyntax ->
                if conditionals.Count = 0 then
                    conditionals.Add(struct ("<unbalanced>", 0))
                else
                    let last = conditionals.Count - 1
                    let struct (condition, branch) = conditionals[last]
                    conditionals[last] <- struct (condition, branch + 1)
            | :? EndIfDirectiveTriviaSyntax ->
                if conditionals.Count = 0 then
                    conditionals.Add(struct ("<unbalanced-endif>", 0))
                else
                    conditionals.RemoveAt(conditionals.Count - 1)
            | _ when isContextDirective directive -> contextSegment <- contextSegment + 1
            | _ -> ()

        for trivia in root.DescendantTrivia(descendIntoTrivia = true) do
            match trivia.GetStructure() with
            | :? DirectiveTriviaSyntax as directive ->
                while tokenIndex < tokens.Length && tokens[tokenIndex].Span.End <= trivia.SpanStart do
                    if not (ignored.Contains tokens[tokenIndex].SpanStart) then
                        preceding <- preceding + 1

                    tokenIndex <- tokenIndex + 1

                takeUsingsBefore trivia.SpanStart
                anchors.Add preceding
                let builder = StringBuilder()
                builder.Append(directive.RawKind).Append ' ' |> ignore

                for token in directive.DescendantTokens() do
                    for nestedTrivia in token.LeadingTrivia do
                        if
                            nestedTrivia.IsKind SyntaxKind.PreprocessingMessageTrivia
                            || nestedTrivia.IsKind SyntaxKind.SkippedTokensTrivia
                        then
                            builder.Append(nestedTrivia.ToFullString().Trim()).Append ' ' |> ignore

                    builder.Append(token.Text).Append ' ' |> ignore

                    for nestedTrivia in token.TrailingTrivia do
                        if
                            nestedTrivia.IsKind SyntaxKind.PreprocessingMessageTrivia
                            || nestedTrivia.IsKind SyntaxKind.SkippedTokensTrivia
                        then
                            builder.Append(nestedTrivia.ToFullString().Trim()).Append ' ' |> ignore

                texts.Add(builder.ToString())
                enter directive
            | _ -> ()

        takeUsingsBefore Int32.MaxValue
        frames.Sort(fun left right -> String.CompareOrdinal(left, right))

        {
            Texts = texts.ToArray()
            Anchors = anchors.ToArray()
            Frames = frames.ToArray()
        }

    let private firstDifference (left: 'a array) (right: 'a array) =
        let mutable index = 0

        while index < min left.Length right.Length && left[index] = right[index] do
            index <- index + 1

        index

    let internal errorCounts (root: SyntaxNode) =
        let counts = Dictionary<string, int>()

        for diagnostic in root.GetDiagnostics() do
            if diagnostic.Severity = DiagnosticSeverity.Error then
                let key = diagnostic.Id + ": " + diagnostic.GetMessage()
                let mutable held = 0
                counts.TryGetValue(key, &held) |> ignore
                counts[key] <- held + 1

        counts

    let private newError (before: SyntaxNode) (after: SyntaxNode) =
        let previous = errorCounts before
        let mutable introduced: string = null

        for entry in errorCounts after do
            if isNull introduced then
                let mutable held = 0

                if not (previous.TryGetValue(entry.Key, &held)) || held < entry.Value then
                    introduced <- entry.Key

        introduced

    let inline private preprocessorSymbolName (tok: SyntaxToken) =
        if tok.IsMissing then
            ""
        else
            let vt = tok.ValueText
            if String.IsNullOrEmpty vt then tok.Text else vt

    let internal conditionalSymbols (roots: SyntaxNode list) =
        let found = SortedSet<string>(StringComparer.Ordinal)

        for root in roots do
            if root.ContainsDirectives then
                for trivia in root.DescendantTrivia(descendIntoTrivia = true) do
                    let condition =
                        match trivia.GetStructure() with
                        | :? IfDirectiveTriviaSyntax as directive -> directive.Condition
                        | :? ElifDirectiveTriviaSyntax as directive -> directive.Condition
                        | _ -> null

                    if not (isNull condition) then
                        for node in condition.DescendantNodesAndSelf() do
                            match node with
                            | :? IdentifierNameSyntax as name ->
                                let sym = preprocessorSymbolName name.Identifier

                                if not (String.IsNullOrEmpty sym) then
                                    found.Add sym |> ignore
                            | _ -> ()

        found

    [<AllowNullLiteral; NoComparison; NoEquality>]
    type private GuardNode
        (
            guardTrue: ExpressionSyntax array,
            guardFalse: ExpressionSyntax array,
            parent: GuardNode,
            isSealed: bool
        ) =
        let mutable gt = guardTrue
        let mutable gf = guardFalse
        let mutable p = parent
        let mutable s = isSealed
        let mutable fullySealed = false
        member _.GuardTrue = gt
        member _.GuardFalse = gf
        member _.Parent = p
        member _.IsSealed = s

        member this.IsFullySealed =
            if fullySealed then
                true
            elif not s then
                false
            elif isNull p then
                fullySealed <- true
                true
            elif p.FullySealedDirect then
                fullySealed <- true
                true
            else
                let chain = Stack<GuardNode>()
                let mutable cur: GuardNode = this
                let mutable ok = true

                while ok && not (isNull cur) && not cur.FullySealedDirect do
                    if not cur.IsSealed then
                        ok <- false
                    else
                        chain.Push cur
                        cur <- cur.Parent

                if ok then
                    while chain.Count > 0 do
                        chain.Pop().MarkFullySealed()

                ok

        member _.FullySealedDirect = fullySealed
        member _.MarkFullySealed() = fullySealed <- true

        member _.Seal
            (
                guardTrue: ExpressionSyntax array,
                guardFalse: ExpressionSyntax array,
                parent: GuardNode
            ) =
            gt <- guardTrue
            gf <- guardFalse
            p <- parent
            s <- true

            if isNull parent || parent.FullySealedDirect then
                fullySealed <- true

    let private guardNodeRefComparer =
        { new IEqualityComparer<GuardNode> with
            member _.Equals(a, b) = obj.ReferenceEquals(a, b)

            member _.GetHashCode(g) =
                System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode g
        }

    let inline private hashSymbol64 (s: string) : uint64 =
        let h1 = uint64 (uint32 (StringComparer.Ordinal.GetHashCode s))
        let h2 = uint64 (uint32 s.Length) <<< 32
        let mutable z = (h1 ||| h2) ^^^ 0x9E3779B97F4A7C15UL
        z <- (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9UL
        z <- (z ^^^ (z >>> 27)) * 0x94D049BB133111EBUL
        z ^^^ (z >>> 31)

    [<Struct; NoComparison; NoEquality>]
    type private DepCacheEntry =
        {
            Result: ValueOption<bool>
            HasPos: bool
            PosDefined: Set<string>
            NegLo: uint64
            NegHi: uint64
            NegMaxPos: int
        }

    [<Struct; NoComparison; NoEquality>]
    type private GuardEvalCached =
        {
            Result: ValueOption<bool>
            HasPos: bool
            NegLo: uint64
            NegHi: uint64
            NegMaxPos: int
        }

    [<NoComparison; NoEquality>]
    type private DepAccum =
        {
            mutable HasPos: bool
            mutable NegLo: uint64
            mutable NegHi: uint64
            mutable NegMaxPos: int
            mutable HistoryAbort: bool
            mutable HistoryExternal: bool
        }

    [<Struct; NoComparison; NoEquality>]
    type private OverrideEntry =
        {
            Defined: bool
            Pos: int
            MaxPos: int
            Depth: int
            Guard: GuardNode
        }

    [<Struct; NoComparison; NoEquality>]
    type private OverrideHistoryCached =
        {
            MaxEntryPos: int
            HitExternal: bool
            Outcome: ValueOption<bool>
            HasPos: bool
            NegLo: uint64
            NegHi: uint64
            NegMaxPos: int
        }

    [<Struct; NoComparison; NoEquality>]
    type private OverrideHistoryDep =
        {
            MaxEntryPos: int
            HitExternal: bool
            Dep: DepCacheEntry
        }

    let private historyListRefComparer =
        { new IEqualityComparer<OverrideEntry list> with
            member _.Equals(a, b) = obj.ReferenceEquals(a, b)

            member _.GetHashCode(l) =
                if isNull (box l) then
                    0
                else
                    System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode l
        }

    [<AllowNullLiteral; NoComparison; NoEquality>]
    type private ConstScopeCache() =
        let guards = Dictionary<GuardNode, ValueOption<bool>>(guardNodeRefComparer)

        let histories =
            Dictionary<OverrideEntry list, struct (int * ValueOption<bool>)>(historyListRefComparer)

        member _.Guards = guards
        member _.Histories = histories

    [<AllowNullLiteral; NoComparison; NoEquality>]
    type private OverrideScope() =
        let history = Dictionary<string, OverrideEntry list>(StringComparer.Ordinal)

        let windows =
            Dictionary<string, ResizeArray<struct (int * int * bool)>>(StringComparer.Ordinal)

        member _.History = history
        member _.Windows = windows
        member _.HasAny = history.Count > 0 || windows.Count > 0

        member _.AddWindow(sym: string, startPos: int, endPos: int, value: bool) =
            let ranges =
                match windows.TryGetValue sym with
                | true, r -> r
                | false, _ ->
                    let r = ResizeArray<struct (int * int * bool)>(1)
                    windows[sym] <- r
                    r

            ranges.Add(struct (startPos, endPos, value))

    [<Struct>]
    type private OverrideLookup =
        | NoOverride
        | ResolvedOverride of bool
        | UnresolvedOverride

    let private tryLookupSiblingWindow
        (overrides: OverrideScope)
        (sym: string)
        (pos: int)
        : bool voption =
        if isNull overrides || overrides.Windows.Count = 0 then
            ValueNone
        else
            match overrides.Windows.TryGetValue sym with
            | false, _ -> ValueNone
            | true, ranges ->
                let n = ranges.Count

                if n = 0 then
                    ValueNone
                elif n <= 8 then
                    let mutable i = 0
                    let mutable found = ValueNone

                    while found.IsNone && i < n do
                        let struct (s, e, v) = ranges[i]

                        if pos >= s && pos < e then found <- ValueSome v
                        elif pos < s then i <- n
                        else i <- i + 1

                    found
                else
                    let mutable lo = 0
                    let mutable hi = n - 1
                    let mutable found = ValueNone

                    while found.IsNone && lo <= hi do
                        let mid = lo + (hi - lo) / 2
                        let struct (s, e, v) = ranges[mid]

                        if pos < s then hi <- mid - 1
                        elif pos >= e then lo <- mid + 1
                        else found <- ValueSome v

                    found

    let private tryLookupUnconditionalOverride (overrides: OverrideScope) (sym: string) (pos: int) =
        if isNull overrides || not overrides.HasAny then
            NoOverride
        else
            match tryLookupSiblingWindow overrides sym pos with
            | ValueSome v -> ResolvedOverride v
            | ValueNone ->
                if overrides.History.Count = 0 then
                    NoOverride
                else
                    match overrides.History.TryGetValue sym with
                    | false, _ -> NoOverride
                    | true, history ->
                        let mutable cur = history
                        let mutable result = NoOverride
                        let mutable found = false

                        while not found do
                            match cur with
                            | [] -> found <- true
                            | (entry: OverrideEntry) :: rest ->
                                if entry.Pos >= pos then
                                    cur <- rest
                                elif isNull entry.Guard || not entry.Guard.IsSealed then
                                    result <- ResolvedOverride entry.Defined
                                    found <- true
                                else
                                    result <- UnresolvedOverride
                                    found <- true

                        result

    [<NoComparison; NoEquality>]
    type private EvalTask =
        | EvalExpr of ExpressionSyntax
        | EvalUnaryNot
        | EvalBinShortCircuit of bool * ExpressionSyntax
        | EvalUnknownShortCircuit of bool
        | EvalCmpRight of bool * ExpressionSyntax
        | EvalCmpFinish of bool
        | EvalGuardNode of GuardNode * bool
        | EvalGuardArray of GuardNode * bool * int * bool * bool
        | EvalFinishParentGuard
        | EvalFinishOverrideEntry of string * int * OverrideEntry * OverrideEntry list * bool
        | EvalEndOverrideHistory of string * int * OverrideEntry list

    let rec private tryEvalConditionFast
        (overrides: OverrideScope)
        (defined: Set<string>)
        (unknownExternal: bool)
        (depth: int)
        (expr: ExpressionSyntax)
        : ValueOption<ValueOption<bool>> =
        if isNull (box expr) then
            ValueSome(ValueSome false)
        elif depth >= 64 then
            ValueNone
        else
            match expr with
            | :? ParenthesizedExpressionSyntax as paren ->
                if isNull (box paren.Expression) then
                    ValueSome(ValueSome false)
                else
                    tryEvalConditionFast
                        overrides
                        defined
                        unknownExternal
                        (depth + 1)
                        paren.Expression
            | :? IdentifierNameSyntax as ident ->
                let sym = preprocessorSymbolName ident.Identifier

                if String.IsNullOrEmpty sym then
                    ValueSome(ValueSome false)
                else
                    match tryLookupUnconditionalOverride overrides sym ident.SpanStart with
                    | ResolvedOverride ov -> ValueSome(ValueSome ov)
                    | NoOverride ->
                        ValueSome(
                            if unknownExternal then
                                ValueNone
                            else
                                ValueSome(defined.Contains sym)
                        )
                    | UnresolvedOverride -> ValueNone
            | :? LiteralExpressionSyntax as literal ->
                ValueSome(ValueSome(literal.IsKind SyntaxKind.TrueLiteralExpression))
            | :? PrefixUnaryExpressionSyntax as unary when
                unary.IsKind SyntaxKind.LogicalNotExpression
                ->
                if isNull (box unary.Operand) then
                    ValueSome(ValueSome true)
                else
                    match
                        tryEvalConditionFast
                            overrides
                            defined
                            unknownExternal
                            (depth + 1)
                            unary.Operand
                    with
                    | ValueSome(ValueSome v) -> ValueSome(ValueSome(not v))
                    | ValueSome ValueNone -> ValueSome ValueNone
                    | ValueNone -> ValueNone
            | :? BinaryExpressionSyntax as binary ->
                match binary.Kind() with
                | SyntaxKind.LogicalAndExpression ->
                    match
                        tryEvalConditionFast
                            overrides
                            defined
                            unknownExternal
                            (depth + 1)
                            binary.Left
                    with
                    | ValueNone -> ValueNone
                    | ValueSome(ValueSome false) -> ValueSome(ValueSome false)
                    | ValueSome(ValueSome true) ->
                        if isNull (box binary.Right) then
                            ValueSome(ValueSome false)
                        else
                            tryEvalConditionFast
                                overrides
                                defined
                                unknownExternal
                                (depth + 1)
                                binary.Right
                    | ValueSome ValueNone ->
                        if isNull (box binary.Right) then
                            ValueSome(ValueSome false)
                        else
                            match
                                tryEvalConditionFast
                                    overrides
                                    defined
                                    unknownExternal
                                    (depth + 1)
                                    binary.Right
                            with
                            | ValueNone -> ValueNone
                            | ValueSome(ValueSome false) -> ValueSome(ValueSome false)
                            | ValueSome _ -> ValueSome ValueNone
                | SyntaxKind.LogicalOrExpression ->
                    match
                        tryEvalConditionFast
                            overrides
                            defined
                            unknownExternal
                            (depth + 1)
                            binary.Left
                    with
                    | ValueNone -> ValueNone
                    | ValueSome(ValueSome true) -> ValueSome(ValueSome true)
                    | ValueSome(ValueSome false) ->
                        if isNull (box binary.Right) then
                            ValueSome(ValueSome false)
                        else
                            tryEvalConditionFast
                                overrides
                                defined
                                unknownExternal
                                (depth + 1)
                                binary.Right
                    | ValueSome ValueNone ->
                        if isNull (box binary.Right) then
                            ValueSome ValueNone
                        else
                            match
                                tryEvalConditionFast
                                    overrides
                                    defined
                                    unknownExternal
                                    (depth + 1)
                                    binary.Right
                            with
                            | ValueNone -> ValueNone
                            | ValueSome(ValueSome true) -> ValueSome(ValueSome true)
                            | ValueSome _ -> ValueSome ValueNone
                | SyntaxKind.EqualsExpression ->
                    match
                        tryEvalConditionFast
                            overrides
                            defined
                            unknownExternal
                            (depth + 1)
                            binary.Left
                    with
                    | ValueNone -> ValueNone
                    | ValueSome ValueNone -> ValueSome ValueNone
                    | ValueSome(ValueSome l) ->
                        match
                            tryEvalConditionFast
                                overrides
                                defined
                                unknownExternal
                                (depth + 1)
                                binary.Right
                        with
                        | ValueNone -> ValueNone
                        | ValueSome ValueNone -> ValueSome ValueNone
                        | ValueSome(ValueSome r) -> ValueSome(ValueSome(l = r))
                | SyntaxKind.NotEqualsExpression ->
                    match
                        tryEvalConditionFast
                            overrides
                            defined
                            unknownExternal
                            (depth + 1)
                            binary.Left
                    with
                    | ValueNone -> ValueNone
                    | ValueSome ValueNone -> ValueSome ValueNone
                    | ValueSome(ValueSome l) ->
                        match
                            tryEvalConditionFast
                                overrides
                                defined
                                unknownExternal
                                (depth + 1)
                                binary.Right
                        with
                        | ValueNone -> ValueNone
                        | ValueSome ValueNone -> ValueSome ValueNone
                        | ValueSome(ValueSome r) -> ValueSome(ValueSome(l <> r))
                | _ -> ValueSome(ValueSome false)
            | _ -> ValueSome(ValueSome false)

    [<AllowNullLiteral; NoComparison; NoEquality>]
    type private EnvGuardCacheSlot() =
        let cache = Dictionary<GuardNode, GuardEvalCached>(guardNodeRefComparer)

        let historyCache =
            Dictionary<OverrideEntry list, OverrideHistoryCached>(historyListRefComparer)

        member val Defined: Set<string> = Set.empty with get, set
        member val MaskLo: uint64 = 0UL with get, set
        member val MaskHi: uint64 = 0UL with get, set
        member val MinFirstPos: int = -1 with get, set
        member val LastPosDef: Set<string> = Unchecked.defaultof<Set<string>> with get, set
        member val DiffLo: uint64 = 0UL with get, set
        member val DiffHi: uint64 = 0UL with get, set
        member val DiffMinFirstPos: int = -1 with get, set
        member _.Cache = cache
        member _.HistoryCache = historyCache

    [<AllowNullLiteral; NoComparison; NoEquality>]
    type private EnvGuardCacheRing(firstSymbolPos: Dictionary<string, int>) =
        let capacity = 16
        let slots = Array.zeroCreate<EnvGuardCacheSlot> capacity
        let mutable count = 0
        let mutable nextEvict = 0
        let mutable lastDefined = Unchecked.defaultof<Set<string>>
        let mutable lastSlot: EnvGuardCacheSlot = null
        let depCache = Dictionary<GuardNode, DepCacheEntry>(guardNodeRefComparer)

        let historyDepCache =
            Dictionary<OverrideEntry list, OverrideHistoryDep>(historyListRefComparer)

        let computeSetProfile (hasExclude: bool) (exclude: Set<string>) (defined: Set<string>) =
            if defined.IsEmpty then
                struct (0UL, 0UL, Int32.MaxValue)
            else
                let mutable lo = 0UL
                let mutable hi = 0UL

                let mutable minPos = if isNull firstSymbolPos then -1 else Int32.MaxValue

                use e = (defined :> seq<string>).GetEnumerator()

                while e.MoveNext() do
                    let sym = e.Current

                    if not hasExclude || not (exclude.Contains sym) then
                        let h = hashSymbol64 sym
                        lo <- lo ||| (1UL <<< (int h &&& 63))
                        hi <- hi ||| (1UL <<< (int (h >>> 6) &&& 63))

                        if not (isNull firstSymbolPos) then
                            match firstSymbolPos.TryGetValue sym with
                            | true, p ->
                                if p < minPos then
                                    minPos <- p
                            | false, _ -> minPos <- -1

                if minPos = Int32.MaxValue then
                    minPos <- -1

                struct (lo, hi, minPos)

        let depMatches (slot: EnvGuardCacheSlot) (entry: DepCacheEntry) =
            if not entry.HasPos then
                (slot.MaskLo &&& entry.NegLo) = 0UL
                || (slot.MaskHi &&& entry.NegHi) = 0UL
                || slot.MinFirstPos > entry.NegMaxPos
            elif obj.ReferenceEquals(slot.Defined, entry.PosDefined) then
                true
            elif entry.PosDefined.IsSubsetOf slot.Defined then
                let struct (dLo, dHi, dMinPos) =
                    if obj.ReferenceEquals(slot.LastPosDef, entry.PosDefined) then
                        struct (slot.DiffLo, slot.DiffHi, slot.DiffMinFirstPos)
                    else
                        let struct (lo, hi, minPos) =
                            computeSetProfile true entry.PosDefined slot.Defined

                        slot.LastPosDef <- entry.PosDefined
                        slot.DiffLo <- lo
                        slot.DiffHi <- hi
                        slot.DiffMinFirstPos <- minPos
                        struct (lo, hi, minPos)

                (dLo &&& entry.NegLo) = 0UL
                || (dHi &&& entry.NegHi) = 0UL
                || dMinPos > entry.NegMaxPos
            else
                false

        member _.GetSlot(defined: Set<string>) : EnvGuardCacheSlot =
            if not (isNull lastSlot) && obj.ReferenceEquals(defined, lastDefined) then
                lastSlot
            else
                let mutable found: EnvGuardCacheSlot = null
                let mutable i = 0

                while isNull found && i < count do
                    let slot = slots[i]

                    if obj.ReferenceEquals(defined, slot.Defined) || defined = slot.Defined then
                        found <- slot

                    i <- i + 1

                if isNull found then
                    let struct (lo, hi, minPos) = computeSetProfile false Set.empty defined

                    let slot =
                        if count < capacity then
                            let s = EnvGuardCacheSlot()
                            s.Defined <- defined
                            s.MaskLo <- lo
                            s.MaskHi <- hi
                            s.MinFirstPos <- minPos
                            slots[count] <- s
                            count <- count + 1
                            s
                        else
                            let idx = nextEvict
                            nextEvict <- (nextEvict + 1) % capacity
                            let s = slots[idx]
                            s.Defined <- defined
                            s.MaskLo <- lo
                            s.MaskHi <- hi
                            s.MinFirstPos <- minPos
                            s.LastPosDef <- Unchecked.defaultof<Set<string>>
                            s.DiffLo <- 0UL
                            s.DiffHi <- 0UL
                            s.DiffMinFirstPos <- -1
                            s.Cache.Clear()
                            s.HistoryCache.Clear()
                            s

                    lastDefined <- defined
                    lastSlot <- slot
                    slot
                else
                    lastDefined <- defined
                    lastSlot <- found
                    found

        member _.RecordDep
            (
                gNode: GuardNode,
                result: ValueOption<bool>,
                hasPos: bool,
                defined: Set<string>,
                negLo: uint64,
                negHi: uint64,
                negMaxPos: int
            ) =
            let storeNew () =
                depCache[gNode] <-
                    {
                        Result = result
                        HasPos = hasPos
                        PosDefined = if hasPos then defined else Set.empty
                        NegLo = negLo
                        NegHi = negHi
                        NegMaxPos = negMaxPos
                    }

            match depCache.TryGetValue gNode with
            | false, _ -> storeNew ()
            | true, existing ->
                if existing.HasPos && (not hasPos || defined.Count < existing.PosDefined.Count) then
                    storeNew ()

        member _.TryMatchDep
            (gNode: GuardNode, slot: EnvGuardCacheSlot, matched: byref<DepCacheEntry>)
            =
            match depCache.TryGetValue gNode with
            | false, _ -> false
            | true, entry ->
                if depMatches slot entry then
                    matched <- entry
                    true
                else
                    false

        member _.RecordHistoryDep
            (
                history: OverrideEntry list,
                maxEntryPos: int,
                hitExternal: bool,
                result: ValueOption<bool>,
                hasPos: bool,
                defined: Set<string>,
                negLo: uint64,
                negHi: uint64,
                negMaxPos: int
            ) =
            let storeNew () =
                historyDepCache[history] <-
                    {
                        MaxEntryPos = maxEntryPos
                        HitExternal = hitExternal
                        Dep =
                            {
                                Result = result
                                HasPos = hasPos
                                PosDefined = if hasPos then defined else Set.empty
                                NegLo = negLo
                                NegHi = negHi
                                NegMaxPos = negMaxPos
                            }
                    }

            match historyDepCache.TryGetValue history with
            | false, _ -> storeNew ()
            | true, existing ->
                if
                    existing.Dep.HasPos
                    && (not hasPos || defined.Count < existing.Dep.PosDefined.Count)
                then
                    storeNew ()

        member _.TryMatchHistoryDep
            (
                history: OverrideEntry list,
                pos: int,
                slot: EnvGuardCacheSlot,
                matched: byref<OverrideHistoryDep>
            ) =
            match historyDepCache.TryGetValue history with
            | false, _ -> false
            | true, entry when entry.MaxEntryPos < pos && depMatches slot entry.Dep ->
                matched <- entry
                true
            | _ -> false

    let private evalConditionIterative
        (overrides: OverrideScope)
        (defined: Set<string>)
        (unknownExternal: bool)
        (constGuardCache: ConstScopeCache)
        (envSlot: EnvGuardCacheSlot)
        (envRing: EnvGuardCacheRing)
        (rootExpr: ExpressionSyntax)
        =
        let tasks = Stack<EvalTask>()
        let results = Stack<ValueOption<bool>>()
        let trackEnvDeps = not unknownExternal && not (isNull envSlot)
        let depStack = if trackEnvDeps then ResizeArray<DepAccum>() else null

        let constAbortStack =
            if not trackEnvDeps && not (isNull constGuardCache) then
                ResizeArray<bool>()
            else
                null

        let inline markHistoryAbort () =
            if not (isNull depStack) && depStack.Count > 0 then
                depStack[depStack.Count - 1].HistoryAbort <- true
            elif not (isNull constAbortStack) && constAbortStack.Count > 0 then
                constAbortStack[constAbortStack.Count - 1] <- true

        let inline mergeDep hasPos negLo negHi negMaxPos =
            if not (isNull depStack) && depStack.Count > 0 then
                let parent = depStack[depStack.Count - 1]

                if hasPos then
                    parent.HasPos <- true

                parent.NegLo <- parent.NegLo ||| negLo
                parent.NegHi <- parent.NegHi ||| negHi

                if negMaxPos > parent.NegMaxPos then
                    parent.NegMaxPos <- negMaxPos

        let evalExternalSymbol (sym: string) (symPos: int) =
            if unknownExternal then
                ValueNone
            else
                let isDef = defined.Contains sym

                if not (isNull depStack) && depStack.Count > 0 then
                    let cur = depStack[depStack.Count - 1]

                    if isDef then
                        cur.HasPos <- true
                    else
                        let h = hashSymbol64 sym
                        cur.NegLo <- cur.NegLo ||| (1UL <<< (int h &&& 63))
                        cur.NegHi <- cur.NegHi ||| (1UL <<< (int (h >>> 6) &&& 63))

                        if symPos > cur.NegMaxPos then
                            cur.NegMaxPos <- symPos

                ValueSome isDef

        let tryHitHistoryCache
            (sym: string)
            (pos: int)
            (cur: OverrideEntry list)
            (inHistoryFrame: bool)
            =
            match cur with
            | [] -> false
            | h :: _ when h.MaxPos >= pos -> false
            | _ ->
                if trackEnvDeps then
                    let mutable slotCached = Unchecked.defaultof<OverrideHistoryCached>

                    if
                        envSlot.HistoryCache.TryGetValue(cur, &slotCached)
                        && slotCached.MaxEntryPos < pos
                    then
                        mergeDep
                            slotCached.HasPos
                            slotCached.NegLo
                            slotCached.NegHi
                            slotCached.NegMaxPos

                        if slotCached.HitExternal then
                            if inHistoryFrame then
                                depStack[depStack.Count - 1].HistoryExternal <- true
                            else
                                results.Push(evalExternalSymbol sym pos)
                        else
                            results.Push slotCached.Outcome

                        true
                    else
                        let mutable depCached = Unchecked.defaultof<OverrideHistoryDep>

                        if
                            not (isNull envRing)
                            && envRing.TryMatchHistoryDep(cur, pos, envSlot, &depCached)
                        then
                            envSlot.HistoryCache[cur] <-
                                {
                                    MaxEntryPos = depCached.MaxEntryPos
                                    HitExternal = depCached.HitExternal
                                    Outcome = depCached.Dep.Result
                                    HasPos = depCached.Dep.HasPos
                                    NegLo = depCached.Dep.NegLo
                                    NegHi = depCached.Dep.NegHi
                                    NegMaxPos = depCached.Dep.NegMaxPos
                                }

                            mergeDep
                                depCached.Dep.HasPos
                                depCached.Dep.NegLo
                                depCached.Dep.NegHi
                                depCached.Dep.NegMaxPos

                            if depCached.HitExternal then
                                if inHistoryFrame then
                                    depStack[depStack.Count - 1].HistoryExternal <- true
                                else
                                    results.Push(evalExternalSymbol sym pos)
                            else
                                results.Push depCached.Dep.Result

                            true
                        else
                            false
                elif not (isNull constGuardCache) then
                    match constGuardCache.Histories.TryGetValue cur with
                    | true, struct (maxEntryPos, outcome) when maxEntryPos < pos ->
                        results.Push outcome
                        true
                    | _ -> false
                else
                    false

        let pushOverrideEval
            (sym: string)
            (pos: int)
            (initialItems: OverrideEntry list)
            (inHistoryFrame: bool)
            =
            let mutable cur = initialItems
            let mutable doneLoop = false

            while not doneLoop do
                match cur with
                | [] ->
                    if inHistoryFrame && trackEnvDeps then
                        depStack[depStack.Count - 1].HistoryExternal <- true
                    else
                        results.Push(evalExternalSymbol sym pos)

                    doneLoop <- true
                | entry :: rest ->
                    if tryHitHistoryCache sym pos cur inHistoryFrame then
                        doneLoop <- true
                    elif entry.Pos >= pos then
                        cur <- rest
                    elif isNull entry.Guard || not entry.Guard.IsSealed then
                        if inHistoryFrame && not (isNull entry.Guard) then
                            markHistoryAbort ()

                        results.Push(ValueSome entry.Defined)
                        doneLoop <- true
                    elif trackEnvDeps then
                        match envSlot.Cache.TryGetValue entry.Guard with
                        | true, cached ->
                            mergeDep cached.HasPos cached.NegLo cached.NegHi cached.NegMaxPos

                            match cached.Result with
                            | ValueSome true ->
                                results.Push(ValueSome entry.Defined)
                                doneLoop <- true
                            | ValueSome false -> cur <- rest
                            | ValueNone ->
                                results.Push ValueNone
                                doneLoop <- true
                        | false, _ ->
                            let mutable depEntry = Unchecked.defaultof<DepCacheEntry>

                            if
                                not (isNull envRing)
                                && envRing.TryMatchDep(entry.Guard, envSlot, &depEntry)
                            then
                                envSlot.Cache[entry.Guard] <-
                                    {
                                        Result = depEntry.Result
                                        HasPos = depEntry.HasPos
                                        NegLo = depEntry.NegLo
                                        NegHi = depEntry.NegHi
                                        NegMaxPos = depEntry.NegMaxPos
                                    }

                                mergeDep
                                    depEntry.HasPos
                                    depEntry.NegLo
                                    depEntry.NegHi
                                    depEntry.NegMaxPos

                                match depEntry.Result with
                                | ValueSome true ->
                                    results.Push(ValueSome entry.Defined)
                                    doneLoop <- true
                                | ValueSome false -> cur <- rest
                                | ValueNone ->
                                    results.Push ValueNone
                                    doneLoop <- true
                            else
                                tasks.Push(
                                    EvalFinishOverrideEntry(sym, pos, entry, rest, inHistoryFrame)
                                )

                                tasks.Push(EvalGuardNode(entry.Guard, false))
                                doneLoop <- true
                    elif isNull constGuardCache then
                        tasks.Push(EvalFinishOverrideEntry(sym, pos, entry, rest, inHistoryFrame))
                        tasks.Push(EvalGuardNode(entry.Guard, false))
                        doneLoop <- true
                    else
                        match constGuardCache.Guards.TryGetValue entry.Guard with
                        | true, ValueSome true ->
                            results.Push(ValueSome entry.Defined)
                            doneLoop <- true
                        | true, ValueSome false -> cur <- rest
                        | true, ValueNone ->
                            results.Push ValueNone
                            doneLoop <- true
                        | false, _ ->
                            tasks.Push(
                                EvalFinishOverrideEntry(sym, pos, entry, rest, inHistoryFrame)
                            )

                            tasks.Push(EvalGuardNode(entry.Guard, false))
                            doneLoop <- true

        let evalHistoryStart (sym: string) (pos: int) (history: OverrideEntry list) =
            let mutable cur = history
            let mutable skipping = true

            while skipping do
                match cur with
                | entry :: rest when entry.Pos >= pos -> cur <- rest
                | _ -> skipping <- false

            match cur with
            | [] -> results.Push(evalExternalSymbol sym pos)
            | h :: _ ->
                if tryHitHistoryCache sym pos cur false then
                    ()
                elif
                    h.MaxPos < pos
                    && (trackEnvDeps || not (isNull constGuardCache))
                    && (isNull h.Guard || h.Guard.IsSealed)
                then
                    if trackEnvDeps then
                        depStack.Add
                            {
                                HasPos = false
                                NegLo = 0UL
                                NegHi = 0UL
                                NegMaxPos = -1
                                HistoryAbort = false
                                HistoryExternal = false
                            }
                    else
                        constAbortStack.Add false

                    tasks.Push(EvalEndOverrideHistory(sym, pos, cur))
                    pushOverrideEval sym pos cur true
                else
                    pushOverrideEval sym pos cur false

        tasks.Push(EvalExpr rootExpr)

        while tasks.Count > 0 do
            match tasks.Pop() with
            | EvalExpr node ->
                if isNull (box node) then
                    results.Push(ValueSome false)
                else
                    match node with
                    | :? ParenthesizedExpressionSyntax as paren ->
                        tasks.Push(EvalExpr paren.Expression)
                    | :? IdentifierNameSyntax as ident ->
                        let sym = preprocessorSymbolName ident.Identifier

                        if String.IsNullOrEmpty sym then
                            results.Push(ValueSome false)
                        elif isNull overrides || not overrides.HasAny then
                            results.Push(evalExternalSymbol sym ident.SpanStart)
                        else
                            match tryLookupSiblingWindow overrides sym ident.SpanStart with
                            | ValueSome v -> results.Push(ValueSome v)
                            | ValueNone ->
                                if overrides.History.Count = 0 then
                                    results.Push(evalExternalSymbol sym ident.SpanStart)
                                else
                                    match overrides.History.TryGetValue sym with
                                    | false, _ ->
                                        results.Push(evalExternalSymbol sym ident.SpanStart)
                                    | true, history -> evalHistoryStart sym ident.SpanStart history
                    | :? LiteralExpressionSyntax as literal ->
                        results.Push(ValueSome(literal.IsKind SyntaxKind.TrueLiteralExpression))
                    | :? PrefixUnaryExpressionSyntax as unary when
                        unary.IsKind SyntaxKind.LogicalNotExpression
                        ->
                        if isNull (box unary.Operand) then
                            results.Push(ValueSome true)
                        else
                            tasks.Push EvalUnaryNot
                            tasks.Push(EvalExpr unary.Operand)
                    | :? BinaryExpressionSyntax as binary ->
                        match binary.Kind() with
                        | SyntaxKind.LogicalAndExpression ->
                            tasks.Push(EvalBinShortCircuit(true, binary.Right))
                            tasks.Push(EvalExpr binary.Left)
                        | SyntaxKind.LogicalOrExpression ->
                            tasks.Push(EvalBinShortCircuit(false, binary.Right))
                            tasks.Push(EvalExpr binary.Left)
                        | SyntaxKind.EqualsExpression ->
                            tasks.Push(EvalCmpRight(true, binary.Right))
                            tasks.Push(EvalExpr binary.Left)
                        | SyntaxKind.NotEqualsExpression ->
                            tasks.Push(EvalCmpRight(false, binary.Right))
                            tasks.Push(EvalExpr binary.Left)
                        | _ -> results.Push(ValueSome false)
                    | _ -> results.Push(ValueSome false)
            | EvalUnaryNot ->
                match results.Pop() with
                | ValueSome v -> results.Push(ValueSome(not v))
                | ValueNone -> results.Push ValueNone
            | EvalBinShortCircuit(isAnd, rightExpr) ->
                match results.Pop() with
                | ValueSome leftVal ->
                    if isAnd then
                        if not leftVal then
                            results.Push(ValueSome false)
                        elif isNull (box rightExpr) then
                            results.Push(ValueSome false)
                        else
                            tasks.Push(EvalExpr rightExpr)
                    elif leftVal then
                        results.Push(ValueSome true)
                    elif isNull (box rightExpr) then
                        results.Push(ValueSome false)
                    else
                        tasks.Push(EvalExpr rightExpr)
                | ValueNone ->
                    if isAnd then
                        if isNull (box rightExpr) then
                            results.Push(ValueSome false)
                        else
                            tasks.Push(EvalUnknownShortCircuit true)
                            tasks.Push(EvalExpr rightExpr)
                    elif isNull (box rightExpr) then
                        results.Push ValueNone
                    else
                        tasks.Push(EvalUnknownShortCircuit false)
                        tasks.Push(EvalExpr rightExpr)
            | EvalUnknownShortCircuit isAnd ->
                match results.Pop() with
                | ValueSome v when v = not isAnd -> results.Push(ValueSome v)
                | _ -> results.Push ValueNone
            | EvalCmpRight(isEq, rightExpr) ->
                match results.Pop() with
                | ValueNone -> results.Push ValueNone
                | ValueSome l ->
                    if isNull (box rightExpr) then
                        results.Push(ValueSome(if isEq then not l else l))
                    else
                        results.Push(ValueSome l)
                        tasks.Push(EvalCmpFinish isEq)
                        tasks.Push(EvalExpr rightExpr)
            | EvalCmpFinish isEq ->
                let r = results.Pop()
                let l = results.Pop()

                match l, r with
                | ValueSome lv, ValueSome rv ->
                    results.Push(ValueSome(if isEq then lv = rv else lv <> rv))
                | _ -> results.Push ValueNone
            | EvalGuardNode(gNode, ready) ->
                if isNull gNode || not gNode.IsSealed then
                    results.Push(ValueSome true)
                elif ready then
                    let ok = results.Peek()

                    if trackEnvDeps then
                        let idx = depStack.Count - 1
                        let acc = depStack[idx]
                        depStack.RemoveAt idx

                        envSlot.Cache[gNode] <-
                            {
                                Result = ok
                                HasPos = acc.HasPos
                                NegLo = acc.NegLo
                                NegHi = acc.NegHi
                                NegMaxPos = acc.NegMaxPos
                            }

                        if not (isNull envRing) then
                            envRing.RecordDep(
                                gNode,
                                ok,
                                acc.HasPos,
                                defined,
                                acc.NegLo,
                                acc.NegHi,
                                acc.NegMaxPos
                            )

                        mergeDep acc.HasPos acc.NegLo acc.NegHi acc.NegMaxPos
                    elif not (isNull constGuardCache) then
                        constGuardCache.Guards[gNode] <- ok
                elif trackEnvDeps then
                    match envSlot.Cache.TryGetValue gNode with
                    | true, cached ->
                        mergeDep cached.HasPos cached.NegLo cached.NegHi cached.NegMaxPos
                        results.Push cached.Result
                    | false, _ ->
                        let mutable depEntry = Unchecked.defaultof<DepCacheEntry>

                        if
                            not (isNull envRing) && envRing.TryMatchDep(gNode, envSlot, &depEntry)
                        then
                            envSlot.Cache[gNode] <-
                                {
                                    Result = depEntry.Result
                                    HasPos = depEntry.HasPos
                                    NegLo = depEntry.NegLo
                                    NegHi = depEntry.NegHi
                                    NegMaxPos = depEntry.NegMaxPos
                                }

                            mergeDep
                                depEntry.HasPos
                                depEntry.NegLo
                                depEntry.NegHi
                                depEntry.NegMaxPos

                            results.Push depEntry.Result
                        else
                            depStack.Add
                                {
                                    HasPos = false
                                    NegLo = 0UL
                                    NegHi = 0UL
                                    NegMaxPos = -1
                                    HistoryAbort = false
                                    HistoryExternal = false
                                }

                            tasks.Push(EvalGuardNode(gNode, true))
                            tasks.Push(EvalGuardArray(gNode, false, 0, false, false))
                elif isNull constGuardCache then
                    tasks.Push(EvalGuardNode(gNode, true))
                    tasks.Push(EvalGuardArray(gNode, false, 0, false, false))
                else
                    match constGuardCache.Guards.TryGetValue gNode with
                    | true, cached -> results.Push cached
                    | false, _ ->
                        tasks.Push(EvalGuardNode(gNode, true))
                        tasks.Push(EvalGuardArray(gNode, false, 0, false, false))
            | EvalGuardArray(gNode, isFalseArray, idx, awaitingResult, hasUnknown) ->
                let mutable keepGoing = true
                let mutable nextIdx = idx
                let mutable unknownSoFar = hasUnknown

                if awaitingResult then
                    match results.Pop() with
                    | ValueSome v ->
                        let ok = if isFalseArray then not v else v

                        if not ok then
                            results.Push(ValueSome false)
                            keepGoing <- false
                        else
                            nextIdx <- idx + 1
                    | ValueNone ->
                        nextIdx <- idx + 1
                        unknownSoFar <- true

                if keepGoing then
                    let arr = if isFalseArray then gNode.GuardFalse else gNode.GuardTrue

                    if nextIdx < arr.Length then
                        tasks.Push(EvalGuardArray(gNode, isFalseArray, nextIdx, true, unknownSoFar))

                        tasks.Push(EvalExpr arr[nextIdx])
                    elif not isFalseArray then
                        tasks.Push(EvalGuardArray(gNode, true, 0, false, unknownSoFar))
                    elif isNull gNode.Parent || not gNode.Parent.IsSealed then
                        results.Push(if unknownSoFar then ValueNone else ValueSome true)
                    else
                        if unknownSoFar then
                            tasks.Push EvalFinishParentGuard

                        tasks.Push(EvalGuardNode(gNode.Parent, false))
            | EvalFinishParentGuard ->
                match results.Pop() with
                | ValueSome false -> results.Push(ValueSome false)
                | _ -> results.Push ValueNone
            | EvalFinishOverrideEntry(sym, pos, entry, rest, inHistoryFrame) ->
                match results.Pop() with
                | ValueSome true -> results.Push(ValueSome entry.Defined)
                | ValueSome false -> pushOverrideEval sym pos rest inHistoryFrame
                | ValueNone -> results.Push ValueNone
            | EvalEndOverrideHistory(sym, pos, startCur) ->
                let maxPos =
                    match startCur with
                    | [] -> -1
                    | h :: _ -> h.MaxPos

                if trackEnvDeps then
                    let idx = depStack.Count - 1
                    let acc = depStack[idx]
                    depStack.RemoveAt idx
                    let isExt = acc.HistoryExternal
                    let outcome = if isExt then ValueNone else results.Peek()

                    if not acc.HistoryAbort && not (List.isEmpty startCur) then
                        envSlot.HistoryCache[startCur] <-
                            {
                                MaxEntryPos = maxPos
                                HitExternal = isExt
                                Outcome = outcome
                                HasPos = acc.HasPos
                                NegLo = acc.NegLo
                                NegHi = acc.NegHi
                                NegMaxPos = acc.NegMaxPos
                            }

                        if not (isNull envRing) then
                            envRing.RecordHistoryDep(
                                startCur,
                                maxPos,
                                isExt,
                                outcome,
                                acc.HasPos,
                                defined,
                                acc.NegLo,
                                acc.NegHi,
                                acc.NegMaxPos
                            )

                    mergeDep acc.HasPos acc.NegLo acc.NegHi acc.NegMaxPos

                    if isExt then
                        results.Push(evalExternalSymbol sym pos)
                elif not (isNull constGuardCache) then
                    let idx = constAbortStack.Count - 1
                    let aborted = constAbortStack[idx]
                    constAbortStack.RemoveAt idx

                    if not aborted && not (List.isEmpty startCur) then
                        constGuardCache.Histories[startCur] <- struct (maxPos, results.Peek())

        results.Pop()

    let private tryConstEvalCondition
        (overrides: OverrideScope)
        (constGuardCache: ConstScopeCache)
        (expr: ExpressionSyntax)
        =
        match tryEvalConditionFast overrides Set.empty true 0 expr with
        | ValueSome v -> v
        | ValueNone ->
            evalConditionIterative overrides Set.empty true constGuardCache null null expr

    let private evalCondition
        (overrides: OverrideScope)
        (guardCaches: EnvGuardCacheRing)
        (defined: Set<string>)
        (expr: ExpressionSyntax)
        =
        let res =
            match tryEvalConditionFast overrides defined false 0 expr with
            | ValueSome v -> v
            | ValueNone ->
                let slot =
                    if isNull guardCaches then
                        null
                    else
                        guardCaches.GetSlot defined

                evalConditionIterative overrides defined false null slot guardCaches expr

        match res with
        | ValueSome v -> v
        | ValueNone -> false

    let private combineWitnessSets
        (ls: Set<string>)
        (lHash: uint64)
        (rs: Set<string>)
        (rHash: uint64)
        =
        let inline foldSmaller larger largerHash smaller =
            Set.fold
                (fun struct (acc, h) item ->
                    if Set.contains item acc then
                        struct (acc, h)
                    else
                        struct (Set.add item acc, h ^^^ hashSymbol64 item))
                struct (larger, largerHash)
                smaller

        if ls.Count >= rs.Count then
            foldSmaller ls lHash rs
        else
            foldSmaller rs rHash ls

    [<NoComparison; NoEquality>]
    type private WitnessShape =
        | Empty
        | One of string
        | Join of WitnessNode * WitnessNode

    and [<NoComparison; NoEquality>] private WitnessNode(shape: WitnessShape) as this =
        let mutable cached: Set<string> option = None
        let mutable cachedHash64 = 0UL
        member _.Shape = shape

        member internal _.Cached = cached
        member internal _.CachedHash64 = cachedHash64

        member internal _.SetCached(s, h) =
            cached <- Some s
            cachedHash64 <- h

        member internal _.CachedValue: Set<string> = Option.defaultValue Set.empty cached

        member _.ToSet() =
            match cached with
            | Some s -> s
            | None ->
                match shape with
                | Empty ->
                    cached <- Some Set.empty
                    cachedHash64 <- 0UL
                    Set.empty
                | One sym ->
                    let s = Set.singleton sym
                    cached <- Some s
                    cachedHash64 <- hashSymbol64 sym
                    s
                | Join((left: WitnessNode), (right: WitnessNode)) ->
                    match left.Cached, right.Cached with
                    | Some ls, Some rs ->
                        let struct (merged, h) =
                            combineWitnessSets ls left.CachedHash64 rs right.CachedHash64

                        cached <- Some merged
                        cachedHash64 <- h
                        merged
                    | _ ->
                        let stack = Stack<struct (bool * WitnessNode)>()
                        let visited = HashSet<obj>(ReferenceEqualityComparer.Instance)
                        stack.Push(struct (false, this))

                        while stack.Count > 0 do
                            let struct (ready, cur) = stack.Pop()

                            if cur.Cached.IsNone then
                                if ready then
                                    match cur.Shape with
                                    | Join(lNode, rNode) ->
                                        let struct (merged, h) =
                                            combineWitnessSets
                                                lNode.CachedValue
                                                lNode.CachedHash64
                                                rNode.CachedValue
                                                rNode.CachedHash64

                                        cur.SetCached(merged, h)
                                    | Empty -> cur.SetCached(Set.empty, 0UL)
                                    | One sym -> cur.SetCached(Set.singleton sym, hashSymbol64 sym)
                                else
                                    match cur.Shape with
                                    | Empty -> cur.SetCached(Set.empty, 0UL)
                                    | One sym -> cur.SetCached(Set.singleton sym, hashSymbol64 sym)
                                    | Join(lNode, rNode) ->
                                        if visited.Add(box cur) then
                                            stack.Push(struct (true, cur))

                                            if rNode.Cached.IsNone then
                                                stack.Push(struct (false, rNode))

                                            if lNode.Cached.IsNone then
                                                stack.Push(struct (false, lNode))

                        Option.defaultValue Set.empty cached

    let private witnessNodeComparer =
        { new IEqualityComparer<WitnessNode> with
            member _.Equals(a, b) =
                if obj.ReferenceEquals(a, b) then
                    true
                elif isNull (box a) || isNull (box b) then
                    false
                else
                    let sa = a.ToSet()
                    let sb = b.ToSet()
                    a.CachedHash64 = b.CachedHash64 && sa = sb

            member _.GetHashCode(a) =
                if isNull (box a) then
                    0
                else
                    ignore (a.ToSet())
                    let h = a.CachedHash64
                    int (h ^^^ (h >>> 32))
        }

    let private emptyWitness = WitnessNode(Empty)

    let private joinWitness (left: WitnessNode) (right: WitnessNode) =
        match left.Shape, right.Shape with
        | Empty, _ -> right
        | _, Empty -> left
        | _ when obj.ReferenceEquals(left, right) -> left
        | _ -> WitnessNode(Join(left, right))

    let private witnessLimit = 12

    let private distinctBounded (capped: bool ref) (candidates: WitnessNode seq) =
        use e = candidates.GetEnumerator()

        if not (e.MoveNext()) then
            []
        else
            let first = e.Current

            if not (e.MoveNext()) then
                [ first ]
            else
                let second = e.Current

                if not (e.MoveNext()) then
                    if witnessNodeComparer.Equals(first, second) then
                        [ first ]
                    else
                        [ first; second ]
                else
                    let seen = HashSet<WitnessNode>(witnessNodeComparer)
                    let kept = ResizeArray<WitnessNode>(witnessLimit)
                    seen.Add first |> ignore
                    kept.Add first

                    let inline addCandidate (item: WitnessNode) =
                        if kept.Count < witnessLimit then
                            if seen.Add item then
                                kept.Add item

                            true
                        elif not (seen.Contains item) then
                            capped.Value <- true
                            false
                        else
                            true

                    if addCandidate second then
                        let mutable more = addCandidate e.Current

                        while more && e.MoveNext() do
                            more <- addCandidate e.Current

                    List.ofSeq kept

    let private combineWitnesses
        (capped: bool ref)
        (left: WitnessNode list)
        (right: WitnessNode list)
        =
        if List.isEmpty left || List.isEmpty right then
            []
        else
            seq {
                for a in left do
                    for b in right do
                        yield joinWitness a b
            }
            |> distinctBounded capped

    let private interleaveWitnesses (left: WitnessNode list) (right: WitnessNode list) =
        if List.isEmpty left then
            right :> seq<WitnessNode>
        elif List.isEmpty right then
            left :> seq<WitnessNode>
        else
            let out = ResizeArray<WitnessNode>(left.Length + right.Length)
            let mutable lCur = left
            let mutable rCur = right

            while not (List.isEmpty lCur && List.isEmpty rCur) do
                match lCur with
                | h :: t ->
                    out.Add h
                    lCur <- t
                | [] -> ()

                match rCur with
                | h :: t ->
                    out.Add h
                    rCur <- t
                | [] -> ()

            out :> seq<WitnessNode>

    let private equalWitnesses
        (capped: bool ref)
        (witnessesFn: bool -> ExpressionSyntax -> WitnessNode list)
        (same: bool)
        (left: ExpressionSyntax)
        (right: ExpressionSyntax)
        =
        if same then
            interleaveWitnesses
                (combineWitnesses capped (witnessesFn true left) (witnessesFn true right))
                (combineWitnesses capped (witnessesFn false left) (witnessesFn false right))
            |> distinctBounded capped
        else
            interleaveWitnesses
                (combineWitnesses capped (witnessesFn true left) (witnessesFn false right))
                (combineWitnesses capped (witnessesFn false left) (witnessesFn true right))
            |> distinctBounded capped

    [<Struct; NoComparison; NoEquality>]
    type private CachedWitnessResult =
        {
            Witnesses: WitnessNode list
            Capped: bool
        }

    [<Struct; NoComparison; NoEquality>]
    type private SymWalkKey =
        {
            Sym: string
            Items: OverrideEntry list
        }

    let private symWalkKeyComparer =
        { new IEqualityComparer<SymWalkKey> with
            member _.Equals(a, b) =
                obj.ReferenceEquals(a.Items, b.Items)
                && String.Equals(a.Sym, b.Sym, StringComparison.Ordinal)

            member _.GetHashCode(k) =
                let hl =
                    if isNull (box k.Items) then
                        0
                    else
                        System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode k.Items

                HashCode.Combine(StringComparer.Ordinal.GetHashCode k.Sym, hl)
        }

    [<NoComparison; NoEquality>]
    type private WitnessMemo =
        {
            True: Dictionary<obj, CachedWitnessResult>
            False: Dictionary<obj, CachedWitnessResult>
            SealedGuardHolds: Dictionary<GuardNode, CachedWitnessResult>
            SealedGuardFails: Dictionary<GuardNode, CachedWitnessResult>
            TempGuardHolds: Dictionary<GuardNode, CachedWitnessResult>
            TempGuardFails: Dictionary<GuardNode, CachedWitnessResult>
            SealedWalkTrue: Dictionary<SymWalkKey, CachedWitnessResult>
            SealedWalkFalse: Dictionary<SymWalkKey, CachedWitnessResult>
            TempWalkTrue: Dictionary<SymWalkKey, CachedWitnessResult>
            TempWalkFalse: Dictionary<SymWalkKey, CachedWitnessResult>
            mutable OverrideEpoch: int
            mutable UnforcedPeer: WitnessMemo voption
            mutable UnforcedBeforePos: int
        }

        member this.ClearTemp() =
            this.True.Clear()
            this.False.Clear()
            this.TempGuardHolds.Clear()
            this.TempGuardFails.Clear()
            this.TempWalkTrue.Clear()
            this.TempWalkFalse.Clear()

        member this.ResetAll() =
            this.ClearTemp()
            this.SealedGuardHolds.Clear()
            this.SealedGuardFails.Clear()
            this.SealedWalkTrue.Clear()
            this.SealedWalkFalse.Clear()

        static member Create() =
            {
                True = Dictionary<obj, CachedWitnessResult>(ReferenceEqualityComparer.Instance)
                False = Dictionary<obj, CachedWitnessResult>(ReferenceEqualityComparer.Instance)
                SealedGuardHolds = Dictionary<GuardNode, CachedWitnessResult>(guardNodeRefComparer)
                SealedGuardFails = Dictionary<GuardNode, CachedWitnessResult>(guardNodeRefComparer)
                TempGuardHolds = Dictionary<GuardNode, CachedWitnessResult>(guardNodeRefComparer)
                TempGuardFails = Dictionary<GuardNode, CachedWitnessResult>(guardNodeRefComparer)
                SealedWalkTrue = Dictionary<SymWalkKey, CachedWitnessResult>(symWalkKeyComparer)
                SealedWalkFalse = Dictionary<SymWalkKey, CachedWitnessResult>(symWalkKeyComparer)
                TempWalkTrue = Dictionary<SymWalkKey, CachedWitnessResult>(symWalkKeyComparer)
                TempWalkFalse = Dictionary<SymWalkKey, CachedWitnessResult>(symWalkKeyComparer)
                OverrideEpoch = 0
                UnforcedPeer = ValueNone
                UnforcedBeforePos = -1
            }

    [<NoComparison; NoEquality>]
    type private GuardHoldState =
        {
            Chain: Stack<GuardNode>
            mutable CurAcc: WitnessNode list
            mutable CurCapped: bool
            mutable NodeG: GuardNode
            mutable Phase: int
            mutable Idx: int
            mutable WaitingChild: bool
        }

    [<NoComparison; NoEquality>]
    type private GuardFailState =
        {
            Chain: Stack<GuardNode>
            mutable ParentFails: WitnessNode list
            mutable ParentCapped: bool
            mutable NodeG: GuardNode
            FailParts: ResizeArray<WitnessNode>
            mutable NodeCapped: bool
            mutable Phase: int
            mutable Idx: int
            mutable WaitingChild: bool
            mutable NeedSeed: bool
        }

    [<NoComparison; NoEquality>]
    type private WalkFrame =
        {
            Sym: string
            SpanStart: int
            Want: bool
            Cur: OverrideEntry list
            Entry: OverrideEntry
            Rest: OverrideEntry list
            mutable Stage: int
            mutable Taken: WitnessNode list
            mutable GuardFails: WitnessNode list
            mutable PrevCap: bool
        }

    [<NoComparison; NoEquality>]
    type private WitnessTask =
        | ExprStart of want: bool * expr: ExpressionSyntax
        | ExprFinishUnary of want: bool * expr: ExpressionSyntax
        | ExprFinishBinaryLeft of want: bool * bin: BinaryExpressionSyntax
        | ExprFinishBinaryRight of
            want: bool *
            bin: BinaryExpressionSyntax *
            leftRes: CachedWitnessResult
        | ExprFinishEqStep of
            want: bool *
            bin: BinaryExpressionSyntax *
            step: int *
            r0: CachedWitnessResult *
            r1: CachedWitnessResult *
            r2: CachedWitnessResult
        | ExprFinishIdent of want: bool * ident: IdentifierNameSyntax
        | RunGuardHold of GuardHoldState
        | RunGuardFail of GuardFailState
        | RunWalk of WalkFrame

    let private witnesses
        (overrides: OverrideScope)
        (forcedExternal: Dictionary<string, bool>)
        (capped: bool ref)
        (memo: WitnessMemo)
        (want: bool)
        (expr: ExpressionSyntax)
        : WitnessNode list =
        if isNull (box expr) then
            []
        else
            let tableFor w = if w then memo.True else memo.False

            let lookupWitnesses w (child: ExpressionSyntax) =
                if isNull (box child) then
                    []
                else
                    match (tableFor w).TryGetValue(box child) with
                    | true, hit -> hit.Witnesses
                    | false, _ -> []

            let emptyRes = { Witnesses = []; Capped = false }

            let singletonEmptyRes =
                {
                    Witnesses = [ emptyWitness ]
                    Capped = false
                }

            let leafWitness sym w =
                if not (isNull forcedExternal) then
                    match forcedExternal.TryGetValue sym with
                    | true, fv -> if fv = w then [ emptyWitness ] else []
                    | false, _ -> if w then [ WitnessNode(One sym) ] else [ emptyWitness ]
                elif w then
                    [ WitnessNode(One sym) ]
                else
                    [ emptyWitness ]

            let tasks = Stack<WitnessTask>()
            let mutable curResult = emptyRes
            let mutable curWalkSealed = true

            let guardHoldCache (g: GuardNode) =
                if g.IsFullySealed then
                    memo.SealedGuardHolds
                else
                    memo.TempGuardHolds

            let guardFailCache (g: GuardNode) =
                if g.IsFullySealed then
                    memo.SealedGuardFails
                else
                    memo.TempGuardFails

            let startGuardHold (topGuard: GuardNode) =
                let chain = Stack<GuardNode>()
                let mutable g = topGuard
                let mutable curAcc = [ emptyWitness ]
                let mutable curCapped = false
                let mutable searching = true

                while searching && not (isNull g) && g.IsSealed do
                    let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                    if (guardHoldCache g).TryGetValue(g, &hit) then
                        curAcc <- hit.Witnesses
                        curCapped <- hit.Capped
                        searching <- false
                    else
                        chain.Push g
                        g <- g.Parent

                if chain.Count = 0 then
                    curResult <-
                        {
                            Witnesses = curAcc
                            Capped = curCapped
                        }
                else
                    let st =
                        {
                            Chain = chain
                            CurAcc = curAcc
                            CurCapped = curCapped
                            NodeG = chain.Pop()
                            Phase = 0
                            Idx = 0
                            WaitingChild = false
                        }

                    tasks.Push(RunGuardHold st)

            let startGuardFail (topGuard: GuardNode) =
                let chain = Stack<GuardNode>()
                let mutable g = topGuard
                let mutable parentFails = []
                let mutable parentCapped = false
                let mutable searching = true

                while searching && not (isNull g) && g.IsSealed do
                    let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                    if (guardFailCache g).TryGetValue(g, &hit) then
                        parentFails <- hit.Witnesses
                        parentCapped <- hit.Capped
                        searching <- false
                    else
                        chain.Push g
                        g <- g.Parent

                if chain.Count = 0 then
                    curResult <-
                        {
                            Witnesses = parentFails
                            Capped = parentCapped
                        }
                else
                    let st =
                        {
                            Chain = chain
                            ParentFails = parentFails
                            ParentCapped = parentCapped
                            NodeG = chain.Pop()
                            FailParts = ResizeArray<WitnessNode>()
                            NodeCapped = parentCapped
                            Phase = 0
                            Idx = 0
                            WaitingChild = false
                            NeedSeed = true
                        }

                    tasks.Push(RunGuardFail st)

            let startWalk sym spanStart w items =
                let sealedWalkMap = if w then memo.SealedWalkTrue else memo.SealedWalkFalse
                let tempWalkMap = if w then memo.TempWalkTrue else memo.TempWalkFalse
                let forcedFreeOfSym = isNull forcedExternal || not (forcedExternal.ContainsKey sym)
                let mutable cur = items
                let mutable resolved = false

                while not resolved do
                    match cur with
                    | [] ->
                        curResult <-
                            {
                                Witnesses = leafWitness sym w
                                Capped = false
                            }

                        curWalkSealed <- true
                        resolved <- true
                    | (entry: OverrideEntry) :: rest ->
                        if entry.Pos >= spanStart then
                            cur <- rest
                        else
                            let wk = { Sym = sym; Items = cur }
                            let mutable cachedWalk = Unchecked.defaultof<CachedWitnessResult>

                            if
                                entry.MaxPos < spanStart
                                && (sealedWalkMap.TryGetValue(wk, &cachedWalk)
                                    || (forcedFreeOfSym
                                        && entry.MaxPos < memo.UnforcedBeforePos
                                        && match memo.UnforcedPeer with
                                           | ValueSome peer ->
                                               (if w then
                                                    peer.SealedWalkTrue
                                                else
                                                    peer.SealedWalkFalse)
                                                   .TryGetValue(wk, &cachedWalk)
                                           | ValueNone -> false))
                            then
                                curResult <- cachedWalk
                                curWalkSealed <- true
                                resolved <- true
                            elif
                                entry.MaxPos < spanStart && tempWalkMap.TryGetValue(wk, &cachedWalk)
                            then
                                curResult <- cachedWalk
                                curWalkSealed <- false
                                resolved <- true
                            elif isNull entry.Guard || not entry.Guard.IsSealed then
                                let res = if entry.Defined = w then [ emptyWitness ] else []
                                let allSealed = isNull entry.Guard
                                let cRes = { Witnesses = res; Capped = false }

                                if entry.MaxPos < spanStart then
                                    if allSealed then
                                        sealedWalkMap[wk] <- cRes
                                    else
                                        tempWalkMap[wk] <- cRes

                                curResult <- cRes
                                curWalkSealed <- allSealed
                                resolved <- true
                            else
                                let wf =
                                    {
                                        Sym = sym
                                        SpanStart = spanStart
                                        Want = w
                                        Cur = cur
                                        Entry = entry
                                        Rest = rest
                                        Stage = 0
                                        Taken = []
                                        GuardFails = []
                                        PrevCap = false
                                    }

                                if entry.Defined = w then
                                    wf.Stage <- 0
                                    tasks.Push(RunWalk wf)
                                    startGuardHold entry.Guard
                                else
                                    wf.Stage <- 1
                                    tasks.Push(RunWalk wf)
                                    startGuardFail entry.Guard

                                resolved <- true

            let startExpr w (node: ExpressionSyntax) =
                if isNull (box node) then
                    curResult <- emptyRes
                else
                    let table = tableFor w
                    let mutable cached = Unchecked.defaultof<CachedWitnessResult>

                    if table.TryGetValue(box node, &cached) then
                        curResult <- cached
                    else
                        match node with
                        | :? ParenthesizedExpressionSyntax as paren ->
                            if isNull (box paren.Expression) then
                                table[box node] <- emptyRes
                                curResult <- emptyRes
                            else
                                tasks.Push(ExprFinishUnary(w, node))
                                tasks.Push(ExprStart(w, paren.Expression))
                        | :? LiteralExpressionSyntax as literal ->
                            let res =
                                if literal.IsKind SyntaxKind.TrueLiteralExpression = w then
                                    singletonEmptyRes
                                else
                                    emptyRes

                            table[box node] <- res
                            curResult <- res
                        | :? PrefixUnaryExpressionSyntax as unary when
                            unary.IsKind SyntaxKind.LogicalNotExpression
                            ->
                            if isNull (box unary.Operand) then
                                table[box node] <- emptyRes
                                curResult <- emptyRes
                            else
                                tasks.Push(ExprFinishUnary(w, node))
                                tasks.Push(ExprStart(not w, unary.Operand))
                        | :? BinaryExpressionSyntax as binary ->
                            match binary.Kind() with
                            | SyntaxKind.LogicalAndExpression
                            | SyntaxKind.LogicalOrExpression ->
                                tasks.Push(ExprFinishBinaryLeft(w, binary))
                                tasks.Push(ExprStart(w, binary.Left))
                            | SyntaxKind.EqualsExpression
                            | SyntaxKind.NotEqualsExpression ->
                                tasks.Push(
                                    ExprFinishEqStep(w, binary, 0, emptyRes, emptyRes, emptyRes)
                                )

                                tasks.Push(ExprStart(true, binary.Left))
                            | _ ->
                                table[box node] <- emptyRes
                                curResult <- emptyRes
                        | :? IdentifierNameSyntax as ident ->
                            let sym = preprocessorSymbolName ident.Identifier

                            if String.IsNullOrEmpty sym then
                                table[box node] <- emptyRes
                                curResult <- emptyRes
                            else if isNull overrides || not overrides.HasAny then
                                let res =
                                    {
                                        Witnesses = leafWitness sym w
                                        Capped = false
                                    }

                                table[box node] <- res
                                curResult <- res
                            else
                                match tryLookupSiblingWindow overrides sym ident.SpanStart with
                                | ValueSome v ->
                                    let res = if v = w then singletonEmptyRes else emptyRes

                                    table[box node] <- res
                                    curResult <- res
                                | ValueNone ->
                                    if overrides.History.Count = 0 then
                                        let res =
                                            {
                                                Witnesses = leafWitness sym w
                                                Capped = false
                                            }

                                        table[box node] <- res
                                        curResult <- res
                                    else
                                        match overrides.History.TryGetValue sym with
                                        | false, _ ->
                                            let res =
                                                {
                                                    Witnesses = leafWitness sym w
                                                    Capped = false
                                                }

                                            table[box node] <- res
                                            curResult <- res
                                        | true, history ->
                                            tasks.Push(ExprFinishIdent(w, ident))
                                            startWalk sym ident.SpanStart w history
                        | _ ->
                            table[box node] <- emptyRes
                            curResult <- emptyRes

            startExpr want expr

            while tasks.Count > 0 do
                match tasks.Pop() with
                | ExprStart(w, node) -> startExpr w node
                | ExprFinishUnary(w, node) -> (tableFor w)[box node] <- curResult
                | ExprFinishBinaryLeft(w, bin) ->
                    let leftRes = curResult

                    let canShortCircuit =
                        not leftRes.Capped
                        && List.isEmpty leftRes.Witnesses
                        && (match bin.Kind() with
                            | SyntaxKind.LogicalAndExpression -> w
                            | SyntaxKind.LogicalOrExpression -> not w
                            | _ -> false)

                    if canShortCircuit then
                        (tableFor w)[box bin] <- emptyRes
                        curResult <- emptyRes
                    else
                        tasks.Push(ExprFinishBinaryRight(w, bin, leftRes))
                        startExpr w bin.Right
                | ExprFinishBinaryRight(w, bin, leftRes) ->
                    let lc = ref false

                    let ws =
                        match bin.Kind() with
                        | SyntaxKind.LogicalAndExpression ->
                            if w then
                                combineWitnesses lc leftRes.Witnesses curResult.Witnesses
                            else
                                interleaveWitnesses leftRes.Witnesses curResult.Witnesses
                                |> distinctBounded lc
                        | SyntaxKind.LogicalOrExpression ->
                            if w then
                                interleaveWitnesses leftRes.Witnesses curResult.Witnesses
                                |> distinctBounded lc
                            else
                                combineWitnesses lc leftRes.Witnesses curResult.Witnesses
                        | _ -> []

                    let res =
                        {
                            Witnesses = ws
                            Capped = lc.Value || leftRes.Capped || curResult.Capped
                        }

                    (tableFor w)[box bin] <- res
                    curResult <- res
                | ExprFinishEqStep(w, bin, step, r0, r1, r2) ->
                    match step with
                    | 0 ->
                        tasks.Push(ExprFinishEqStep(w, bin, 1, curResult, emptyRes, emptyRes))
                        startExpr false bin.Left
                    | 1 ->
                        tasks.Push(ExprFinishEqStep(w, bin, 2, r0, curResult, emptyRes))
                        startExpr true bin.Right
                    | 2 ->
                        tasks.Push(ExprFinishEqStep(w, bin, 3, r0, r1, curResult))
                        startExpr false bin.Right
                    | _ ->
                        let lc = ref false

                        let effW =
                            if bin.IsKind SyntaxKind.NotEqualsExpression then
                                not w
                            else
                                w

                        let ws = equalWitnesses lc lookupWitnesses effW bin.Left bin.Right

                        let res =
                            {
                                Witnesses = ws
                                Capped =
                                    lc.Value
                                    || r0.Capped
                                    || r1.Capped
                                    || r2.Capped
                                    || curResult.Capped
                            }

                        (tableFor w)[box bin] <- res
                        curResult <- res
                | ExprFinishIdent(w, ident) -> (tableFor w)[box ident] <- curResult
                | RunGuardHold st ->
                    if st.WaitingChild then
                        let lc = ref false
                        st.CurAcc <- combineWitnesses lc st.CurAcc curResult.Witnesses
                        st.CurCapped <- st.CurCapped || curResult.Capped || lc.Value
                        st.Idx <- st.Idx + 1
                        st.WaitingChild <- false

                    let mutable yielding = false

                    while not yielding do
                        if st.Phase = 0 then
                            if List.isEmpty st.CurAcc then
                                st.Phase <- 2
                            elif st.Idx < st.NodeG.GuardTrue.Length then
                                let exprG = st.NodeG.GuardTrue[st.Idx]
                                let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                                if memo.True.TryGetValue(box exprG, &hit) then
                                    let lc = ref false
                                    st.CurAcc <- combineWitnesses lc st.CurAcc hit.Witnesses
                                    st.CurCapped <- st.CurCapped || hit.Capped || lc.Value
                                    st.Idx <- st.Idx + 1
                                else
                                    st.WaitingChild <- true
                                    tasks.Push(RunGuardHold st)
                                    startExpr true exprG
                                    yielding <- true
                            else
                                st.Phase <- 1
                                st.Idx <- 0
                        elif st.Phase = 1 then
                            if List.isEmpty st.CurAcc then
                                st.Phase <- 2
                            elif st.Idx < st.NodeG.GuardFalse.Length then
                                let exprG = st.NodeG.GuardFalse[st.Idx]
                                let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                                if memo.False.TryGetValue(box exprG, &hit) then
                                    let lc = ref false
                                    st.CurAcc <- combineWitnesses lc st.CurAcc hit.Witnesses
                                    st.CurCapped <- st.CurCapped || hit.Capped || lc.Value
                                    st.Idx <- st.Idx + 1
                                else
                                    st.WaitingChild <- true
                                    tasks.Push(RunGuardHold st)
                                    startExpr false exprG
                                    yielding <- true
                            else
                                st.Phase <- 2
                        else
                            let entryRes =
                                {
                                    Witnesses = st.CurAcc
                                    Capped = st.CurCapped
                                }

                            (guardHoldCache st.NodeG)[st.NodeG] <- entryRes

                            let mutable moved = false

                            while st.Chain.Count > 0 && not moved do
                                let nextG = st.Chain.Pop()
                                let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                                if (guardHoldCache nextG).TryGetValue(nextG, &hit) then
                                    st.CurAcc <- hit.Witnesses
                                    st.CurCapped <- hit.Capped
                                else
                                    st.NodeG <- nextG
                                    st.Phase <- 0
                                    st.Idx <- 0
                                    moved <- true

                            if not moved then
                                curResult <-
                                    {
                                        Witnesses = st.CurAcc
                                        Capped = st.CurCapped
                                    }

                                yielding <- true
                | RunGuardFail st ->
                    if st.WaitingChild then
                        for cand in curResult.Witnesses do
                            st.FailParts.Add cand

                        st.NodeCapped <- st.NodeCapped || curResult.Capped
                        st.Idx <- st.Idx + 1
                        st.WaitingChild <- false

                    let mutable yielding = false

                    while not yielding do
                        if st.NeedSeed then
                            st.FailParts.Clear()

                            for cand in st.ParentFails do
                                st.FailParts.Add cand

                            st.NodeCapped <- st.ParentCapped
                            st.NeedSeed <- false

                        if st.Phase = 0 then
                            if st.Idx < st.NodeG.GuardTrue.Length then
                                let exprG = st.NodeG.GuardTrue[st.Idx]
                                let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                                if memo.False.TryGetValue(box exprG, &hit) then
                                    for cand in hit.Witnesses do
                                        st.FailParts.Add cand

                                    st.NodeCapped <- st.NodeCapped || hit.Capped
                                    st.Idx <- st.Idx + 1
                                else
                                    st.WaitingChild <- true
                                    tasks.Push(RunGuardFail st)
                                    startExpr false exprG
                                    yielding <- true
                            else
                                st.Phase <- 1
                                st.Idx <- 0
                        elif st.Phase = 1 then
                            if st.Idx < st.NodeG.GuardFalse.Length then
                                let exprG = st.NodeG.GuardFalse[st.Idx]
                                let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                                if memo.True.TryGetValue(box exprG, &hit) then
                                    for cand in hit.Witnesses do
                                        st.FailParts.Add cand

                                    st.NodeCapped <- st.NodeCapped || hit.Capped
                                    st.Idx <- st.Idx + 1
                                else
                                    st.WaitingChild <- true
                                    tasks.Push(RunGuardFail st)
                                    startExpr true exprG
                                    yielding <- true
                            else
                                st.Phase <- 2
                        else
                            let lc = ref false
                            let nextFails = distinctBounded lc st.FailParts
                            let didCap = st.NodeCapped || lc.Value

                            let entryRes =
                                {
                                    Witnesses = nextFails
                                    Capped = didCap
                                }

                            (guardFailCache st.NodeG)[st.NodeG] <- entryRes
                            st.ParentFails <- nextFails
                            st.ParentCapped <- didCap

                            let mutable moved = false

                            while st.Chain.Count > 0 && not moved do
                                let nextG = st.Chain.Pop()
                                let mutable hit = Unchecked.defaultof<CachedWitnessResult>

                                if (guardFailCache nextG).TryGetValue(nextG, &hit) then
                                    st.ParentFails <- hit.Witnesses
                                    st.ParentCapped <- hit.Capped
                                else
                                    st.NodeG <- nextG
                                    st.Phase <- 0
                                    st.Idx <- 0
                                    st.NeedSeed <- true
                                    moved <- true

                            if not moved then
                                curResult <-
                                    {
                                        Witnesses = st.ParentFails
                                        Capped = st.ParentCapped
                                    }

                                yielding <- true
                | RunWalk wf ->
                    if wf.Stage = 0 then
                        wf.Taken <- curResult.Witnesses
                        wf.PrevCap <- curResult.Capped
                        wf.Stage <- 1
                        tasks.Push(RunWalk wf)
                        startGuardFail wf.Entry.Guard
                    elif wf.Stage = 1 then
                        let guardFails = curResult.Witnesses
                        let prevCap = wf.PrevCap || curResult.Capped

                        if List.isEmpty guardFails then
                            let lc = ref false
                            let resList = distinctBounded lc wf.Taken
                            let didCap = prevCap || lc.Value
                            let allSealed = wf.Entry.Guard.IsFullySealed
                            let cRes = { Witnesses = resList; Capped = didCap }

                            if wf.Entry.MaxPos < wf.SpanStart then
                                let wk = { Sym = wf.Sym; Items = wf.Cur }

                                if allSealed then
                                    (if wf.Want then
                                         memo.SealedWalkTrue
                                     else
                                         memo.SealedWalkFalse)[wk] <- cRes
                                else
                                    (if wf.Want then memo.TempWalkTrue else memo.TempWalkFalse)[wk] <-
                                        cRes

                            curResult <- cRes
                            curWalkSealed <- allSealed
                        else
                            wf.GuardFails <- guardFails
                            wf.PrevCap <- prevCap
                            wf.Stage <- 2
                            tasks.Push(RunWalk wf)
                            startWalk wf.Sym wf.SpanStart wf.Want wf.Rest
                    else
                        let restRes = curResult
                        let restSealed = curWalkSealed
                        let lc = ref false
                        let skipped = combineWitnesses lc wf.GuardFails restRes.Witnesses
                        let resList = distinctBounded lc (Seq.append wf.Taken skipped)
                        let didCap = wf.PrevCap || restRes.Capped || lc.Value
                        let allSealed = wf.Entry.Guard.IsFullySealed && restSealed
                        let cRes = { Witnesses = resList; Capped = didCap }

                        if wf.Entry.MaxPos < wf.SpanStart then
                            let wk = { Sym = wf.Sym; Items = wf.Cur }

                            if allSealed then
                                (if wf.Want then
                                     memo.SealedWalkTrue
                                 else
                                     memo.SealedWalkFalse)[wk] <- cRes
                            else
                                (if wf.Want then memo.TempWalkTrue else memo.TempWalkFalse)[wk] <-
                                    cRes

                        curResult <- cRes
                        curWalkSealed <- allSealed

            if curResult.Capped then
                capped.Value <- true

            curResult.Witnesses

    let private collectRiskSymbols
        (overrides: OverrideScope)
        (mustHold: bool)
        (expr: ExpressionSyntax)
        =
        let riskSyms = ResizeArray<string>()
        let seen = HashSet<string>(StringComparer.Ordinal)
        let work = Stack<struct (bool * bool * int * ExpressionSyntax)>()
        work.Push(struct (false, mustHold, 0, expr))
        let mutable alwaysCheck = false
        let mutable hasEq = false

        while not alwaysCheck && work.Count > 0 do
            let struct (insideEq, desiredEval, d, node) = work.Pop()

            if not (isNull (box node)) then
                if d >= 64 then
                    alwaysCheck <- true
                else
                    match node with
                    | :? ParenthesizedExpressionSyntax as paren ->
                        work.Push(struct (insideEq, desiredEval, d + 1, paren.Expression))
                    | :? LiteralExpressionSyntax -> ()
                    | :? PrefixUnaryExpressionSyntax as unary when
                        unary.IsKind SyntaxKind.LogicalNotExpression
                        ->
                        work.Push(struct (insideEq, not desiredEval, d + 1, unary.Operand))
                    | :? BinaryExpressionSyntax as binary ->
                        match binary.Kind() with
                        | SyntaxKind.LogicalAndExpression
                        | SyntaxKind.LogicalOrExpression ->
                            work.Push(struct (insideEq, desiredEval, d + 1, binary.Right))
                            work.Push(struct (insideEq, desiredEval, d + 1, binary.Left))
                        | SyntaxKind.EqualsExpression
                        | SyntaxKind.NotEqualsExpression ->
                            hasEq <- true
                            work.Push(struct (true, false, d + 1, binary.Right))
                            work.Push(struct (true, false, d + 1, binary.Left))
                        | _ -> ()
                    | :? IdentifierNameSyntax as ident ->
                        let sym = preprocessorSymbolName ident.Identifier

                        if not (String.IsNullOrEmpty sym) then
                            match tryLookupUnconditionalOverride overrides sym ident.SpanStart with
                            | ResolvedOverride _ -> ()
                            | UnresolvedOverride -> alwaysCheck <- true
                            | NoOverride ->
                                if (insideEq || not desiredEval) && seen.Add sym then
                                    riskSyms.Add sym
                    | _ -> ()

        if
            alwaysCheck
            || (hasEq
                && tryEvalConditionFast overrides Set.empty false 0 expr
                   <> ValueSome(ValueSome mustHold))
        then
            null
        else
            riskSyms.ToArray()

    [<NoComparison; NoEquality>]
    type private WatcherIndex =
        {
            Exprs: ResizeArray<ExpressionSyntax>
            Entries: ResizeArray<string array>
            Watchers: Dictionary<string, ResizeArray<int>>
            Always: ResizeArray<int>
            mutable CheckedStamp: int array
            mutable Stamp: int
        }

        static member Create() =
            {
                Exprs = ResizeArray<ExpressionSyntax>()
                Entries = ResizeArray<string array>()
                Watchers = Dictionary<string, ResizeArray<int>>(StringComparer.Ordinal)
                Always = ResizeArray<int>()
                CheckedStamp = Array.empty
                Stamp = 0
            }

        member private this.NextCheckStamp(minLen: int) =
            if this.CheckedStamp.Length < minLen then
                let newLen = max minLen (max 16 (this.CheckedStamp.Length * 2))
                this.CheckedStamp <- Array.zeroCreate<int> newLen
                this.Stamp <- 1
            elif this.Stamp = Int32.MaxValue then
                Array.fill this.CheckedStamp 0 this.CheckedStamp.Length 0
                this.Stamp <- 1
            else
                this.Stamp <- this.Stamp + 1

            this.Stamp

        member this.Count = this.Exprs.Count

        member this.Add(overrides: OverrideScope, mustHold: bool, expr: ExpressionSyntax) =
            let idx = this.Exprs.Count
            this.Exprs.Add expr
            let syms = collectRiskSymbols overrides mustHold expr
            this.Entries.Add syms

            if isNull syms then
                this.Always.Add idx
            else
                for i = 0 to syms.Length - 1 do
                    let s = syms[i]

                    match this.Watchers.TryGetValue s with
                    | true, list -> list.Add idx
                    | false, _ ->
                        let list = ResizeArray<int>(1)
                        list.Add idx
                        this.Watchers[s] <- list

        member this.TruncateTo(keepCount: int) =
            while this.Exprs.Count > keepCount do
                let idx = this.Exprs.Count - 1
                this.Exprs.RemoveAt idx
                let syms = this.Entries[idx]
                this.Entries.RemoveAt idx

                if isNull syms then
                    if this.Always.Count > 0 && this.Always[this.Always.Count - 1] = idx then
                        this.Always.RemoveAt(this.Always.Count - 1)
                else
                    for i = 0 to syms.Length - 1 do
                        let s = syms[i]

                        match this.Watchers.TryGetValue s with
                        | true, list ->
                            if list.Count > 0 && list[list.Count - 1] = idx then
                                list.RemoveAt(list.Count - 1)

                            if list.Count = 0 then
                                this.Watchers.Remove s |> ignore
                        | false, _ -> ()

        member this.Check
            (
                overrides: OverrideScope,
                guardCaches: EnvGuardCacheRing,
                limit: int,
                mustHold: bool,
                env: Set<string>
            ) =
            if limit <= 0 || (this.Always.Count = 0 && this.Watchers.Count = 0) then
                true
            elif env.Count <= 1 && this.Always.Count = 0 then
                let mutable ok = true
                use symEnum = (env :> seq<string>).GetEnumerator()

                if symEnum.MoveNext() then
                    match this.Watchers.TryGetValue symEnum.Current with
                    | false, _ -> ()
                    | true, indices ->
                        let mutable m = 0

                        while ok && m < indices.Count && indices[m] < limit do
                            let idx = indices[m]

                            if
                                evalCondition overrides guardCaches env this.Exprs[idx] <> mustHold
                            then
                                ok <- false

                            m <- m + 1

                ok
            else
                let stamp = this.NextCheckStamp limit
                let stamps = this.CheckedStamp
                let mutable ok = true
                let mutable k = 0

                while ok && k < this.Always.Count && this.Always[k] < limit do
                    let idx = this.Always[k]

                    if stamps[idx] <> stamp then
                        stamps[idx] <- stamp

                        if evalCondition overrides guardCaches env this.Exprs[idx] <> mustHold then
                            ok <- false

                    k <- k + 1

                if ok && this.Watchers.Count > 0 then
                    use symEnum = (env :> seq<string>).GetEnumerator()

                    while ok && symEnum.MoveNext() do
                        match this.Watchers.TryGetValue symEnum.Current with
                        | false, _ -> ()
                        | true, indices ->
                            let mutable m = 0

                            while ok && m < indices.Count && indices[m] < limit do
                                let idx = indices[m]

                                if stamps[idx] <> stamp then
                                    stamps[idx] <- stamp

                                    if
                                        evalCondition overrides guardCaches env this.Exprs[idx]
                                        <> mustHold
                                    then
                                        ok <- false

                                m <- m + 1

                ok

        member this.CollectFailing
            (
                overrides: OverrideScope,
                guardCaches: EnvGuardCacheRing,
                limit: int,
                mustHold: bool,
                env: Set<string>,
                seen: HashSet<int>,
                target: ResizeArray<int>
            ) =
            if limit > 0 && (this.Always.Count > 0 || this.Watchers.Count > 0) then
                let stamp = this.NextCheckStamp limit
                let stamps = this.CheckedStamp
                let mutable k = 0

                while k < this.Always.Count && this.Always[k] < limit do
                    let idx = this.Always[k]

                    if stamps[idx] <> stamp then
                        stamps[idx] <- stamp

                        if
                            not (seen.Contains idx)
                            && evalCondition overrides guardCaches env this.Exprs[idx] <> mustHold
                        then
                            seen.Add idx |> ignore
                            target.Add idx

                    k <- k + 1

                if this.Watchers.Count > 0 then
                    use symEnum = (env :> seq<string>).GetEnumerator()

                    while symEnum.MoveNext() do
                        match this.Watchers.TryGetValue symEnum.Current with
                        | false, _ -> ()
                        | true, indices ->
                            let mutable m = 0

                            while m < indices.Count && indices[m] < limit do
                                let idx = indices[m]

                                if stamps[idx] <> stamp then
                                    stamps[idx] <- stamp

                                    if
                                        not (seen.Contains idx)
                                        && evalCondition overrides guardCaches env this.Exprs[idx]
                                           <> mustHold
                                    then
                                        seen.Add idx |> ignore
                                        target.Add idx

                                m <- m + 1

    let inline private unwrapParens (expr: ExpressionSyntax) =
        let mutable cur = expr
        let mutable looping = not (isNull (box cur))

        while looping do
            match cur with
            | :? ParenthesizedExpressionSyntax as p when not (isNull (box p.Expression)) ->
                cur <- p.Expression
            | _ -> looping <- false

        cur

    let private priorExprComparer =
        { new IEqualityComparer<ExpressionSyntax> with
            member _.Equals(x, y) =
                if obj.ReferenceEquals(x, y) then
                    true
                else
                    let work = Stack<struct (ExpressionSyntax * ExpressionSyntax)>()
                    work.Push(struct (x, y))
                    let mutable equal = true

                    while equal && work.Count > 0 do
                        let struct (lRaw, rRaw) = work.Pop()
                        let l = unwrapParens lRaw
                        let r = unwrapParens rRaw

                        if not (obj.ReferenceEquals(l, r)) then
                            if isNull (box l) || isNull (box r) || l.RawKind <> r.RawKind then
                                equal <- false
                            else
                                match l with
                                | :? IdentifierNameSyntax as li ->
                                    let ri = r :?> IdentifierNameSyntax
                                    let lSym = preprocessorSymbolName li.Identifier
                                    let rSym = preprocessorSymbolName ri.Identifier

                                    equal <-
                                        not (String.IsNullOrEmpty lSym)
                                        && not (String.IsNullOrEmpty rSym)
                                        && String.Equals(lSym, rSym, StringComparison.Ordinal)
                                | :? LiteralExpressionSyntax as ll ->
                                    let rl = r :?> LiteralExpressionSyntax

                                    equal <-
                                        String.Equals(
                                            ll.Token.ValueText,
                                            rl.Token.ValueText,
                                            StringComparison.Ordinal
                                        )
                                | :? PrefixUnaryExpressionSyntax as lu ->
                                    let ru = r :?> PrefixUnaryExpressionSyntax
                                    work.Push(struct (lu.Operand, ru.Operand))
                                | :? BinaryExpressionSyntax as lb ->
                                    let rb = r :?> BinaryExpressionSyntax
                                    work.Push(struct (lb.Right, rb.Right))
                                    work.Push(struct (lb.Left, rb.Left))
                                | _ -> equal <- SyntaxFactory.AreEquivalent(l, r, false)

                    equal

            member _.GetHashCode(expr) =
                let mutable hc = HashCode()
                let work = Stack<ExpressionSyntax>()
                work.Push expr

                while work.Count > 0 do
                    let cur = unwrapParens (work.Pop())

                    if isNull (box cur) then
                        hc.Add 0
                    else
                        hc.Add cur.RawKind

                        match cur with
                        | :? IdentifierNameSyntax as id ->
                            let sym = preprocessorSymbolName id.Identifier

                            if not (String.IsNullOrEmpty sym) then
                                hc.Add(StringComparer.Ordinal.GetHashCode sym)
                        | :? LiteralExpressionSyntax as lit ->
                            if not (isNull lit.Token.ValueText) then
                                hc.Add(StringComparer.Ordinal.GetHashCode lit.Token.ValueText)
                        | :? PrefixUnaryExpressionSyntax as u -> work.Push u.Operand
                        | :? BinaryExpressionSyntax as b ->
                            work.Push b.Right
                            work.Push b.Left
                        | _ -> ()

                hc.ToHashCode()
        }

    [<NoComparison; NoEquality>]
    type private FallbackConstraintState =
        {
            Forced: Dictionary<string, bool>
            mutable Consistent: bool
            mutable HasGuarded: bool
            mutable OuterInit: bool
            mutable ProcessedPriors: int
            UnsatOnEmptyPriors: ResizeArray<int>
            mutable UnsatStepped: int
            mutable UnsatBaseReady: bool
            mutable UnsatBaseCapped: bool
            mutable UnsatBaseAcc: WitnessNode list
            SmallWatchers: Dictionary<string, ResizeArray<struct (int * int)>>
            SmallPropQueue: Queue<struct (int * int)>
            SmallInPropQueue: HashSet<struct (int * int)>
            mutable SmallOuterInit: bool
            mutable SmallProcessedPriors: int
            AddedKeys: ResizeArray<string>
            Work: Stack<struct (bool * ExpressionSyntax)>
        }

        static member Create() =
            {
                Forced = Dictionary<string, bool>(StringComparer.Ordinal)
                Consistent = true
                HasGuarded = false
                OuterInit = false
                ProcessedPriors = 0
                UnsatOnEmptyPriors = ResizeArray<int>()
                UnsatStepped = 0
                UnsatBaseReady = false
                UnsatBaseCapped = false
                UnsatBaseAcc = []
                SmallWatchers =
                    Dictionary<string, ResizeArray<struct (int * int)>>(StringComparer.Ordinal)
                SmallPropQueue = Queue<struct (int * int)>()
                SmallInPropQueue = HashSet<struct (int * int)>()
                SmallOuterInit = false
                SmallProcessedPriors = 0
                AddedKeys = ResizeArray<string>()
                Work = Stack<struct (bool * ExpressionSyntax)>()
            }

    [<NoComparison; NoEquality>]
    type private ConditionalFrame =
        {
            Priors: WatcherIndex
            SavedTrueCount: int
            SavedFalseCount: int
            mutable ActiveFalseAddedCount: int
            mutable TakenTrue: ExpressionSyntax voption
            mutable TakenPriorCount: int
            mutable NegatedReady: bool
            mutable NegatedCount: int
            mutable NegatedCandidates: WitnessNode list
            mutable FrameUnconditional: bool
            mutable PriorsAllConstFalse: bool
            mutable AnyPriorConstTrue: bool
            mutable ArmImpossible: bool
            mutable ArmNode: GuardNode
            mutable PriorNegNode: GuardNode
            mutable PriorNegSyncCount: int
            mutable PendingGuarded: ResizeArray<struct (string * OverrideEntry)>
            mutable EvalCaches: EnvGuardCacheRing
            mutable ConstGuardCache: ConstScopeCache
            mutable SeenPriors: HashSet<ExpressionSyntax>
            mutable SiblingOverrides: Dictionary<string, bool>
            mutable FallbackState: FallbackConstraintState voption
        }

        member this.SetSiblingOverride(sym: string, value: bool) =
            if isNull this.SiblingOverrides then
                this.SiblingOverrides <- Dictionary<string, bool>(StringComparer.Ordinal)

            this.SiblingOverrides[sym] <- value

        member this.TakeSiblingOverrides() =
            let m = this.SiblingOverrides
            this.SiblingOverrides <- null
            m

        member this.EnsureEvalCaches(firstSymbolPos: Dictionary<string, int>) =
            if isNull this.EvalCaches then
                this.EvalCaches <- EnvGuardCacheRing firstSymbolPos

            this.EvalCaches

        member this.EnsureConstGuardCache() =
            if isNull this.ConstGuardCache then
                this.ConstGuardCache <- ConstScopeCache()

            this.ConstGuardCache

        member this.EnsureSeenPriors() =
            if isNull this.SeenPriors then
                let set = HashSet<ExpressionSyntax>(priorExprComparer)

                for i = 0 to this.Priors.Count - 1 do
                    let e = this.Priors.Exprs[i]

                    if not (isNull (box e)) then
                        set.Add e |> ignore

                this.SeenPriors <- set

            this.SeenPriors

        member this.EnsureFallbackState() =
            match this.FallbackState with
            | ValueSome s -> s
            | ValueNone ->
                let s = FallbackConstraintState.Create()
                this.FallbackState <- ValueSome s
                s

    let private exprMentionsAnySymbol (symMap: Dictionary<string, bool>) (expr: ExpressionSyntax) =
        if isNull symMap || symMap.Count = 0 || isNull (box expr) then
            false
        else
            let work = Stack<ExpressionSyntax>()
            work.Push expr
            let mutable found = false

            while not found && work.Count > 0 do
                let cur = work.Pop()

                if not (isNull (box cur)) then
                    match cur with
                    | :? IdentifierNameSyntax as ident ->
                        let sym = preprocessorSymbolName ident.Identifier

                        if not (String.IsNullOrEmpty sym) && symMap.ContainsKey sym then
                            found <- true
                    | :? ParenthesizedExpressionSyntax as p -> work.Push p.Expression
                    | :? PrefixUnaryExpressionSyntax as u when
                        u.IsKind SyntaxKind.LogicalNotExpression
                        ->
                        work.Push u.Operand
                    | :? BinaryExpressionSyntax as b ->
                        match b.Kind() with
                        | SyntaxKind.LogicalAndExpression
                        | SyntaxKind.LogicalOrExpression
                        | SyntaxKind.EqualsExpression
                        | SyntaxKind.NotEqualsExpression ->
                            work.Push b.Right
                            work.Push b.Left
                        | _ -> ()
                    | _ -> ()

            found

    let private evalConstraints
        (overrides: OverrideScope)
        (guardCaches: EnvGuardCacheRing)
        (priors: WatcherIndex)
        (priorLimit: int)
        (outerTrue: WatcherIndex)
        (trueLimit: int)
        (outerFalse: WatcherIndex)
        (falseLimit: int)
        (env: Set<string>)
        =
        priors.Check(overrides, guardCaches, priorLimit, false, env)
        && outerTrue.Check(overrides, guardCaches, trueLimit, true, env)
        && outerFalse.Check(overrides, guardCaches, falseLimit, false, env)

    let private extendCandidates
        (overrides: OverrideScope)
        (guardCaches: EnvGuardCacheRing)
        (capped: bool ref)
        (memo: WitnessMemo)
        (baseCandidates: WitnessNode list)
        (addTrue: ExpressionSyntax list)
        (addFalse: ExpressionSyntax list)
        (priors: WatcherIndex)
        (priorLimit: int)
        (outerTrue: WatcherIndex)
        (outerTrueLimit: int)
        (outerFalse: WatcherIndex)
        (outerFalseLimit: int)
        =
        if List.isEmpty baseCandidates then
            []
        else
            let mutable acc = baseCandidates

            let partitionSatisfying want expr (candidates: WitnessNode list) =
                let sat = ResizeArray<WitnessNode>(candidates.Length)
                let unsat = ResizeArray<WitnessNode>()

                for w in candidates do
                    if evalCondition overrides guardCaches (w.ToSet()) expr = want then
                        sat.Add w
                    else
                        unsat.Add w

                sat, unsat

            let applyStep want expr =
                if not (List.isEmpty acc) then
                    let sat, unsat = partitionSatisfying want expr acc

                    if sat.Count > witnessLimit then
                        acc <- distinctBounded capped sat
                    elif sat.Count = witnessLimit || unsat.Count = 0 then
                        acc <- List.ofSeq sat
                    else
                        let exprWitnesses = witnesses overrides null capped memo want expr

                        let extended =
                            combineWitnesses capped (List.ofSeq unsat) exprWitnesses
                            |> List.filter (fun w ->
                                evalCondition overrides guardCaches (w.ToSet()) expr = want)

                        if sat.Count = 0 then
                            acc <- extended
                        else
                            for w in extended do
                                sat.Add w

                            acc <- distinctBounded capped sat

            for expr in addTrue do
                applyStep true expr

            for expr in addFalse do
                applyStep false expr

            if List.isEmpty acc then
                []
            elif
                not (List.isEmpty acc)
                && priors.Watchers.Count = 0
                && priors.Always.Count = 0
                && outerTrue.Watchers.Count = 0
                && outerTrue.Always.Count = 0
                && outerFalse.Watchers.Count = 0
                && outerFalse.Always.Count = 0
            then
                acc
            else
                let kept = ResizeArray<WitnessNode>(acc.Length)

                let seen =
                    if acc.Length > 1 then
                        HashSet<WitnessNode>(witnessNodeComparer)
                    else
                        null

                for w in acc do
                    let unchangedFromBase =
                        baseCandidates |> List.exists (fun b -> witnessNodeComparer.Equals(w, b))

                    if
                        unchangedFromBase
                        || evalConstraints
                            overrides
                            guardCaches
                            priors
                            priorLimit
                            outerTrue
                            outerTrueLimit
                            outerFalse
                            outerFalseLimit
                            (w.ToSet())
                    then
                        if isNull seen || seen.Add w then
                            kept.Add w

                List.ofSeq kept

    let private pushConstraintInto
        (overrides: OverrideScope)
        (forced: Dictionary<string, bool>)
        (addedKeys: ResizeArray<string>)
        (work: Stack<struct (bool * ExpressionSyntax)>)
        (consistent: bool byref)
        (hasGuarded: bool byref)
        (want: bool)
        (expr: ExpressionSyntax)
        =
        if consistent && not (isNull (box expr)) then
            work.Clear()
            work.Push(struct (want, expr))

            while consistent && work.Count > 0 do
                let struct (w, node) = work.Pop()

                if not (isNull (box node)) then
                    match node with
                    | :? ParenthesizedExpressionSyntax as paren ->
                        if isNull (box paren.Expression) then
                            if w then
                                consistent <- false
                        else
                            work.Push(struct (w, paren.Expression))
                    | :? PrefixUnaryExpressionSyntax as unary when
                        unary.IsKind SyntaxKind.LogicalNotExpression
                        ->
                        if isNull (box unary.Operand) then
                            if not w then
                                consistent <- false
                        else
                            work.Push(struct (not w, unary.Operand))
                    | :? BinaryExpressionSyntax as binary ->
                        match binary.Kind() with
                        | SyntaxKind.LogicalAndExpression when w ->
                            work.Push(struct (true, binary.Right))
                            work.Push(struct (true, binary.Left))
                        | SyntaxKind.LogicalOrExpression when not w ->
                            work.Push(struct (false, binary.Right))
                            work.Push(struct (false, binary.Left))
                        | _ -> ()
                    | :? LiteralExpressionSyntax as literal ->
                        if literal.IsKind SyntaxKind.TrueLiteralExpression <> w then
                            consistent <- false
                    | :? IdentifierNameSyntax as ident ->
                        let name = preprocessorSymbolName ident.Identifier

                        if not (String.IsNullOrEmpty name) then
                            match tryLookupUnconditionalOverride overrides name ident.SpanStart with
                            | ResolvedOverride ov ->
                                if ov <> w then
                                    consistent <- false
                            | UnresolvedOverride -> hasGuarded <- true
                            | NoOverride ->
                                match forced.TryGetValue name with
                                | true, existing ->
                                    if existing <> w then
                                        consistent <- false
                                | false, _ ->
                                    forced[name] <- w

                                    if not (isNull addedKeys) then
                                        addedKeys.Add name
                    | _ -> ()

    let inline private hasAnySymbolOverride (overrides: OverrideScope) (sym: string) (pos: int) =
        not (isNull overrides)
        && overrides.HasAny
        && (overrides.History.ContainsKey sym
            || match tryLookupSiblingWindow overrides sym pos with
               | ValueSome _ -> true
               | ValueNone -> false)

    let private tryCollectSmallFreeInto
        (overrides: OverrideScope)
        (forced: Dictionary<string, bool>)
        (maxFree: int)
        (free: ResizeArray<string>)
        (seen: HashSet<string>)
        (expr: ExpressionSyntax)
        : bool =
        free.Clear()
        seen.Clear()

        if isNull (box expr) then
            false
        else
            let work = Stack<struct (int * ExpressionSyntax)>()
            work.Push(struct (0, expr))
            let mutable ok = true

            while ok && work.Count > 0 do
                let struct (d, cur) = work.Pop()

                if isNull (box cur) || d >= 64 then
                    ok <- false
                else
                    match cur with
                    | :? ParenthesizedExpressionSyntax as paren ->
                        work.Push(struct (d + 1, paren.Expression))
                    | :? PrefixUnaryExpressionSyntax as unary when
                        unary.IsKind SyntaxKind.LogicalNotExpression
                        ->
                        work.Push(struct (d + 1, unary.Operand))
                    | :? LiteralExpressionSyntax as lit when
                        lit.IsKind SyntaxKind.TrueLiteralExpression
                        || lit.IsKind SyntaxKind.FalseLiteralExpression
                        ->
                        ()
                    | :? BinaryExpressionSyntax as bin ->
                        match bin.Kind() with
                        | SyntaxKind.LogicalAndExpression
                        | SyntaxKind.LogicalOrExpression
                        | SyntaxKind.EqualsExpression
                        | SyntaxKind.NotEqualsExpression ->
                            work.Push(struct (d + 1, bin.Right))
                            work.Push(struct (d + 1, bin.Left))
                        | _ -> ok <- false
                    | :? IdentifierNameSyntax as ident ->
                        let sym = preprocessorSymbolName ident.Identifier

                        if String.IsNullOrEmpty sym then
                            ok <- false
                        elif hasAnySymbolOverride overrides sym ident.SpanStart then
                            ok <- false
                        elif not (forced.ContainsKey sym) && seen.Add sym then
                            if free.Count >= maxFree then ok <- false else free.Add sym
                    | _ -> ok <- false

            ok

    let rec private evalSmallBoolExpr
        (forced: Dictionary<string, bool>)
        (free: ResizeArray<string>)
        (mask: int)
        (expr: ExpressionSyntax)
        : bool =
        match expr with
        | :? ParenthesizedExpressionSyntax as paren ->
            evalSmallBoolExpr forced free mask paren.Expression
        | :? PrefixUnaryExpressionSyntax as unary ->
            not (evalSmallBoolExpr forced free mask unary.Operand)
        | :? LiteralExpressionSyntax as lit -> lit.IsKind SyntaxKind.TrueLiteralExpression
        | :? BinaryExpressionSyntax as bin ->
            let lv = evalSmallBoolExpr forced free mask bin.Left
            let rv = evalSmallBoolExpr forced free mask bin.Right

            match bin.Kind() with
            | SyntaxKind.LogicalAndExpression -> lv && rv
            | SyntaxKind.LogicalOrExpression -> lv || rv
            | SyntaxKind.EqualsExpression -> lv = rv
            | _ -> lv <> rv
        | :? IdentifierNameSyntax as ident ->
            let sym = preprocessorSymbolName ident.Identifier

            match forced.TryGetValue sym with
            | true, v -> v
            | false, _ ->
                let mutable matched = false
                let mutable i = 0

                while not matched && i < free.Count do
                    if StringComparer.Ordinal.Equals(free[i], sym) then
                        matched <- (mask &&& (1 <<< i)) <> 0

                    i <- i + 1

                matched
        | _ -> false

    let private tryPickSplitSymbol
        (overrides: OverrideScope)
        (forced: Dictionary<string, bool>)
        (addTrue: ExpressionSyntax list)
        (outerTrue: WatcherIndex)
        (outerTrueLimit: int)
        (outerFalse: WatcherIndex)
        (outerFalseLimit: int)
        (priors: WatcherIndex)
        (priorLimit: int)
        : string voption =
        let scores = Dictionary<string, int>(StringComparer.Ordinal)
        let targetSyms = HashSet<string>(StringComparer.Ordinal)
        let exprSyms = HashSet<string>(StringComparer.Ordinal)
        let work = Stack<ExpressionSyntax>()

        let scanExpr (inTarget: bool) (expr: ExpressionSyntax) =
            if not (isNull (box expr)) then
                exprSyms.Clear()
                work.Clear()
                work.Push expr

                while work.Count > 0 do
                    let cur = work.Pop()

                    if not (isNull (box cur)) then
                        match cur with
                        | :? ParenthesizedExpressionSyntax as paren -> work.Push paren.Expression
                        | :? PrefixUnaryExpressionSyntax as unary -> work.Push unary.Operand
                        | :? BinaryExpressionSyntax as bin ->
                            work.Push bin.Right
                            work.Push bin.Left
                        | :? IdentifierNameSyntax as ident ->
                            let sym = preprocessorSymbolName ident.Identifier

                            if
                                not (String.IsNullOrEmpty sym)
                                && not (forced.ContainsKey sym)
                                && not (hasAnySymbolOverride overrides sym ident.SpanStart)
                                && exprSyms.Add sym
                            then
                                if inTarget then
                                    targetSyms.Add sym |> ignore

                                let weight =
                                    if inTarget then 3
                                    elif targetSyms.Contains sym then 4
                                    else 1

                                let prev =
                                    match scores.TryGetValue sym with
                                    | true, s -> s
                                    | false, _ -> 0

                                scores[sym] <- prev + weight
                        | _ -> ()

        for expr in addTrue do
            scanExpr true expr

        for i = 0 to outerTrueLimit - 1 do
            scanExpr false outerTrue.Exprs[i]

        for i = 0 to outerFalseLimit - 1 do
            scanExpr false outerFalse.Exprs[i]

        for i = 0 to priorLimit - 1 do
            scanExpr false priors.Exprs[i]

        let mutable best = ValueNone
        let mutable bestScore = -1

        for kv in scores do
            if kv.Value > bestScore then
                bestScore <- kv.Value
                best <- ValueSome kv.Key

        best

    let private solveConstrainedCandidates
        (overrides: OverrideScope)
        (guardCaches: EnvGuardCacheRing)
        (memoResolver: Dictionary<string, bool> -> WitnessMemo)
        (fallbackState: FallbackConstraintState voption)
        (outerTrue: WatcherIndex)
        (outerTrueLimit: int)
        (outerFalse: WatcherIndex)
        (outerFalseLimit: int)
        (priors: WatcherIndex)
        (priorLimit: int)
        (addTrue: ExpressionSyntax list)
        (truncatedOut: bool ref)
        =
        let state =
            match fallbackState with
            | ValueSome s -> s
            | ValueNone -> FallbackConstraintState.Create()

        let mutable consistent = state.Consistent
        let mutable hasGuarded = state.HasGuarded

        if not state.OuterInit then
            state.OuterInit <- true

            for i = outerTrueLimit - 1 downto 0 do
                pushConstraintInto
                    overrides
                    state.Forced
                    null
                    state.Work
                    &consistent
                    &hasGuarded
                    true
                    outerTrue.Exprs[i]

            for i = outerFalseLimit - 1 downto 0 do
                pushConstraintInto
                    overrides
                    state.Forced
                    null
                    state.Work
                    &consistent
                    &hasGuarded
                    false
                    outerFalse.Exprs[i]

        let freeBuf = ResizeArray<string>(4)
        let seenBuf = HashSet<string>(StringComparer.Ordinal)

        let enqueueSmallWatchers
            (watchers: Dictionary<string, ResizeArray<struct (int * int)>>)
            (q: Queue<struct (int * int)>)
            (inQ: HashSet<struct (int * int)>)
            (sym: string)
            =
            if not (isNull watchers) then
                match watchers.TryGetValue sym with
                | false, _ -> ()
                | true, list ->
                    for wi = 0 to list.Count - 1 do
                        let item = list[wi]

                        if inQ.Add item then
                            q.Enqueue item

        let inspectSmallConstraint
            (primaryWatchers: Dictionary<string, ResizeArray<struct (int * int)>>)
            (extraWatchers: Dictionary<string, ResizeArray<struct (int * int)>>)
            (q: Queue<struct (int * int)>)
            (inQ: HashSet<struct (int * int)>)
            (addedOut: ResizeArray<string>)
            (recordWatchers: bool)
            (kind: int)
            (idx: int)
            (want: bool)
            (expr: ExpressionSyntax)
            =
            if tryCollectSmallFreeInto overrides state.Forced 4 freeBuf seenBuf expr then
                let n = freeBuf.Count
                let maskLimit = 1 <<< n
                let mutable satCount = 0
                let mutable andMask = maskLimit - 1
                let mutable orMask = 0

                for mask = 0 to maskLimit - 1 do
                    if evalSmallBoolExpr state.Forced freeBuf mask expr = want then
                        satCount <- satCount + 1
                        andMask <- andMask &&& mask
                        orMask <- orMask ||| mask

                if satCount = 0 then
                    false
                else
                    if n > 0 then
                        for bi = 0 to n - 1 do
                            let bit = 1 <<< bi
                            let sym = freeBuf[bi]

                            let forcedVal =
                                if (andMask &&& bit) <> 0 then ValueSome true
                                elif (orMask &&& bit) = 0 then ValueSome false
                                else ValueNone

                            match forcedVal with
                            | ValueSome v ->
                                if not (state.Forced.ContainsKey sym) then
                                    state.Forced[sym] <- v

                                    if not (isNull addedOut) then
                                        addedOut.Add sym

                                    enqueueSmallWatchers primaryWatchers q inQ sym
                                    enqueueSmallWatchers extraWatchers q inQ sym
                            | ValueNone ->
                                if recordWatchers then
                                    let targetWatchers =
                                        if isNull extraWatchers then
                                            primaryWatchers
                                        else
                                            extraWatchers

                                    match targetWatchers.TryGetValue sym with
                                    | true, list -> list.Add(struct (kind, idx))
                                    | false, _ ->
                                        let list = ResizeArray<struct (int * int)>(1)
                                        list.Add(struct (kind, idx))
                                        targetWatchers[sym] <- list

                    true
            else
                true

        while state.ProcessedPriors < priorLimit do
            let pExpr = priors.Exprs[state.ProcessedPriors]

            if consistent then
                let addedTarget =
                    if state.SmallOuterInit then
                        state.AddedKeys.Clear()
                        state.AddedKeys
                    else
                        null

                pushConstraintInto
                    overrides
                    state.Forced
                    addedTarget
                    state.Work
                    &consistent
                    &hasGuarded
                    false
                    pExpr

                if consistent && not (isNull addedTarget) && addedTarget.Count > 0 then
                    for ai = 0 to addedTarget.Count - 1 do
                        enqueueSmallWatchers
                            state.SmallWatchers
                            state.SmallPropQueue
                            state.SmallInPropQueue
                            addedTarget[ai]

                    addedTarget.Clear()

                if not (isNull (box pExpr)) then
                    if evalCondition overrides guardCaches Set.empty pExpr <> false then
                        state.UnsatOnEmptyPriors.Add state.ProcessedPriors
                    elif state.UnsatBaseReady && not (List.isEmpty state.UnsatBaseAcc) then
                        let surviving =
                            state.UnsatBaseAcc
                            |> List.filter (fun w ->
                                evalCondition overrides guardCaches (w.ToSet()) pExpr = false)

                        state.UnsatBaseAcc <- surviving

                        if List.isEmpty surviving && state.UnsatBaseCapped then
                            state.UnsatBaseReady <- false
                            state.UnsatBaseCapped <- false
                            state.UnsatStepped <- 0

            state.ProcessedPriors <- state.ProcessedPriors + 1

        state.Consistent <- consistent
        state.HasGuarded <- hasGuarded

        if state.Consistent then
            let mutable baseOk = true

            if not state.SmallOuterInit then
                state.SmallOuterInit <- true
                let mutable oi = outerTrueLimit - 1

                while baseOk && oi >= 0 do
                    baseOk <-
                        inspectSmallConstraint
                            state.SmallWatchers
                            null
                            state.SmallPropQueue
                            state.SmallInPropQueue
                            null
                            true
                            0
                            oi
                            true
                            outerTrue.Exprs[oi]

                    oi <- oi - 1

                let mutable ofi = outerFalseLimit - 1

                while baseOk && ofi >= 0 do
                    baseOk <-
                        inspectSmallConstraint
                            state.SmallWatchers
                            null
                            state.SmallPropQueue
                            state.SmallInPropQueue
                            null
                            true
                            1
                            ofi
                            false
                            outerFalse.Exprs[ofi]

                    ofi <- ofi - 1

            while baseOk && state.SmallProcessedPriors < priorLimit do
                let pi = state.SmallProcessedPriors

                baseOk <-
                    inspectSmallConstraint
                        state.SmallWatchers
                        null
                        state.SmallPropQueue
                        state.SmallInPropQueue
                        null
                        true
                        2
                        pi
                        false
                        priors.Exprs[pi]

                state.SmallProcessedPriors <- pi + 1

            while baseOk && state.SmallPropQueue.Count > 0 do
                let struct (kind, idx) as item = state.SmallPropQueue.Dequeue()
                state.SmallInPropQueue.Remove item |> ignore

                baseOk <-
                    match kind with
                    | 0 ->
                        inspectSmallConstraint
                            state.SmallWatchers
                            null
                            state.SmallPropQueue
                            state.SmallInPropQueue
                            null
                            false
                            0
                            idx
                            true
                            outerTrue.Exprs[idx]
                    | 1 ->
                        inspectSmallConstraint
                            state.SmallWatchers
                            null
                            state.SmallPropQueue
                            state.SmallInPropQueue
                            null
                            false
                            1
                            idx
                            false
                            outerFalse.Exprs[idx]
                    | _ ->
                        inspectSmallConstraint
                            state.SmallWatchers
                            null
                            state.SmallPropQueue
                            state.SmallInPropQueue
                            null
                            false
                            2
                            idx
                            false
                            priors.Exprs[idx]

            if not baseOk then
                state.Consistent <- false

        let stepAccCore
            (onDelta: (string -> unit) voption)
            (mCapped: bool ref)
            (mMemo: WitnessMemo)
            (curAcc: WitnessNode list)
            (want: bool)
            (expr: ExpressionSyntax)
            =
            if List.isEmpty curAcc then
                []
            else
                let sat = ResizeArray<WitnessNode>(curAcc.Length)
                let unsat = ResizeArray<WitnessNode>()

                for w in curAcc do
                    if evalCondition overrides guardCaches (w.ToSet()) expr = want then
                        sat.Add w
                    else
                        unsat.Add w

                if sat.Count > witnessLimit then
                    distinctBounded mCapped sat
                elif unsat.Count = 0 then
                    curAcc
                elif sat.Count = witnessLimit then
                    List.ofSeq sat
                else
                    let exprWitnesses = witnesses overrides state.Forced mCapped mMemo want expr

                    match onDelta with
                    | ValueSome notify ->
                        let unsatSets = ResizeArray<Set<string>>(unsat.Count)

                        for u in unsat do
                            unsatSets.Add(u.ToSet())

                        let notified = HashSet<string>(StringComparer.Ordinal)

                        for wExtra in exprWitnesses do
                            for s in wExtra.ToSet() do
                                if not (notified.Contains s) then
                                    let mutable missing = false
                                    let mutable ui = 0

                                    while not missing && ui < unsatSets.Count do
                                        if not (unsatSets[ui].Contains s) then
                                            missing <- true

                                        ui <- ui + 1

                                    if missing && notified.Add s then
                                        notify s
                    | ValueNone -> ()

                    let extended =
                        combineWitnesses mCapped (List.ofSeq unsat) exprWitnesses
                        |> List.filter (fun w ->
                            evalCondition overrides guardCaches (w.ToSet()) expr = want)

                    if sat.Count = 0 then
                        extended
                    else
                        for w in extended do
                            sat.Add w

                        distinctBounded mCapped sat

        let stepAcc = stepAccCore ValueNone

        let seedFromForced () =
            let mutable seed = emptyWitness

            for kv in state.Forced do
                if kv.Value then
                    seed <- joinWitness seed (WitnessNode(One kv.Key))

            seed

        if
            state.Consistent
            && state.UnsatOnEmptyPriors.Count > 0
            && state.UnsatStepped < state.UnsatOnEmptyPriors.Count
        then
            let baseSeed = seedFromForced ()

            if not state.UnsatBaseReady then
                state.UnsatBaseAcc <- [ baseSeed ]
                state.UnsatBaseReady <- true
            elif not (Set.isEmpty (baseSeed.ToSet())) && state.UnsatStepped > 0 then
                state.UnsatBaseAcc <-
                    state.UnsatBaseAcc |> List.map (fun w -> joinWitness baseSeed w)

            let baseMemo = memoResolver state.Forced

            let baseCapped = ref state.UnsatBaseCapped

            while state.UnsatStepped < state.UnsatOnEmptyPriors.Count
                  && not (List.isEmpty state.UnsatBaseAcc) do
                let pIdx = state.UnsatOnEmptyPriors[state.UnsatStepped]

                state.UnsatBaseAcc <-
                    stepAcc baseCapped baseMemo state.UnsatBaseAcc false priors.Exprs[pIdx]

                state.UnsatStepped <- state.UnsatStepped + 1

            state.UnsatBaseCapped <- baseCapped.Value

            if List.isEmpty state.UnsatBaseAcc && not state.UnsatBaseCapped then
                state.Consistent <- false

        if not state.Consistent then
            []
        else
            let savedConsistent = state.Consistent
            let savedHasGuarded = state.HasGuarded
            state.AddedKeys.Clear()

            try
                let mutable armConsistent = savedConsistent
                let mutable armHasGuarded = savedHasGuarded

                for expr in addTrue do
                    pushConstraintInto
                        overrides
                        state.Forced
                        state.AddedKeys
                        state.Work
                        &armConsistent
                        &armHasGuarded
                        true
                        expr

                let addTrueArr = Array.ofList addTrue

                let propagateSmallForcings () =
                    let localWatchers =
                        if addTrueArr.Length > 1 then
                            Dictionary<string, ResizeArray<struct (int * int)>>(
                                StringComparer.Ordinal
                            )
                        else
                            null

                    let propQueue = Queue<struct (int * int)>()
                    let inPropQueue = HashSet<struct (int * int)>()

                    for ai = 0 to state.AddedKeys.Count - 1 do
                        enqueueSmallWatchers
                            state.SmallWatchers
                            propQueue
                            inPropQueue
                            state.AddedKeys[ai]

                    let mutable cOk = true
                    let mutable i = 0

                    while cOk && i < addTrueArr.Length do
                        cOk <-
                            inspectSmallConstraint
                                state.SmallWatchers
                                localWatchers
                                propQueue
                                inPropQueue
                                state.AddedKeys
                                (addTrueArr.Length > 1)
                                3
                                i
                                true
                                addTrueArr[i]

                        i <- i + 1

                    while cOk && propQueue.Count > 0 do
                        let struct (kind, idx) as item = propQueue.Dequeue()
                        inPropQueue.Remove item |> ignore

                        cOk <-
                            match kind with
                            | 0 ->
                                inspectSmallConstraint
                                    state.SmallWatchers
                                    localWatchers
                                    propQueue
                                    inPropQueue
                                    state.AddedKeys
                                    false
                                    0
                                    idx
                                    true
                                    outerTrue.Exprs[idx]
                            | 1 ->
                                inspectSmallConstraint
                                    state.SmallWatchers
                                    localWatchers
                                    propQueue
                                    inPropQueue
                                    state.AddedKeys
                                    false
                                    1
                                    idx
                                    false
                                    outerFalse.Exprs[idx]
                            | 2 ->
                                inspectSmallConstraint
                                    state.SmallWatchers
                                    localWatchers
                                    propQueue
                                    inPropQueue
                                    state.AddedKeys
                                    false
                                    2
                                    idx
                                    false
                                    priors.Exprs[idx]
                            | _ ->
                                inspectSmallConstraint
                                    state.SmallWatchers
                                    localWatchers
                                    propQueue
                                    inPropQueue
                                    state.AddedKeys
                                    false
                                    3
                                    idx
                                    true
                                    addTrueArr[idx]

                    cOk

                if armConsistent then
                    armConsistent <- propagateSmallForcings ()

                if not armConsistent then
                    []
                else
                    let filterValid (cands: WitnessNode list) =
                        if List.isEmpty cands then
                            []
                        else
                            let kept = ResizeArray<WitnessNode>(cands.Length)
                            let seen = HashSet<WitnessNode>(witnessNodeComparer)

                            for w in cands do
                                let env = w.ToSet()

                                if
                                    evalConstraints
                                        overrides
                                        guardCaches
                                        priors
                                        priorLimit
                                        outerTrue
                                        outerTrueLimit
                                        outerFalse
                                        outerFalseLimit
                                        env
                                    && List.forall
                                        (fun expr -> evalCondition overrides guardCaches env expr)
                                        addTrue
                                    && seen.Add w
                                then
                                    kept.Add w

                            List.ofSeq kept

                    let runWithUnsatBase (directUnsat: bool) : struct (WitnessNode list * bool) =
                        let localMemo = memoResolver state.Forced
                        let localCapped = ref false
                        let seed = seedFromForced ()
                        let mutable acc = [ seed ]

                        for expr in addTrue do
                            if not (List.isEmpty acc) then
                                acc <- stepAcc localCapped localMemo acc true expr

                        let mutable oi = 0

                        while not (List.isEmpty acc) && oi < outerTrueLimit do
                            acc <- stepAcc localCapped localMemo acc true outerTrue.Exprs[oi]
                            oi <- oi + 1

                        let mutable ofi = 0

                        while not (List.isEmpty acc) && ofi < outerFalseLimit do
                            acc <- stepAcc localCapped localMemo acc false outerFalse.Exprs[ofi]
                            ofi <- ofi + 1

                        if not (List.isEmpty acc) && state.UnsatOnEmptyPriors.Count > 0 then
                            if
                                not directUnsat
                                && state.UnsatBaseReady
                                && not (List.isEmpty state.UnsatBaseAcc)
                            then
                                if state.UnsatOnEmptyPriors.Count <= 16 then
                                    let alreadySat = ResizeArray<WitnessNode>(acc.Length)
                                    let needUnsat = ResizeArray<WitnessNode>()

                                    for w in acc do
                                        let env = w.ToSet()
                                        let mutable ok = true
                                        let mutable ui = 0

                                        while ok && ui < state.UnsatOnEmptyPriors.Count do
                                            let pIdx = state.UnsatOnEmptyPriors[ui]

                                            if
                                                evalCondition
                                                    overrides
                                                    guardCaches
                                                    env
                                                    priors.Exprs[pIdx]
                                                <> false
                                            then
                                                ok <- false

                                            ui <- ui + 1

                                        if ok then alreadySat.Add w else needUnsat.Add w

                                    if needUnsat.Count > 0 then
                                        let combined =
                                            combineWitnesses
                                                localCapped
                                                (List.ofSeq needUnsat)
                                                state.UnsatBaseAcc

                                        for w in combined do
                                            alreadySat.Add w

                                    acc <- distinctBounded localCapped alreadySat
                                else
                                    acc <- combineWitnesses localCapped acc state.UnsatBaseAcc
                            else
                                for ui = 0 to state.UnsatOnEmptyPriors.Count - 1 do
                                    let pIdx = state.UnsatOnEmptyPriors[ui]

                                    acc <-
                                        stepAcc localCapped localMemo acc false priors.Exprs[pIdx]

                        if not (List.isEmpty acc) && priorLimit > 0 then
                            let stepped = HashSet<int>()
                            let failing = ResizeArray<int>()
                            let mutable checking = true

                            while checking && not (List.isEmpty acc) do
                                failing.Clear()

                                for w in acc do
                                    priors.CollectFailing(
                                        overrides,
                                        guardCaches,
                                        priorLimit,
                                        false,
                                        (w.ToSet()),
                                        stepped,
                                        failing
                                    )

                                if failing.Count = 0 then
                                    checking <- false
                                else
                                    for fi = 0 to failing.Count - 1 do
                                        acc <-
                                            stepAcc
                                                localCapped
                                                localMemo
                                                acc
                                                false
                                                priors.Exprs[failing[fi]]

                        let mutable kept = filterValid acc

                        if List.isEmpty kept && not (List.isEmpty acc) then
                            let dirtyQueue = Queue<string>()
                            let inDirtyQueue = HashSet<string>(StringComparer.Ordinal)

                            let enqueueSym (s: string) =
                                if not (String.IsNullOrEmpty s) && inDirtyQueue.Add s then
                                    dirtyQueue.Enqueue s

                            let onDelta = ValueSome enqueueSym

                            for w in acc do
                                for s in w.ToSet() do
                                    enqueueSym s

                            let stateBuckets = Dictionary<uint64, ResizeArray<WitnessNode list>>()

                            let tryRecordState (cands: WitnessNode list) =
                                let mutable h = uint64 cands.Length * 0x9e3779b97f4a7c15UL

                                for w in cands do
                                    ignore (w.ToSet())
                                    let x = w.CachedHash64 * 0xbf58476d1ce4e5b9UL
                                    h <- h ^^^ (x ^^^ (x >>> 31))

                                match stateBuckets.TryGetValue h with
                                | false, _ ->
                                    let bucket = ResizeArray<WitnessNode list>(1)
                                    bucket.Add cands
                                    stateBuckets[h] <- bucket
                                    true
                                | true, bucket ->
                                    let mutable dup = false
                                    let mutable bi = 0

                                    while not dup && bi < bucket.Count do
                                        let prev = bucket[bi]

                                        if
                                            prev.Length = cands.Length
                                            && prev
                                               |> List.forall (fun pw ->
                                                   cands
                                                   |> List.exists (fun cw ->
                                                       witnessNodeComparer.Equals(pw, cw)))
                                            && cands
                                               |> List.forall (fun cw ->
                                                   prev
                                                   |> List.exists (fun pw ->
                                                       witnessNodeComparer.Equals(cw, pw)))
                                        then
                                            dup <- true

                                        bi <- bi + 1

                                    if dup then
                                        false
                                    else
                                        bucket.Add cands
                                        true

                            ignore (tryRecordState acc)

                            let repairExpr (want: bool) (expr: ExpressionSyntax) =
                                if not (List.isEmpty acc) then
                                    let mutable anyFail = false

                                    for w in acc do
                                        if
                                            not anyFail
                                            && evalCondition overrides guardCaches (w.ToSet()) expr
                                               <> want
                                        then
                                            anyFail <- true

                                    if anyFail then
                                        acc <-
                                            stepAccCore onDelta localCapped localMemo acc want expr

                            let checkAlwaysList (wIdx: WatcherIndex) (limit: int) (want: bool) =
                                let mutable k = 0

                                while not (List.isEmpty acc)
                                      && k < wIdx.Always.Count
                                      && wIdx.Always[k] < limit do
                                    repairExpr want wIdx.Exprs[wIdx.Always[k]]
                                    k <- k + 1

                            let checkWatchersForSym
                                (wIdx: WatcherIndex)
                                (limit: int)
                                (want: bool)
                                (sym: string)
                                =
                                if limit > 0 && not (List.isEmpty acc) then
                                    match wIdx.Watchers.TryGetValue sym with
                                    | false, _ -> ()
                                    | true, indices ->
                                        let mutable m = 0

                                        while not (List.isEmpty acc)
                                              && m < indices.Count
                                              && indices[m] < limit do
                                            repairExpr want wIdx.Exprs[indices[m]]
                                            m <- m + 1

                            let checkAlwaysAndTargets () =
                                checkAlwaysList outerTrue outerTrueLimit true
                                checkAlwaysList outerFalse outerFalseLimit false
                                checkAlwaysList priors priorLimit false

                                for expr in addTrue do
                                    repairExpr true expr

                            let maxRepairSteps =
                                max
                                    4096
                                    ((outerTrueLimit + outerFalseLimit + priorLimit + addTrue.Length)
                                     * 8)

                            let mutable repairSteps = 0
                            let mutable cycling = false
                            let prevAlways = acc
                            checkAlwaysAndTargets ()

                            if
                                not (obj.ReferenceEquals(prevAlways, acc)) && not (List.isEmpty acc)
                            then
                                repairSteps <- repairSteps + 1

                                if not (tryRecordState acc) then
                                    cycling <- true

                            while not (List.isEmpty acc)
                                  && not cycling
                                  && repairSteps < maxRepairSteps
                                  && dirtyQueue.Count > 0 do
                                while not (List.isEmpty acc)
                                      && not cycling
                                      && repairSteps < maxRepairSteps
                                      && dirtyQueue.Count > 0 do
                                    let sym = dirtyQueue.Dequeue()
                                    inDirtyQueue.Remove sym |> ignore
                                    let prevAcc = acc
                                    checkWatchersForSym outerTrue outerTrueLimit true sym
                                    checkWatchersForSym outerFalse outerFalseLimit false sym
                                    checkWatchersForSym priors priorLimit false sym

                                    if
                                        not (obj.ReferenceEquals(prevAcc, acc))
                                        && not (List.isEmpty acc)
                                    then
                                        repairSteps <- repairSteps + 1

                                        if not (tryRecordState acc) then
                                            cycling <- true

                                if
                                    not (List.isEmpty acc)
                                    && not cycling
                                    && repairSteps < maxRepairSteps
                                then
                                    let prevAcc = acc
                                    checkAlwaysAndTargets ()

                                    if
                                        not (obj.ReferenceEquals(prevAcc, acc))
                                        && not (List.isEmpty acc)
                                    then
                                        repairSteps <- repairSteps + 1

                                        if not (tryRecordState acc) then
                                            cycling <- true

                            if repairSteps >= maxRepairSteps then
                                localCapped.Value <- true

                            kept <- filterValid acc

                        struct (kept, localCapped.Value)

                    let solveCurrent (allowUnsatBase: bool) =
                        let struct (solved, capped1) = runWithUnsatBase (not allowUnsatBase)

                        if not (List.isEmpty solved) then
                            struct (solved, capped1)
                        elif allowUnsatBase && state.UnsatOnEmptyPriors.Count > 0 then
                            let struct (solved2, capped2) = runWithUnsatBase true
                            struct (solved2, capped1 || capped2)
                        else
                            struct (solved, capped1)

                    let rec solveSplit (depth: int) (leavesLeft: int ref) =
                        if leavesLeft.Value <= 0 then
                            struct ([], true)
                        else
                            leavesLeft.Value <- leavesLeft.Value - 1
                            let struct (directSolved, directCapped) = solveCurrent (depth = 0)

                            if
                                not (List.isEmpty directSolved) || not directCapped || depth >= 4
                            then
                                struct (directSolved, directCapped)
                            else
                                match
                                    tryPickSplitSymbol
                                        overrides
                                        state.Forced
                                        addTrue
                                        outerTrue
                                        outerTrueLimit
                                        outerFalse
                                        outerFalseLimit
                                        priors
                                        priorLimit
                                with
                                | ValueNone -> struct ([], directCapped)
                                | ValueSome splitSym ->
                                    let probeVal (v: bool) =
                                        let savedCount = state.AddedKeys.Count

                                        try
                                            state.Forced[splitSym] <- v
                                            state.AddedKeys.Add splitSym

                                            if propagateSmallForcings () then
                                                solveSplit (depth + 1) leavesLeft
                                            else
                                                struct ([], false)
                                        finally
                                            while state.AddedKeys.Count > savedCount do
                                                let lastIdx = state.AddedKeys.Count - 1

                                                state.Forced.Remove state.AddedKeys[lastIdx]
                                                |> ignore

                                                state.AddedKeys.RemoveAt lastIdx

                                    let struct (tSolved, tCapped) = probeVal true
                                    let struct (fSolved, fCapped) = probeVal false

                                    if List.isEmpty tSolved && List.isEmpty fSolved then
                                        struct ([], tCapped || fCapped || directCapped)
                                    else
                                        let combinedCap = ref false

                                        let combined =
                                            distinctBounded combinedCap (Seq.append tSolved fSolved)

                                        struct (combined, false)

                    let struct (finalSolved, finalCapped) = solveSplit 0 (ref 16)

                    if List.isEmpty finalSolved && finalCapped then
                        truncatedOut.Value <- true

                    finalSolved
            finally
                for i = 0 to state.AddedKeys.Count - 1 do
                    state.Forced.Remove state.AddedKeys[i] |> ignore

                state.AddedKeys.Clear()
                state.Consistent <- savedConsistent
                state.HasGuarded <- savedHasGuarded

    let private discoverBranchConfigs
        (shouldStop: unit -> bool)
        (canAcceptAlternate: unit -> bool)
        (discoveryCapped: bool ref)
        (roots: SyntaxNode list)
        (enqueueBranch: bool -> string array -> unit)
        (enqueueSingleton: string -> unit)
        =
        let toConfig (symbols: Set<string>) =
            let arr = symbols |> Set.toArray
            Array.Sort(arr, StringComparer.Ordinal)
            arr

        let enqueueSolved (candidates: WitnessNode list) =
            if not (shouldStop ()) && not (List.isEmpty candidates) then
                if canAcceptAlternate () then
                    if List.isEmpty candidates.Tail then
                        enqueueBranch true (toConfig (candidates.Head.ToSet()))
                    else
                        let sets =
                            candidates |> List.map (fun w -> w.ToSet()) |> List.sortBy Set.count

                        let mutable isPrimary = true

                        for candidate in sets do
                            if not (shouldStop ()) && (isPrimary || canAcceptAlternate ()) then
                                enqueueBranch isPrimary (toConfig candidate)
                                isPrimary <- false
                else
                    let mutable best = candidates.Head.ToSet()

                    for w in candidates.Tail do
                        let s = w.ToSet()

                        if s.Count < best.Count then
                            best <- s

                    enqueueBranch true (toConfig best)

        use rootEnum = (roots :> seq<SyntaxNode>).GetEnumerator()

        while not (shouldStop ()) && rootEnum.MoveNext() do
            let root = rootEnum.Current

            if root.ContainsDirectives then
                let memo = WitnessMemo.Create()

                let mutable memoDirty = false
                let mutable overrideEpoch = 0
                let fallbackMemos = Dictionary<string, WitnessMemo>(StringComparer.Ordinal)
                let fallbackScratch = WitnessMemo.Create()
                fallbackScratch.UnforcedPeer <- ValueSome memo
                let mutable fallbackScratchKey = ""

                let overrideScope = OverrideScope()
                let localOverrides = overrideScope.History

                let topConstGuardCache = ConstScopeCache()

                let firstSymbolPos = Dictionary<string, int>(StringComparer.Ordinal)

                let exprSymbolWork = Stack<ExpressionSyntax>()

                let recordExprSymbols (expr: ExpressionSyntax) =
                    if not (isNull (box expr)) then
                        exprSymbolWork.Clear()
                        exprSymbolWork.Push expr

                        while exprSymbolWork.Count > 0 do
                            let cur = exprSymbolWork.Pop()

                            if not (isNull (box cur)) then
                                match cur with
                                | :? IdentifierNameSyntax as ident ->
                                    let sym = preprocessorSymbolName ident.Identifier

                                    if not (String.IsNullOrEmpty sym) then
                                        let pos = ident.SpanStart

                                        match firstSymbolPos.TryGetValue sym with
                                        | true, existing when existing <= pos -> ()
                                        | _ -> firstSymbolPos[sym] <- pos
                                | :? ParenthesizedExpressionSyntax as p ->
                                    exprSymbolWork.Push p.Expression
                                | :? PrefixUnaryExpressionSyntax as u when
                                    u.IsKind SyntaxKind.LogicalNotExpression
                                    ->
                                    exprSymbolWork.Push u.Operand
                                | :? BinaryExpressionSyntax as b ->
                                    match b.Kind() with
                                    | SyntaxKind.LogicalAndExpression
                                    | SyntaxKind.LogicalOrExpression
                                    | SyntaxKind.EqualsExpression
                                    | SyntaxKind.NotEqualsExpression ->
                                        exprSymbolWork.Push b.Right
                                        exprSymbolWork.Push b.Left
                                    | _ -> ()
                                | _ -> ()

                let overrideKeysAtDepth = ResizeArray<struct (int * string)>()
                let rootCapped = ref false
                let stack = ResizeArray<ConditionalFrame>()
                let activeTrue = WatcherIndex.Create()
                let activeFalse = WatcherIndex.Create()
                let resolvedCandidates = ResizeArray<WitnessNode list>()
                resolvedCandidates.Add [ emptyWitness ]

                let mutable topEvalGuardCaches: EnvGuardCacheRing = null

                let scopeCachesFor (depth: int) =
                    if depth <= 0 then
                        if isNull topEvalGuardCaches then
                            topEvalGuardCaches <- EnvGuardCacheRing firstSymbolPos

                        topEvalGuardCaches
                    else
                        stack[depth - 1].EnsureEvalCaches firstSymbolPos

                let scopeConstGuardCacheFor (depth: int) =
                    if depth <= 0 then
                        topConstGuardCache
                    else
                        stack[depth - 1].EnsureConstGuardCache()

                let activeOverrides () =
                    if memoDirty then
                        memo.ClearTemp()
                        memoDirty <- false
                        overrideEpoch <- overrideEpoch + 1

                    if overrideScope.HasAny then overrideScope else null

                let resolveFallbackMemo (forced: Dictionary<string, bool>) =
                    if isNull forced || forced.Count = 0 then
                        memo
                    else
                        let canonicalKey =
                            if forced.Count = 1 then
                                use e =
                                    (forced :> IEnumerable<KeyValuePair<string, bool>>)
                                        .GetEnumerator()

                                if e.MoveNext() then
                                    if e.Current.Value then
                                        e.Current.Key + "=1"
                                    else
                                        e.Current.Key + "=0"
                                else
                                    ""
                            else
                                let parts = ResizeArray<string>(forced.Count)

                                for kv in forced do
                                    parts.Add(if kv.Value then kv.Key + "=1" else kv.Key + "=0")

                                parts.Sort(StringComparer.Ordinal)
                                String.Join("\u0000", parts)

                        let mutable minPos = Int32.MaxValue

                        for kv in forced do
                            match firstSymbolPos.TryGetValue kv.Key with
                            | true, p ->
                                if p < minPos then
                                    minPos <- p
                            | false, _ -> minPos <- -1

                        let targetMemo =
                            match fallbackMemos.TryGetValue canonicalKey with
                            | true, m ->
                                if m.OverrideEpoch <> overrideEpoch then
                                    m.ClearTemp()
                                    m.OverrideEpoch <- overrideEpoch

                                m
                            | false, _ ->
                                if fallbackMemos.Count < 64 then
                                    let m = WitnessMemo.Create()
                                    m.OverrideEpoch <- overrideEpoch
                                    m.UnforcedPeer <- ValueSome memo
                                    fallbackMemos[canonicalKey] <- m
                                    m
                                else
                                    if
                                        not (
                                            StringComparer.Ordinal.Equals(
                                                fallbackScratchKey,
                                                canonicalKey
                                            )
                                        )
                                    then
                                        fallbackScratch.ResetAll()
                                        fallbackScratchKey <- canonicalKey
                                        fallbackScratch.OverrideEpoch <- overrideEpoch
                                    elif fallbackScratch.OverrideEpoch <> overrideEpoch then
                                        fallbackScratch.ClearTemp()
                                        fallbackScratch.OverrideEpoch <- overrideEpoch

                                    fallbackScratch

                        targetMemo.UnforcedBeforePos <- minPos
                        targetMemo

                let truncateResolved (keepCount: int) =
                    if resolvedCandidates.Count > keepCount then
                        resolvedCandidates.RemoveRange(
                            keepCount,
                            resolvedCandidates.Count - keepCount
                        )

                let advanceNegated
                    (frameIdx: int)
                    (baseCandidates: WitnessNode list)
                    (frame: ConditionalFrame)
                    (targetCount: int)
                    =
                    let ov = activeOverrides ()
                    let caches = scopeCachesFor frameIdx

                    if not frame.NegatedReady then
                        frame.NegatedCandidates <- baseCandidates
                        frame.NegatedCount <- 0
                        frame.NegatedReady <- true

                    while frame.NegatedCount < targetCount
                          && not (List.isEmpty frame.NegatedCandidates) do
                        let idx = frame.NegatedCount

                        frame.NegatedCandidates <-
                            extendCandidates
                                ov
                                caches
                                rootCapped
                                memo
                                frame.NegatedCandidates
                                []
                                [ frame.Priors.Exprs[idx] ]
                                frame.Priors
                                idx
                                activeTrue
                                frame.SavedTrueCount
                                activeFalse
                                frame.SavedFalseCount

                        frame.NegatedCount <- idx + 1

                    frame.NegatedCandidates

                let ensureResolved (depth: int) =
                    while resolvedCandidates.Count <= depth do
                        let idx = resolvedCandidates.Count - 1
                        let frame = stack[idx]
                        let baseCands = resolvedCandidates[idx]

                        let negCands =
                            if frame.TakenPriorCount > 0 then
                                advanceNegated idx baseCands frame frame.TakenPriorCount
                            else
                                baseCands

                        let ov = activeOverrides ()
                        let caches = scopeCachesFor idx

                        let nextCands =
                            match frame.TakenTrue with
                            | ValueSome expr ->
                                extendCandidates
                                    ov
                                    caches
                                    rootCapped
                                    memo
                                    negCands
                                    [ expr ]
                                    []
                                    frame.Priors
                                    frame.TakenPriorCount
                                    activeTrue
                                    frame.SavedTrueCount
                                    activeFalse
                                    frame.SavedFalseCount
                            | ValueNone -> negCands

                        resolvedCandidates.Add nextCands

                    resolvedCandidates[depth]

                let pushOverrideEntry (sym: string) (entry: OverrideEntry) =
                    match localOverrides.TryGetValue sym with
                    | true, history ->
                        let maxPos =
                            match history with
                            | [] -> entry.Pos
                            | h :: _ -> max entry.Pos h.MaxPos

                        localOverrides[sym] <- { entry with MaxPos = maxPos } :: history
                    | false, _ -> localOverrides[sym] <- [ { entry with MaxPos = entry.Pos } ]

                    if entry.Depth > 0 then
                        overrideKeysAtDepth.Add(struct (entry.Depth, sym))

                    memoDirty <- true

                let ensureArmNode (frameIdx: int) =
                    let frame = stack[frameIdx]

                    if isNull frame.ArmNode then
                        frame.ArmNode <- GuardNode(Array.empty, Array.empty, null, false)

                    frame.ArmNode

                let recordLocalOverride (sym: string) (value: bool) (pos: int) =
                    let depth = stack.Count

                    let guard =
                        if depth > 0 then
                            ensureResolved depth |> ignore
                            ensureArmNode (depth - 1)
                        else
                            null

                    pushOverrideEntry
                        sym
                        {
                            Defined = value
                            Pos = pos
                            MaxPos = pos
                            Depth = depth
                            Guard = guard
                        }

                let localCheckForced = Dictionary<string, bool>(StringComparer.Ordinal)
                let localCheckWork = Stack<struct (bool * ExpressionSyntax)>()

                let isConditionLocallyImpossible (ov: OverrideScope) (cond: ExpressionSyntax) =
                    if isNull (box cond) then
                        true
                    else
                        localCheckForced.Clear()
                        let mutable ok = true
                        let mutable guarded = false

                        pushConstraintInto
                            ov
                            localCheckForced
                            null
                            localCheckWork
                            &ok
                            &guarded
                            true
                            cond

                        not ok

                let popGuardSliceRange
                    (exprs: ResizeArray<ExpressionSyntax>)
                    (startCount: int)
                    (endCount: int)
                    =
                    let count = endCount - startCount

                    if count <= 0 then
                        Array.empty
                    else
                        let arr = Array.zeroCreate<ExpressionSyntax> count

                        for i = 0 to count - 1 do
                            arr[i] <- exprs[startCount + i]

                        arr

                let popGuardSlice (exprs: ResizeArray<ExpressionSyntax>) (startCount: int) =
                    popGuardSliceRange exprs startCount exprs.Count

                let promoteOverridesFrom (frameDepth: int) =
                    if frameDepth > 0 && overrideKeysAtDepth.Count > 0 then
                        let targetDepth = frameDepth - 1
                        let mutable i = overrideKeysAtDepth.Count - 1

                        while i >= 0
                              && (let struct (d, _) = overrideKeysAtDepth[i] in d >= frameDepth) do
                            let struct (_, sym) = overrideKeysAtDepth[i]

                            if targetDepth = 0 then
                                overrideKeysAtDepth.RemoveAt i
                            else
                                overrideKeysAtDepth[i] <- struct (targetDepth, sym)

                            i <- i - 1

                let popOverridesAtDepth (frameDepth: int) =
                    let popped = ResizeArray<struct (string * OverrideEntry)>()

                    while overrideKeysAtDepth.Count > 0
                          && (let struct (d, _) = overrideKeysAtDepth[overrideKeysAtDepth.Count - 1] in

                              d >= frameDepth) do
                        let idx = overrideKeysAtDepth.Count - 1
                        let struct (_, sym) = overrideKeysAtDepth[idx]
                        overrideKeysAtDepth.RemoveAt idx

                        match localOverrides.TryGetValue sym with
                        | true, entry :: tail ->
                            match tail with
                            | [] -> localOverrides.Remove sym |> ignore
                            | rest -> localOverrides[sym] <- rest

                            popped.Add(struct (sym, { entry with Depth = frameDepth - 1 }))
                        | _ -> ()

                    popped

                let closeArmOverrides
                    (frame: ConditionalFrame)
                    (frameDepth: int)
                    (stashToPending: bool)
                    =
                    if not (isNull frame.ArmNode) then
                        let baseParent =
                            if frameDepth > 1 then
                                ensureArmNode (frameDepth - 2)
                            else
                                null

                        if frame.FrameUnconditional then
                            frame.ArmNode.Seal(Array.empty, Array.empty, baseParent)
                        else
                            let guardTrue = popGuardSlice activeTrue.Exprs frame.SavedTrueCount

                            let priorEnd =
                                min
                                    activeFalse.Count
                                    (frame.SavedFalseCount + frame.ActiveFalseAddedCount)

                            let syncedEnd =
                                min priorEnd (frame.SavedFalseCount + frame.PriorNegSyncCount)

                            let priorParent =
                                if syncedEnd < priorEnd then
                                    let deltaFalse =
                                        popGuardSliceRange activeFalse.Exprs syncedEnd priorEnd

                                    let prevParent =
                                        if isNull frame.PriorNegNode then
                                            baseParent
                                        else
                                            frame.PriorNegNode

                                    let negNode = GuardNode(Array.empty, Array.empty, null, false)
                                    negNode.Seal(Array.empty, deltaFalse, prevParent)
                                    frame.PriorNegNode <- negNode
                                    frame.PriorNegSyncCount <- priorEnd - frame.SavedFalseCount
                                    negNode
                                elif not (isNull frame.PriorNegNode) then
                                    frame.PriorNegNode
                                else
                                    baseParent

                            frame.ArmNode.Seal(guardTrue, Array.empty, priorParent)

                        frame.ArmNode <- null
                        memoDirty <- true

                    let hasAtDepth =
                        overrideKeysAtDepth.Count > 0
                        && (let struct (d, _) = overrideKeysAtDepth[overrideKeysAtDepth.Count - 1] in
                            d >= frameDepth)

                    if stashToPending then
                        if hasAtDepth then
                            let popped = popOverridesAtDepth frameDepth

                            if popped.Count > 0 then
                                if isNull frame.PendingGuarded then
                                    frame.PendingGuarded <- ResizeArray()

                                for i = popped.Count - 1 downto 0 do
                                    frame.PendingGuarded.Add popped[i]

                            memoDirty <- true
                    elif isNull frame.PendingGuarded then
                        if hasAtDepth then
                            promoteOverridesFrom frameDepth
                    else
                        if hasAtDepth then
                            let popped = popOverridesAtDepth frameDepth

                            for i = 0 to frame.PendingGuarded.Count - 1 do
                                let struct (sym, entry) = frame.PendingGuarded[i]
                                pushOverrideEntry sym entry

                            for i = popped.Count - 1 downto 0 do
                                let struct (sym, entry) = popped[i]
                                pushOverrideEntry sym entry
                        else
                            for i = 0 to frame.PendingGuarded.Count - 1 do
                                let struct (sym, entry) = frame.PendingGuarded[i]
                                pushOverrideEntry sym entry

                        memoDirty <- true

                let restoreActive (frame: ConditionalFrame) =
                    activeTrue.TruncateTo frame.SavedTrueCount
                    activeFalse.TruncateTo frame.SavedFalseCount

                let restoreActiveArm (frame: ConditionalFrame) =
                    activeTrue.TruncateTo frame.SavedTrueCount
                    activeFalse.TruncateTo(frame.SavedFalseCount + frame.ActiveFalseAddedCount)

                let syncActiveFalse (ov: OverrideScope) (frame: ConditionalFrame) =
                    while frame.ActiveFalseAddedCount < frame.Priors.Count do
                        activeFalse.Add(ov, false, frame.Priors.Exprs[frame.ActiveFalseAddedCount])
                        frame.ActiveFalseAddedCount <- frame.ActiveFalseAddedCount + 1

                let finishSolved
                    (ov: OverrideScope)
                    (caches: EnvGuardCacheRing)
                    (fallbackState: FallbackConstraintState voption)
                    (branchTruncated: bool)
                    (found: WitnessNode list)
                    (priors: WatcherIndex)
                    (priorLimit: int)
                    (savedTrueCount: int)
                    (savedFalseCount: int)
                    (trueTargets: ExpressionSyntax list)
                    =
                    let mutable solveCapped = false

                    let solved =
                        if List.isEmpty found then
                            let capRef = ref false

                            let res =
                                solveConstrainedCandidates
                                    ov
                                    caches
                                    resolveFallbackMemo
                                    fallbackState
                                    activeTrue
                                    savedTrueCount
                                    activeFalse
                                    savedFalseCount
                                    priors
                                    priorLimit
                                    trueTargets
                                    capRef

                            solveCapped <- capRef.Value
                            res
                        else
                            found

                    if List.isEmpty solved && (branchTruncated || solveCapped) then
                        discoveryCapped.Value <- true

                    enqueueSolved solved

                let handleDefineOrUndef
                    (isDefine: bool)
                    (name: SyntaxToken)
                    (isActive: bool)
                    (pos: int)
                    =
                    let sym = preprocessorSymbolName name

                    if not (String.IsNullOrEmpty sym) then
                        if stack.Count > 0 then
                            let fIdx = stack.Count - 1
                            let frame = stack[fIdx]
                            let encImpossible = fIdx > 0 && stack[fIdx - 1].ArmImpossible

                            if not encImpossible && not frame.AnyPriorConstTrue then
                                frame.SetSiblingOverride(sym, isDefine)

                            if not frame.ArmImpossible then
                                recordLocalOverride sym isDefine pos
                        elif isActive then
                            recordLocalOverride sym isDefine pos

                use triviaEnum = (root.DescendantTrivia(descendIntoTrivia = true)).GetEnumerator()

                while not (shouldStop ()) && triviaEnum.MoveNext() do
                    let trivia = triviaEnum.Current

                    match trivia.GetStructure() with
                    | :? DefineDirectiveTriviaSyntax as directive ->
                        handleDefineOrUndef true directive.Name directive.IsActive trivia.SpanStart
                    | :? UndefDirectiveTriviaSyntax as directive ->
                        handleDefineOrUndef false directive.Name directive.IsActive trivia.SpanStart
                    | :? IfDirectiveTriviaSyntax as directive ->
                        recordExprSymbols directive.Condition
                        let depth = stack.Count
                        let savedTrue = activeTrue.Count
                        let savedFalse = activeFalse.Count
                        let enclosingImpossible = depth > 0 && stack[depth - 1].ArmImpossible
                        let ov = activeOverrides ()

                        let condConst =
                            if isNull directive.Condition then
                                ValueSome false
                            else
                                tryConstEvalCondition
                                    ov
                                    (scopeConstGuardCacheFor depth)
                                    directive.Condition

                        let armImpossible =
                            enclosingImpossible
                            || condConst = ValueSome false
                            || (not directive.BranchTaken
                                && isConditionLocallyImpossible ov directive.Condition)

                        if
                            not armImpossible
                            && not directive.BranchTaken
                            && not (isNull directive.Condition)
                        then
                            let baseCands = ensureResolved depth
                            let caches = scopeCachesFor depth
                            let branchCapped = ref rootCapped.Value

                            let found =
                                if List.isEmpty baseCands then
                                    []
                                else
                                    extendCandidates
                                        ov
                                        caches
                                        branchCapped
                                        memo
                                        baseCands
                                        [ directive.Condition ]
                                        []
                                        (WatcherIndex.Create())
                                        0
                                        activeTrue
                                        activeTrue.Count
                                        activeFalse
                                        activeFalse.Count

                            finishSolved
                                ov
                                caches
                                ValueNone
                                branchCapped.Value
                                found
                                (WatcherIndex.Create())
                                0
                                activeTrue.Count
                                activeFalse.Count
                                [ directive.Condition ]

                        let priors = WatcherIndex.Create()
                        let mutable takenTrue = ValueNone

                        if not (isNull directive.Condition) then
                            priors.Add(ov, false, directive.Condition)

                            if condConst <> ValueSome true then
                                takenTrue <- ValueSome directive.Condition
                                activeTrue.Add(ov, true, directive.Condition)

                        stack.Add
                            {
                                Priors = priors
                                SavedTrueCount = savedTrue
                                SavedFalseCount = savedFalse
                                ActiveFalseAddedCount = 0
                                TakenTrue = takenTrue
                                TakenPriorCount = 0
                                NegatedReady = false
                                NegatedCount = 0
                                NegatedCandidates = []
                                FrameUnconditional =
                                    directive.BranchTaken && condConst = ValueSome true
                                PriorsAllConstFalse = condConst = ValueSome false
                                AnyPriorConstTrue = condConst = ValueSome true
                                ArmImpossible = armImpossible
                                ArmNode = null
                                PriorNegNode = null
                                PriorNegSyncCount = 0
                                PendingGuarded = null
                                EvalCaches = null
                                ConstGuardCache = null
                                SeenPriors = null
                                SiblingOverrides = null
                                FallbackState = ValueNone
                            }
                    | :? ElifDirectiveTriviaSyntax as directive ->
                        recordExprSymbols directive.Condition

                        if stack.Count > 0 then
                            let frameIdx = stack.Count - 1
                            let frame = stack[frameIdx]
                            frame.EvalCaches <- null
                            frame.ConstGuardCache <- null
                            let siblingOv = frame.TakeSiblingOverrides()

                            if not frame.FrameUnconditional then
                                closeArmOverrides frame (frameIdx + 1) true

                            truncateResolved (frameIdx + 1)
                            restoreActiveArm frame

                            let enclosingImpossible =
                                frameIdx > 0 && stack[frameIdx - 1].ArmImpossible

                            let cond = directive.Condition
                            let usesSiblingOv = exprMentionsAnySymbol siblingOv cond

                            if usesSiblingOv then
                                let cStart = cond.SpanStart
                                let cEnd = cond.Span.End

                                for kv in siblingOv do
                                    overrideScope.AddWindow(kv.Key, cStart, cEnd, kv.Value)

                            let ov = activeOverrides ()
                            let seenPriors = frame.EnsureSeenPriors()

                            let condDuplicate =
                                not usesSiblingOv
                                && not (isNull (box cond))
                                && not (seenPriors.Add cond)

                            let condConst =
                                if isNull (box cond) then
                                    ValueSome false
                                elif condDuplicate then
                                    ValueNone
                                else
                                    tryConstEvalCondition ov (scopeConstGuardCacheFor frameIdx) cond

                            let armImpossible =
                                enclosingImpossible
                                || frame.AnyPriorConstTrue
                                || condDuplicate
                                || condConst = ValueSome false
                                || (not directive.BranchTaken
                                    && isConditionLocallyImpossible ov cond)

                            if
                                not armImpossible
                                && not directive.BranchTaken
                                && not (isNull (box cond))
                            then
                                let baseCands = ensureResolved frameIdx
                                let caches = scopeCachesFor frameIdx

                                let baseNeg =
                                    if List.isEmpty baseCands then
                                        []
                                    else
                                        advanceNegated frameIdx baseCands frame frame.Priors.Count

                                let branchCapped = ref rootCapped.Value

                                let found =
                                    if List.isEmpty baseNeg then
                                        []
                                    else
                                        extendCandidates
                                            ov
                                            caches
                                            branchCapped
                                            memo
                                            baseNeg
                                            [ cond ]
                                            []
                                            frame.Priors
                                            frame.Priors.Count
                                            activeTrue
                                            frame.SavedTrueCount
                                            activeFalse
                                            frame.SavedFalseCount

                                finishSolved
                                    ov
                                    caches
                                    (ValueSome(frame.EnsureFallbackState()))
                                    branchCapped.Value
                                    found
                                    frame.Priors
                                    frame.Priors.Count
                                    frame.SavedTrueCount
                                    frame.SavedFalseCount
                                    [ cond ]

                            if not condDuplicate && not (isNull (box cond)) then
                                frame.TakenTrue <-
                                    if condConst <> ValueSome true then
                                        ValueSome cond
                                    else
                                        ValueNone

                                frame.TakenPriorCount <- frame.Priors.Count

                                if condConst <> ValueSome true then
                                    activeTrue.Add(ov, true, cond)

                                syncActiveFalse ov frame

                                if directive.BranchTaken then
                                    frame.FrameUnconditional <-
                                        frame.PriorsAllConstFalse && condConst = ValueSome true

                                frame.Priors.Add(ov, false, cond)

                                frame.PriorsAllConstFalse <-
                                    frame.PriorsAllConstFalse && condConst = ValueSome false

                                frame.AnyPriorConstTrue <-
                                    frame.AnyPriorConstTrue || condConst = ValueSome true
                            elif condDuplicate then
                                frame.TakenTrue <- ValueNone
                                frame.TakenPriorCount <- frame.Priors.Count
                                syncActiveFalse ov frame
                            else
                                frame.TakenTrue <- ValueNone
                                frame.TakenPriorCount <- 0
                                frame.PriorsAllConstFalse <- false

                            frame.ArmImpossible <- armImpossible
                    | :? ElseDirectiveTriviaSyntax as directive ->
                        if stack.Count > 0 then
                            let frameIdx = stack.Count - 1
                            let frame = stack[frameIdx]
                            frame.EvalCaches <- null
                            frame.ConstGuardCache <- null
                            frame.TakeSiblingOverrides() |> ignore

                            if not frame.FrameUnconditional then
                                closeArmOverrides frame (frameIdx + 1) true

                            truncateResolved (frameIdx + 1)
                            restoreActiveArm frame

                            let enclosingImpossible =
                                frameIdx > 0 && stack[frameIdx - 1].ArmImpossible

                            let armImpossible = enclosingImpossible || frame.AnyPriorConstTrue
                            let ov = activeOverrides ()

                            if not armImpossible && not directive.BranchTaken then
                                let baseCands = ensureResolved frameIdx
                                let caches = scopeCachesFor frameIdx

                                let found =
                                    if List.isEmpty baseCands then
                                        []
                                    else
                                        advanceNegated frameIdx baseCands frame frame.Priors.Count

                                finishSolved
                                    ov
                                    caches
                                    (ValueSome(frame.EnsureFallbackState()))
                                    rootCapped.Value
                                    found
                                    frame.Priors
                                    frame.Priors.Count
                                    frame.SavedTrueCount
                                    frame.SavedFalseCount
                                    []

                            frame.TakenTrue <- ValueNone
                            frame.TakenPriorCount <- frame.Priors.Count
                            syncActiveFalse ov frame
                            frame.ArmImpossible <- armImpossible

                            if directive.BranchTaken then
                                frame.FrameUnconditional <- frame.PriorsAllConstFalse
                    | :? EndIfDirectiveTriviaSyntax ->
                        if stack.Count > 0 then
                            let frame = stack[stack.Count - 1]
                            frame.EvalCaches <- null
                            frame.ConstGuardCache <- null
                            let frameDepth = stack.Count
                            stack.RemoveAt(stack.Count - 1)
                            closeArmOverrides frame frameDepth false
                            truncateResolved (stack.Count + 1)
                            restoreActive frame

                            if stack.Count = 0 then
                                rootCapped.Value <- false
                    | _ -> ()

        if not (shouldStop ()) then
            let mutable symEnum = (conditionalSymbols roots).GetEnumerator()

            try
                while not (shouldStop ()) && symEnum.MoveNext() do
                    enqueueSingleton symEnum.Current
            finally
                symEnum.Dispose()

    let internal compareRoots configuration (before: SyntaxNode) (after: SyntaxNode) =
        let finding category detail =
            Some
                {
                    Category = category
                    Configuration = configuration
                    Detail = detail
                }

        let mismatch = compareTrees before after

        if not (isNull mismatch) then
            finding Structural mismatch
        else

            let structured =
                if not (before.ContainsDirectives || after.ContainsDirectives) then
                    None
                else
                    let left = directiveShape before
                    let right = directiveShape after

                    if left.Texts <> right.Texts then
                        let index = firstDifference left.Texts right.Texts

                        finding
                            Directives
                            (String.Format(
                                "{0} directives vs {1}, first difference at {2}",
                                left.Texts.Length,
                                right.Texts.Length,
                                index
                            ))
                    elif left.Anchors <> right.Anchors then
                        let index = firstDifference left.Anchors right.Anchors

                        finding
                            Directives
                            (String.Format(
                                "directive {0} ({1}) after token {2} vs {3}",
                                index,
                                left.Texts[index].Trim(),
                                left.Anchors[index],
                                right.Anchors[index]
                            ))
                    elif left.Frames <> right.Frames then
                        let index = firstDifference left.Frames right.Frames

                        finding
                            UsingScope
                            (String.Format(
                                "using {0} imported from frame '{1}' vs '{2}'",
                                index,
                                (if index < left.Frames.Length then
                                     left.Frames[index]
                                 else
                                     "-"),
                                (if index < right.Frames.Length then
                                     right.Frames[index]
                                 else
                                     "-")
                            ))
                    else
                        None

            match structured with
            | Some _ -> structured
            | None ->
                match newError before after with
                | null -> None
                | introduced -> finding NewSyntaxError introduced

    let adjudicate (source: string) (formatted: string) (symbolBudget: int) =
        let budget = max 0 symbolBudget
        let before = parse source parseOptions
        let after = parse formatted parseOptions
        let findings = ResizeArray<Finding>()
        let mutable configurations = 1
        let mutable capped = false

        match compareRoots "default" before after with
        | Some finding -> findings.Add finding
        | None ->
            let primaryScheduled = HashSet<string>(StringComparer.Ordinal)
            let anyScheduled = HashSet<string>(StringComparer.Ordinal)
            let testedKeys = HashSet<string>(StringComparer.Ordinal)
            primaryScheduled.Add "" |> ignore
            anyScheduled.Add "" |> ignore
            testedKeys.Add "" |> ignore
            let primaryQueue = Queue<struct (string * string array)>()
            let alternateQueue = Queue<struct (string * string array)>()
            let singletonQueue = Queue<struct (string * string array)>()

            let mutable tested = 0

            let canQueueAlternate () =
                alternateQueue.Count < max 0 (budget - tested) + primaryQueue.Count

            let enqueueBranch isPrimary (config: string array) =
                if config.Length > 0 then
                    let key = String.Join("\u0000", config)

                    if not (testedKeys.Contains key) then
                        if isPrimary then
                            if primaryScheduled.Add key then
                                anyScheduled.Add key |> ignore
                                primaryQueue.Enqueue(struct (key, config))
                        elif canQueueAlternate () && anyScheduled.Add key then
                            alternateQueue.Enqueue(struct (key, config))

            let enqueueSingleton (symbol: string) =
                if
                    not (String.IsNullOrEmpty symbol)
                    && not (testedKeys.Contains symbol)
                    && anyScheduled.Add symbol
                then
                    singletonQueue.Enqueue(struct (symbol, [| symbol |]))

            let dequeueFrom (queue: Queue<struct (string * string array)>) =
                let mutable found = ValueNone

                while found.IsNone && queue.Count > 0 do
                    let struct (key, config) = queue.Dequeue()

                    if testedKeys.Add key then
                        found <- ValueSome config

                found

            let nextConfig () =
                match dequeueFrom primaryQueue with
                | ValueSome config -> ValueSome config
                | ValueNone ->
                    match dequeueFrom alternateQueue with
                    | ValueSome config -> ValueSome config
                    | ValueNone -> dequeueFrom singletonQueue

            let hasPending (queue: Queue<struct (string * string array)>) =
                while queue.Count > 0 && testedKeys.Contains(let struct (k, _) = queue.Peek() in k) do
                    queue.Dequeue() |> ignore

                queue.Count > 0

            let hasEnoughDiscovery () =
                let remaining = budget - tested

                if remaining <= 0 then
                    hasPending primaryQueue
                    || hasPending alternateQueue
                    || hasPending singletonQueue
                else
                    primaryQueue.Count > remaining

            let canAcceptAlternate () =
                not (hasEnoughDiscovery ()) && canQueueAlternate ()

            let discoveryCapped = ref false

            discoverBranchConfigs
                hasEnoughDiscovery
                canAcceptAlternate
                discoveryCapped
                [ before; after ]
                enqueueBranch
                enqueueSingleton

            let mutable running = true

            while findings.Count = 0 && running do
                match if tested < budget then nextConfig () else ValueNone with
                | ValueNone -> running <- false
                | ValueSome config ->
                    let options = parseOptions.WithPreprocessorSymbols config
                    let nextBefore = parse source options
                    let nextAfter = parse formatted options
                    let label = "#define " + String.Join(", ", config)
                    tested <- tested + 1

                    match compareRoots label nextBefore nextAfter with
                    | Some finding -> findings.Add finding
                    | None ->
                        discoverBranchConfigs
                            hasEnoughDiscovery
                            canAcceptAlternate
                            discoveryCapped
                            [ nextBefore; nextAfter ]
                            enqueueBranch
                            enqueueSingleton

            configurations <- 1 + tested

            capped <-
                findings.Count = 0
                && (discoveryCapped.Value
                    || hasPending primaryQueue
                    || hasPending alternateQueue
                    || hasPending singletonQueue)

        {
            Findings = List.ofSeq findings
            SourceHadErrors = findings.Count > 0 && (errorCounts before).Count > 0
            Configurations = configurations
            SymbolsCapped = capped
        }
