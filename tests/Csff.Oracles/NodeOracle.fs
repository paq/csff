namespace Csff.Conformance

open System.Collections.Generic
open Csff.Lexer
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Csff.Parser

module NodeOracle =

    let private validRange start count available =
        start >= 0 && count >= 0 && start <= available && count <= available - start

    let private describeNode source (tree: SyntaxTree) index =
        let node = tree.Node index

        if validRange node.TokenStart node.TokenCount tree.TokenCount then
            let struct (start, length) = tree.SourceSpan index
            Diagnostics.describe source $"{node.Kind} ({int node.Kind})" start length
        else
            $"{node.Kind} ({int node.Kind}), invalid token range start={node.TokenStart}, count={node.TokenCount}"

    let private describeExpectedNode source (node: SyntaxNode) =
        Diagnostics.describe
            source
            $"{node.Kind()} ({node.RawKind})"
            node.SpanStart
            node.Span.Length

    let private describeToken source (token: Token) =
        Diagnostics.describe source $"{token.Kind} ({int token.Kind})" token.Start token.Length

    let private describeExpectedToken source (token: SyntaxToken) =
        Diagnostics.describe
            source
            $"{token.Kind()} ({token.RawKind})"
            token.SpanStart
            token.Span.Length

    let checkTree (filePath: string) (source: string) (tree: SyntaxTree) : Result<unit, string> =
        let root = CSharpSyntaxTree.ParseText(source, RoslynOptions.value).GetRoot()
        let expectedNodes = root.DescendantNodes() |> Seq.toArray
        let expectedTokens = root.DescendantTokens() |> Seq.toArray
        let actualNodes = ResizeArray<int>()
        let actualTokens = ResizeArray<int>()
        let actualTokenParents = ResizeArray<int>()
        let expectedNodeIndices = Dictionary<SyntaxNode, int>()
        let visited = Array.zeroCreate<bool> tree.NodeCount
        let pending = Stack<struct (int * int)>()
        let mutable failure = None

        let hasSkippedTrivia (tokens: SyntaxToken array) =
            tokens
            |> Array.exists (fun token ->
                Seq.append token.LeadingTrivia token.TrailingTrivia
                |> Seq.exists (fun trivia -> trivia.IsKind SyntaxKind.SkippedTokensTrivia))

        let expectedComplete =
            not (
                expectedNodes
                |> Array.exists (fun node ->
                    node.IsMissing || node.RawKind = int NodeKind.IncompleteMember)
            )
            && not (
                expectedTokens
                |> Array.exists (fun token ->
                    token.IsMissing
                    || token.RawKind = int TokenKind.BadToken
                    || (token.Span.Length <= 0
                        && token.RawKind <> int TokenKind.EndOfFileToken
                        && token.RawKind <> int TokenKind.OmittedArraySizeExpressionToken
                        && token.RawKind <> int TokenKind.OmittedTypeArgumentToken
                        && not (
                            token.RawKind = int TokenKind.InterpolatedStringTextToken
                            && (match token.Parent with
                                | null -> true
                                | parent ->
                                    match
                                        parent.FirstAncestorOrSelf<
                                            Syntax.InterpolatedStringExpressionSyntax
                                         >()
                                    with
                                    | null -> true
                                    | literal ->
                                        literal.GetDiagnostics()
                                        |> Seq.forall (fun diagnostic -> diagnostic.Id <> "CS9005"))
                        )))
            )
            && not (hasSkippedTrivia expectedTokens)

        let counts =
            $"node count Roslyn={expectedNodes.Length}, csff={max 0 (tree.NodeCount - 1)}; token count Roslyn={expectedTokens.Length}, csff={tree.TokenCount}"

        let mismatch offset reason roslyn csff =
            if failure.IsNone then
                failure <-
                    Some
                        $"{filePath}: offset {offset}: {reason} ({counts}).\n  Roslyn: {roslyn}\n  csff: {csff}"

        let compareTrivia tokenIndex side (roslyn: SyntaxTriviaList) start count expectedOffset =
            if not (validRange start count tree.TriviaCount) then
                mismatch
                    expectedOffset
                    $"token {tokenIndex} {side} trivia range invalid"
                    (describeExpectedToken source expectedTokens[tokenIndex])
                    $"start={start}, count={count}, available={tree.TriviaCount}"
            else
                let mutable index = 0

                while failure.IsNone && index < max roslyn.Count count do
                    let expectedTrivia = if index < roslyn.Count then Some roslyn[index] else None

                    let actualTrivia =
                        if index < count then
                            Some(tree.Trivia(start + index))
                        else
                            None

                    let same =
                        match expectedTrivia, actualTrivia with
                        | Some left, Some right ->
                            left.RawKind = int right.Kind
                            && left.FullSpan.Start = right.Start
                            && left.FullSpan.Length = right.Length
                        | _ -> false

                    if not same then
                        let offset =
                            match expectedTrivia, actualTrivia with
                            | Some left, _ -> left.FullSpan.Start
                            | _, Some right -> right.Start
                            | _ -> expectedOffset

                        let left =
                            match expectedTrivia with
                            | Some trivia ->
                                Diagnostics.describe
                                    source
                                    $"{trivia.Kind()} ({trivia.RawKind})"
                                    trivia.FullSpan.Start
                                    trivia.FullSpan.Length
                            | None -> "<missing trivia>"

                        let right =
                            match actualTrivia with
                            | Some trivia ->
                                Diagnostics.describe
                                    source
                                    $"{trivia.Kind} ({int trivia.Kind})"
                                    trivia.Start
                                    trivia.Length
                            | None -> "<missing trivia>"

                        mismatch
                            offset
                            $"token {tokenIndex} {side} trivia {index} mismatch (Roslyn count={roslyn.Count}, csff count={count})"
                            left
                            right

                    index <- index + 1

        if tree.RootIndex >= 0 then
            pending.Push(struct (tree.RootIndex, -1))

        expectedNodeIndices.Add(root, tree.RootIndex)

        while failure.IsNone && pending.Count > 0 do
            let struct (child, parent) = pending.Pop()

            if child >= 0 then
                if child >= tree.NodeCount || visited[child] then
                    mismatch
                        0
                        "invalid or repeated child node"
                        "<tree node>"
                        $"node index={child}, parent={parent}"
                else
                    let node = tree.Node child
                    visited[child] <- true

                    if node.Parent <> parent then
                        mismatch
                            0
                            "node parent mismatch"
                            $"parent={parent}"
                            (describeNode source tree child + $", parent={node.Parent}")
                    elif not (validRange node.ChildStart node.ChildCount tree.ChildCount) then
                        mismatch
                            0
                            "invalid child range"
                            "<direct children>"
                            (describeNode source tree child
                             + $", child start={node.ChildStart}, count={node.ChildCount}")
                    elif not (validRange node.TokenStart node.TokenCount tree.TokenCount) then
                        mismatch
                            0
                            "invalid node token range"
                            "<descendant tokens>"
                            (describeNode source tree child)
                    else
                        if child <> tree.RootIndex then
                            actualNodes.Add child

                        for index in node.ChildStart + node.ChildCount - 1 .. -1 .. node.ChildStart do
                            pending.Push(struct (tree.Child index, child))
            else
                let index = ~~~child

                if index >= tree.TokenCount then
                    mismatch
                        0
                        "invalid child token"
                        "<tree token>"
                        $"token index={index}, parent={parent}"
                else
                    actualTokens.Add index
                    actualTokenParents.Add parent

        let mutable index = 0

        while failure.IsNone && index < max expectedNodes.Length actualNodes.Count do
            if index >= expectedNodes.Length then
                let nodeIndex = actualNodes[index]
                let struct (start, _) = tree.SourceSpan nodeIndex

                mismatch
                    start
                    $"node {index} count mismatch"
                    "<missing node>"
                    (describeNode source tree nodeIndex)
            elif index >= actualNodes.Count then
                let node = expectedNodes[index]

                mismatch
                    node.SpanStart
                    $"node {index} count mismatch"
                    (describeExpectedNode source node)
                    "<missing node>"
            else
                let expected = expectedNodes[index]
                let nodeIndex = actualNodes[index]
                let actual = tree.Node nodeIndex
                let struct (start, length) = tree.SourceSpan nodeIndex

                if
                    expected.RawKind <> int actual.Kind
                    || expected.SpanStart <> start
                    || expected.Span.Length <> length
                then
                    mismatch
                        expected.SpanStart
                        $"node {index} mismatch"
                        (describeExpectedNode source expected)
                        (describeNode source tree nodeIndex)
                elif actual.Parent <> expectedNodeIndices[expected.Parent] then
                    mismatch
                        expected.SpanStart
                        $"node {index} parent mismatch"
                        (describeExpectedNode source expected + $", parent={expected.Parent.Kind()}")
                        (describeNode source tree nodeIndex
                         + $", parent={(tree.Node actual.Parent).Kind}")

                expectedNodeIndices.Add(expected, nodeIndex)

            index <- index + 1

        index <- 0

        while failure.IsNone && index < max expectedTokens.Length actualTokens.Count do
            if index >= expectedTokens.Length then
                let token = tree.Token actualTokens[index]

                mismatch
                    token.Start
                    $"token {index} count mismatch"
                    "<missing token>"
                    (describeToken source token)
            elif index >= actualTokens.Count then
                let token = expectedTokens[index]

                mismatch
                    token.SpanStart
                    $"token {index} count mismatch"
                    (describeExpectedToken source token)
                    "<missing token>"
            else
                let expected = expectedTokens[index]
                let actual = tree.Token actualTokens[index]

                if
                    expected.RawKind <> int actual.Kind
                    || expected.SpanStart <> actual.Start
                    || expected.Span.Length <> actual.Length
                then
                    mismatch
                        expected.SpanStart
                        $"token {index} mismatch"
                        (describeExpectedToken source expected)
                        (describeToken source actual)
                elif actualTokens[index] <> index then
                    mismatch
                        expected.SpanStart
                        $"token {index} storage order mismatch"
                        (describeExpectedToken source expected)
                        (describeToken source actual + $", token index={actualTokens[index]}")
                elif actualTokenParents[index] <> expectedNodeIndices[expected.Parent] then
                    mismatch
                        expected.SpanStart
                        $"token {index} parent mismatch"
                        (describeExpectedToken source expected
                         + $", parent={expected.Parent.Kind()}")
                        (describeToken source actual
                         + $", parent={(tree.Node actualTokenParents[index]).Kind}")
                else
                    compareTrivia
                        index
                        "leading"
                        expected.LeadingTrivia
                        actual.TriviaStart
                        actual.LeadingCount
                        expected.SpanStart

                    if failure.IsNone then
                        compareTrivia
                            index
                            "trailing"
                            expected.TrailingTrivia
                            (actual.TriviaStart + actual.LeadingCount)
                            actual.TrailingCount
                            expected.SpanStart

            index <- index + 1

        if failure.IsNone then
            match Array.tryFindIndex not visited with
            | Some nodeIndex ->
                mismatch 0 "unreachable node" "<missing node>" (describeNode source tree nodeIndex)
            | None -> ()

            if actualTokens.Count <> tree.TokenCount then
                mismatch
                    0
                    "unreachable parser tokens"
                    "<tree token stream>"
                    $"reachable={actualTokens.Count}, stored={tree.TokenCount}"

            if tree.RootIndex < 0 then
                mismatch
                    root.SpanStart
                    "root count mismatch"
                    (describeExpectedNode source root)
                    "<missing node>"
            else
                let actual = tree.Node tree.RootIndex
                let struct (start, length) = tree.SourceSpan tree.RootIndex

                if
                    root.RawKind <> int actual.Kind
                    || root.SpanStart <> start
                    || root.Span.Length <> length
                then
                    mismatch
                        root.SpanStart
                        "root mismatch"
                        (describeExpectedNode source root)
                        (describeNode source tree tree.RootIndex)

            if failure.IsNone && tree.IsComplete <> expectedComplete then
                mismatch
                    root.SpanStart
                    "completeness mismatch"
                    $"IsComplete={expectedComplete}"
                    $"IsComplete={tree.IsComplete} (recovered={tree.RecoveredTokens})"

        match failure with
        | Some message -> Error message
        | None -> Ok()

    let check (filePath: string) (source: string) (tree: SyntaxTree) : Result<unit, string> =
        Parser.parse source tree
        checkTree filePath source tree
