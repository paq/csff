namespace Csff.Conformance

open Csff.Lexer
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

module RoslynOracle =

    let private describeToken source (token: SyntaxToken) =
        Diagnostics.describe
            source
            $"{token.Kind()} ({token.RawKind})"
            token.SpanStart
            token.Span.Length

    let private describeCsffToken source (token: Token) =
        Diagnostics.describe source $"{token.Kind} ({int token.Kind})" token.Start token.Length

    [<Struct; NoComparison; NoEquality>]
    type private Expected =
        {
            Kind: int
            Start: int
            Length: int
            Leading: SyntaxTriviaList
            Trailing: SyntaxTriviaList
        }

    let private describeExpected source (token: Expected) =
        Diagnostics.describe
            source
            $"{LanguagePrimitives.EnumOfValue<uint16, SyntaxKind>(uint16 token.Kind)} ({token.Kind})"
            token.Start
            token.Length

    let private rejoin (tokens: SyntaxToken[]) =
        let joined = ResizeArray<Expected>(tokens.Length)
        let mutable index = 0

        while index < tokens.Length do
            let first = tokens[index]
            let mutable last = index
            let mutable kind = first.RawKind

            let contiguous offset =
                offset < tokens.Length
                && tokens[offset].SpanStart = tokens[offset - 1].Span.End
                && tokens[offset].FullSpan.Start = tokens[offset].SpanStart

            let joinsRight offset =
                contiguous offset
                && (offset - index) < 3
                && (tokens[offset].Kind() = SyntaxKind.GreaterThanToken
                    || tokens[offset].Kind() = SyntaxKind.GreaterThanEqualsToken)
                && tokens[offset - 1].Kind() = SyntaxKind.GreaterThanToken

            match first.Kind() with
            | SyntaxKind.GreaterThanToken ->
                while joinsRight (last + 1) do
                    last <- last + 1

                let width = last - index + 1
                let endsWithEquals = tokens[last].Kind() = SyntaxKind.GreaterThanEqualsToken

                kind <-
                    match width, endsWithEquals with
                    | 1, _ -> int SyntaxKind.GreaterThanToken
                    | 2, false -> int SyntaxKind.GreaterThanGreaterThanToken
                    | 2, true -> int SyntaxKind.GreaterThanGreaterThanEqualsToken
                    | 3, false -> int SyntaxKind.GreaterThanGreaterThanGreaterThanToken
                    | _ -> int SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken
            | SyntaxKind.DotToken ->
                if contiguous (index + 1) && tokens[index + 1].Kind() = SyntaxKind.DotToken then
                    last <- index + 1
                    kind <- int SyntaxKind.DotDotToken
            | _ -> ()

            joined.Add
                {
                    Kind = kind
                    Start = first.SpanStart
                    Length = tokens[last].Span.End - first.SpanStart
                    Leading = first.LeadingTrivia
                    Trailing = tokens[last].TrailingTrivia
                }

            index <- last + 1

        joined.ToArray()

    let checkBuffer
        (filePath: string)
        (source: string)
        (buffer: TokenBuffer)
        : Result<unit, string> =
        let expected =
            SyntaxFactory.ParseTokens(source, options = RoslynOptions.value)
            |> Seq.toArray
            |> rejoin

        let mutable failure = None
        let counts = $"token count Roslyn={expected.Length}, csff={buffer.TokenCount}"

        let mismatch offset reason roslyn csff =
            if failure.IsNone then
                failure <-
                    Some
                        $"{filePath}: offset {offset}: {reason} ({counts}).\n  Roslyn: {roslyn}\n  csff: {csff}"

        let compareTrivia tokenIndex side (roslyn: SyntaxTriviaList) start count =
            let mutable index = 0

            while failure.IsNone && index < max roslyn.Count count do
                let expectedTrivia = if index < roslyn.Count then Some roslyn[index] else None

                let actualTrivia =
                    if
                        index < count
                        && start >= 0
                        && start <= buffer.TriviaCount
                        && index < buffer.TriviaCount - start
                    then
                        Some(buffer.Trivia(start + index))
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
                        | _ -> expected[tokenIndex].Start

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

            if
                failure.IsNone
                && (count < 0
                    || start < 0
                    || start > buffer.TriviaCount
                    || count > buffer.TriviaCount - start)
            then
                mismatch
                    expected[tokenIndex].Start
                    $"token {tokenIndex} {side} trivia range invalid"
                    (describeExpected source expected[tokenIndex])
                    $"start={start}, count={count}, available={buffer.TriviaCount}"

        let mutable index = 0

        while failure.IsNone && index < max expected.Length buffer.TokenCount do
            if index >= expected.Length then
                let actual = buffer.Token index

                mismatch
                    actual.Start
                    $"token {index} count mismatch"
                    "<missing token>"
                    (describeCsffToken source actual)
            elif index >= buffer.TokenCount then
                let token = expected[index]

                mismatch
                    token.Start
                    $"token {index} count mismatch"
                    (describeExpected source token)
                    "<missing token>"
            else
                let token = expected[index]
                let actual = buffer.Token index

                if
                    token.Kind <> int actual.Kind
                    || token.Start <> actual.Start
                    || token.Length <> actual.Length
                then
                    mismatch
                        token.Start
                        $"token {index} mismatch"
                        (describeExpected source token)
                        (describeCsffToken source actual)
                else
                    compareTrivia
                        index
                        "leading"
                        token.Leading
                        actual.TriviaStart
                        actual.LeadingCount

                    compareTrivia
                        index
                        "trailing"
                        token.Trailing
                        (actual.TriviaStart + actual.LeadingCount)
                        actual.TrailingCount

            index <- index + 1

        match failure with
        | Some message -> Error message
        | None -> Ok()

    let check (filePath: string) (source: string) (buffer: TokenBuffer) : Result<unit, string> =
        Lexer.lex source buffer
        checkBuffer filePath source buffer
