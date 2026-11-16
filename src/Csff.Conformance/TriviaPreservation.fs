namespace Csff.Conformance

open System
open Csff.Lexer
open Csff.Parser

module TriviaPreservation =
    [<Struct>]
    type private Line =
        {
            Kind: TriviaKind
            Start: int
            Length: int
            Preceding: int
        }

    let private contentLength (text: string) (start: int) (length: int) =
        let mutable result = length

        while result > 0 && Char.IsWhiteSpace text[start + result - 1] do
            result <- result - 1

        result

    let private tokenEnd (buffer: TokenBuffer) index =
        let token = buffer.Token index
        token.End

    let private tokenKind (buffer: TokenBuffer) index =
        let token = buffer.Token index
        token.Kind

    let private collect (text: string) (buffer: TokenBuffer) (into: ResizeArray<Line>) =
        into.Clear()
        let mutable token = 0
        let mutable usingRunEnd = -1
        let mutable preceding = 0

        for index = 0 to buffer.TriviaCount - 1 do
            let item = buffer.Trivia index

            if item.Length > 0 && text[item.Start] = '#' then
                while token < buffer.TokenCount && tokenEnd buffer token <= item.Start do
                    if token > usingRunEnd then
                        let kind = tokenKind buffer token

                        let usingKeyword =
                            if kind = TokenKind.UsingKeyword then
                                token
                            elif
                                (kind = TokenKind.GlobalKeyword
                                 || (kind = TokenKind.IdentifierToken
                                     && (let tok = buffer.Token token in

                                         tok.Length = 6
                                         && text
                                             .AsSpan(tok.Start, 6)
                                             .SequenceEqual("global".AsSpan()))))
                                && token + 1 < buffer.TokenCount
                                && tokenKind buffer (token + 1) = TokenKind.UsingKeyword
                            then
                                token + 1
                            else
                                -1

                        if
                            usingKeyword >= 0
                            && (usingKeyword + 1 >= buffer.TokenCount
                                || tokenKind buffer (usingKeyword + 1) <> TokenKind.OpenParenToken)
                        then
                            let mutable finish = usingKeyword + 1
                            let mutable scanning = true

                            while scanning && finish < buffer.TokenCount do
                                let next = tokenKind buffer finish

                                if
                                    next = TokenKind.SemicolonToken
                                    || next = TokenKind.OpenBraceToken
                                    || next = TokenKind.CloseBraceToken
                                then
                                    scanning <- false
                                else
                                    finish <- finish + 1

                            if
                                finish < buffer.TokenCount
                                && tokenKind buffer finish = TokenKind.SemicolonToken
                            then
                                usingRunEnd <- finish
                            else
                                preceding <- preceding + 1
                        else
                            preceding <- preceding + 1

                    token <- token + 1

                into.Add
                    {
                        Kind = item.Kind
                        Start = item.Start
                        Length = contentLength text item.Start item.Length
                        Preceding = preceding
                    }

    [<AllowNullLiteral; Sealed>]
    type private Scratch() =
        let expectedTree = SyntaxTree()
        let formattedTree = SyntaxTree()
        let left = ResizeArray<Line>()
        let right = ResizeArray<Line>()

        [<ThreadStatic; DefaultValue>]
        static val mutable private current: Scratch

        static member Acquire() =
            let existing = Scratch.current

            if isNull existing then
                let created = Scratch()
                Scratch.current <- created
                created
            else
                existing

        member _.ExpectedTree = expectedTree
        member _.FormattedTree = formattedTree
        member _.Left = left
        member _.Right = right

        member _.TrimOversized() =
            if
                expectedTree.LexerBuffer.TokensStorage.Length > 16384
                || expectedTree.LexerBuffer.TriviaStorage.Length > 16384
            then
                expectedTree.ReleasePooledBuffers()

            if
                formattedTree.LexerBuffer.TokensStorage.Length > 16384
                || formattedTree.LexerBuffer.TriviaStorage.Length > 16384
            then
                formattedTree.ReleasePooledBuffers()

    let private sameTokens
        (left: string)
        (leftBuffer: TokenBuffer)
        (right: string)
        (rightBuffer: TokenBuffer)
        =
        let mutable same = leftBuffer.TokenCount = rightBuffer.TokenCount
        let mutable index = 0

        while same && index < leftBuffer.TokenCount do
            let a = leftBuffer.Token index
            let b = rightBuffer.Token index

            same <-
                a.Kind = b.Kind
                && a.Length = b.Length
                && left.AsSpan(a.Start, a.Length).SequenceEqual(right.AsSpan(b.Start, b.Length))

            index <- index + 1

        same

    let differenceWith (symbols: string array) (expected: string) (formatted: string) : string =
        if not (expected.Contains('#')) && not (formatted.Contains('#')) then
            null
        else
            let scratch = Scratch.Acquire()
            let expectedTree = scratch.ExpectedTree
            let formattedTree = scratch.FormattedTree
            let left = scratch.Left
            let right = scratch.Right

            try
                if symbols.Length > 0 then
                    Parser.lexOnlyWith symbols expected expectedTree
                    Parser.lexOnlyWith symbols formatted formattedTree
                else
                    Parser.lexOnly expected expectedTree
                    Parser.lexOnly formatted formattedTree

                let expectedBuffer = expectedTree.LexerBuffer
                let formattedBuffer = formattedTree.LexerBuffer

                collect expected expectedBuffer left
                collect formatted formattedBuffer right

                let shared = min left.Count right.Count
                let mutable detail = null
                let mutable index = 0

                while isNull detail && index < shared do
                    let a = left[index]
                    let b = right[index]

                    if
                        a.Kind = TriviaKind.ShebangDirectiveTrivia
                        && b.Kind = TriviaKind.ShebangDirectiveTrivia
                        && (a.Start = 0) <> (b.Start = 0)
                    then
                        detail <-
                            String.Format(
                                "directive {0} ({1}) {2} the file and now {3}",
                                index,
                                Diagnostics.excerpt expected a.Start a.Length,
                                (if a.Start = 0 then "began" else "did not begin"),
                                (if b.Start = 0 then "does" else "does not")
                            )
                    elif a.Kind <> b.Kind then
                        detail <-
                            String.Format(
                                "directive {0} was read as {1} and is now read as {2}: {3} became {4}",
                                index,
                                a.Kind.ToString(),
                                b.Kind.ToString(),
                                Diagnostics.excerpt expected a.Start a.Length,
                                Diagnostics.excerpt formatted b.Start b.Length
                            )
                    elif
                        not (
                            expected
                                .AsSpan(a.Start, a.Length)
                                .SequenceEqual(formatted.AsSpan(b.Start, b.Length))
                        )
                    then
                        detail <-
                            String.Format(
                                "directive {0}: {1} became {2}",
                                index,
                                Diagnostics.excerpt expected a.Start a.Length,
                                Diagnostics.excerpt formatted b.Start b.Length
                            )

                    index <- index + 1

                if isNull detail && left.Count <> right.Count then
                    detail <- String.Format("directive count {0} vs {1}", left.Count, right.Count)

                if
                    isNull detail
                    && left.Count = right.Count
                    && sameTokens expected expectedBuffer formatted formattedBuffer
                then
                    let mutable index = 0

                    while isNull detail && index < left.Count do
                        let a = left[index]
                        let b = right[index]

                        if a.Preceding <> b.Preceding then
                            detail <-
                                String.Format(
                                    "directive {0} ({1}) followed {2} tokens and now follows {3}",
                                    index,
                                    Diagnostics.excerpt expected a.Start a.Length,
                                    a.Preceding,
                                    b.Preceding
                                )

                        index <- index + 1

                detail
            finally
                scratch.TrimOversized()

    let difference (expected: string) (formatted: string) : string =
        differenceWith Array.empty expected formatted
