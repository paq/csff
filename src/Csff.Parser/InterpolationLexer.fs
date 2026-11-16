namespace Csff.Parser

open System
open Csff.Lexer

module internal InterpolationLexer =
    let private newline ch =
        ch = '\r' || ch = '\n' || ch = '\u0085' || ch = '\u2028' || ch = '\u2029'

    let private whitespace ch =
        ch = ' '
        || ch = '\t'
        || ch = '\v'
        || ch = '\f'
        || ch = '\u001a'
        || ch = '\ufeff'
        || Char.GetUnicodeCategory ch = Globalization.UnicodeCategory.SpaceSeparator

    let private expandCore
        (source: string)
        (original: Token)
        (tree: SyntaxTree)
        (holes: ResizeArray<struct (int * int)>)
        =
        let tokens = tree.InterpolationTokens
        tokens.Clear()

        let inline plain kind start length =
            {
                Kind = kind
                Start = start
                Length = length
                TriviaStart = 0
                LeadingCount = 0
                TrailingCount = 0
            }

        let inline add kind start length = tokens.Add(plain kind start length)

        let inline appendLexed (buffer: TokenBuffer) count =
            for index in 0 .. count - 1 do
                let token = buffer.Token index
                let triviaStart = tree.TriviaCount

                for offset in 0 .. token.LeadingCount + token.TrailingCount - 1 do
                    let trivia = buffer.Trivia(token.TriviaStart + offset)

                    tree.AddTrivia trivia |> ignore

                tokens.Add({ token with TriviaStart = triviaStart })

        let mutable quote = original.Start
        let mutable dollars = 0
        let mutable verbatim = false
        let mutable ats = 0

        while quote < original.End && source[quote] <> '"' do
            if source[quote] = '$' then
                dollars <- dollars + 1

            if source[quote] = '@' then
                verbatim <- true
                ats <- ats + 1

            quote <- quote + 1

        let mutable quoteCount = 0

        while quote + quoteCount < original.End && source[quote + quoteCount] = '"' do
            quoteCount <- quoteCount + 1

        let raw = not verbatim && quoteCount >= 3

        if ats > 1 || (dollars > 1 && (ats > 0 || quoteCount < 3)) then
            tree.Recover()

        let width = if raw then max 1 dollars else 1
        let mutable contentStart = quote + (if raw then quoteCount else 1)
        let mutable contentEnd = original.End
        let mutable closed = false

        if raw then
            let mutable ending = original.End

            while ending > contentStart && source[ending - 1] = '"' do
                ending <- ending - 1

            if original.End - ending >= quoteCount then
                closed <- true
                contentEnd <- ending
        elif original.End > contentStart && source[original.End - 1] = '"' then
            let mutable preceding = original.End - 1

            if verbatim then
                while preceding > contentStart && source[preceding - 1] = '"' do
                    preceding <- preceding - 1

                closed <- (original.End - preceding) % 2 = 1
            else
                while preceding > contentStart && source[preceding - 1] = '\\' do
                    preceding <- preceding - 1

                closed <- (original.End - 1 - preceding) % 2 = 0

            if closed then
                contentEnd <- original.End - 1

        if not closed then
            tree.Recover()

        let mutable multiline = false

        if raw then
            let mutable line = contentStart

            while line < original.End && whitespace source[line] do
                line <- line + 1

            if line < original.End && newline source[line] then
                multiline <- true
                contentStart <- line + 1

                if
                    source[line] = '\r'
                    && contentStart < original.End
                    && source[contentStart] = '\n'
                then
                    contentStart <- contentStart + 1

                let mutable lineStart = contentEnd

                while lineStart > contentStart && not (newline source[lineStart - 1]) do
                    lineStart <- lineStart - 1

                let mutable indentationOnly = closed

                for index = lineStart to contentEnd - 1 do
                    indentationOnly <- indentationOnly && whitespace source[index]

                if lineStart > contentStart && indentationOnly then
                    contentEnd <- lineStart - 1

                    if
                        source[contentEnd] = '\n'
                        && contentEnd > contentStart
                        && source[contentEnd - 1] = '\r'
                    then
                        contentEnd <- contentEnd - 1

        contentEnd <- max contentStart contentEnd

        let startKind =
            if raw then
                if multiline then
                    TokenKind.InterpolatedMultiLineRawStringStartToken
                else
                    TokenKind.InterpolatedSingleLineRawStringStartToken
            elif verbatim then
                TokenKind.InterpolatedVerbatimStringStartToken
            else
                TokenKind.InterpolatedStringStartToken

        add startKind original.Start (contentStart - original.Start)
        let mutable cursor = contentStart
        let mutable textStart = cursor
        let mutable degraded = ats > 1 || (dollars > 1 && (ats > 0 || quoteCount < 3))

        while cursor < contentEnd do
            if not raw && not verbatim && source[cursor] = '\\' then
                cursor <- min contentEnd (cursor + 2)
            elif
                not raw
                && source[cursor] = '{'
                && cursor + 1 < contentEnd
                && source[cursor + 1] = '{'
            then
                cursor <- cursor + 2
            elif source[cursor] = '{' then
                let mutable run = cursor

                while run < contentEnd && source[run] = '{' do
                    run <- run + 1

                if run - cursor < width then
                    cursor <- run
                else
                    if raw && run - cursor >= width * 2 then
                        degraded <- true

                    let opening = if raw then run - width else cursor

                    if opening > textStart then
                        add TokenKind.InterpolatedStringTextToken textStart (opening - textStart)

                    let expressionStart = opening + width
                    let openingBuffer = tree.InterpolationBuffer

                    let struct (initialBoundary, initialFormat) =
                        Lexer.lexInterpolationWithRecovery
                            degraded
                            source
                            (expressionStart - 1)
                            contentEnd
                            openingBuffer

                    let mutable boundary = initialBoundary
                    let mutable format = initialFormat

                    let eof = openingBuffer.Token(openingBuffer.TokenCount - 1)
                    let mutable unterminatedComment = false

                    for index = eof.TriviaStart to eof.TriviaStart
                                                   + eof.LeadingCount
                                                   + eof.TrailingCount
                                                   - 1 do
                        let trivia = openingBuffer.Trivia index

                        if
                            (trivia.Kind = TriviaKind.MultiLineCommentTrivia
                             || trivia.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                            && (trivia.Length < 2
                                || source[trivia.Start + trivia.Length - 2] <> '*'
                                || source[trivia.Start + trivia.Length - 1] <> '/')
                        then
                            unterminatedComment <- true

                    if unterminatedComment then
                        Lexer.lexInterpolationWithRecovery
                            false
                            source
                            (expressionStart - 1)
                            original.End
                            openingBuffer
                        |> ignore

                        boundary <- original.End
                        format <- false
                        contentEnd <- original.End
                        closed <- false

                    if openingBuffer.HasMalformedTrivia then
                        tree.LexerBuffer.MarkMalformedTrivia()
                        tree.Recover()

                    let firstIndex = tokens.Count

                    appendLexed openingBuffer (max 0 (openingBuffer.TokenCount - 1))

                    if tokens.Count > firstIndex then
                        tokens[firstIndex] <-
                            { tokens[firstIndex] with
                                Start = opening
                                Length = width
                            }

                    let mutable closing = boundary

                    let inline closingWidth limit position =
                        let mutable finish = position

                        while finish < limit && finish - position < width && source[finish] = '}' do
                            finish <- finish + 1

                        let length = finish - position

                        if length < width then
                            tree.Recover()

                        length

                    let mutable closeLength = 0

                    if format then
                        closing <- min contentEnd (boundary + 1)
                        let formatStart = closing

                        while closing < contentEnd
                              && source[closing] <> '}'
                              && not (raw && source[closing] = '"') do
                            if not raw && not verbatim && source[closing] = '\\' then
                                closing <- min contentEnd (closing + 2)
                            else
                                closing <- closing + 1

                        add
                            TokenKind.InterpolatedStringTextToken
                            formatStart
                            (closing - formatStart)

                        closeLength <- closingWidth contentEnd closing

                        if raw && closeLength < width then
                            degraded <- true

                        add TokenKind.CloseBraceToken closing closeLength
                    elif
                        tokens.Count > firstIndex
                        && closing < contentEnd
                        && openingBuffer.Token(openingBuffer.TokenCount - 2).Kind =
                            TokenKind.CloseBraceToken
                    then
                        let last = tokens.Count - 1
                        closeLength <- closingWidth contentEnd closing

                        if raw && closeLength < width then
                            degraded <- true

                        tokens[last] <-
                            { tokens[last] with
                                Length = closeLength
                            }
                    else
                        tree.Recover()
                        let eof = openingBuffer.Token(openingBuffer.TokenCount - 1)
                        closing <- max closing eof.Start
                        let triviaStart = tree.TriviaCount

                        for offset = 0 to eof.LeadingCount + eof.TrailingCount - 1 do
                            tree.AddTrivia(openingBuffer.Trivia(eof.TriviaStart + offset)) |> ignore

                        tokens.Add
                            { eof with
                                Kind = TokenKind.CloseBraceToken
                                Start = closing
                                Length = 0
                                TriviaStart = triviaStart
                            }

                    if not (isNull holes) then
                        holes.Add(struct (opening, closing + closeLength - opening))

                    cursor <- min contentEnd (closing + closeLength)
                    textStart <- cursor
            elif raw && source[cursor] = '}' then
                let mutable finish = cursor

                while finish < contentEnd && source[finish] = '}' do
                    finish <- finish + 1

                if finish - cursor >= width then
                    degraded <- true

                cursor <- finish
            else
                cursor <- cursor + 1

        if contentEnd > textStart then
            add TokenKind.InterpolatedStringTextToken textStart (contentEnd - textStart)

        add
            (if raw then
                 TokenKind.InterpolatedRawStringEndToken
             else
                 TokenKind.InterpolatedStringEndToken)
            contentEnd
            (if closed then original.End - contentEnd else 0)

        let first = tokens[0]
        let last = tokens[tokens.Count - 1]

        tokens[0] <-
            { first with
                TriviaStart = original.TriviaStart
                LeadingCount = original.LeadingCount
            }

        tokens[tokens.Count - 1] <-
            { last with
                TriviaStart = original.TriviaStart + original.LeadingCount
                TrailingCount = original.TrailingCount
            }

        tokens

    let expand (source: string) (original: Token) (tree: SyntaxTree) =
        expandCore source original tree null

    let expandWithHoles
        (source: string)
        (original: Token)
        (tree: SyntaxTree)
        (holes: ResizeArray<struct (int * int)>)
        =
        expandCore source original tree holes
