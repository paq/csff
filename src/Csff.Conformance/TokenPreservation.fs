namespace Csff.Conformance

open System
open System.Buffers
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Runtime.Intrinsics
open System.Text
open Csff.Lexer
open Csff.Parser
open Csff.Printer

module TokenPreservation =
    let private lineTerminatorChars =
        SearchValues.Create("\r\n\u0085\u2028\u2029".AsSpan())

    let inline private sameTokenTextSpan
        (leftText: ReadOnlySpan<char>)
        (leftToken: inref<Token>)
        (rightText: ReadOnlySpan<char>)
        (rightToken: inref<Token>)
        =
        if leftToken.Kind < TokenKind.InterpolatedStringStartToken then
            true
        else
            let len = leftToken.Length

            if len <> rightToken.Length then
                false
            elif len = 0 then
                true
            elif len = 1 then
                leftText[leftToken.Start] = rightText[rightToken.Start]
            elif
                len <= 16
                && len <= leftText.Length
                && len <= rightText.Length
                && uint32 leftToken.Start <= uint32 (leftText.Length - len)
                && uint32 rightToken.Start <= uint32 (rightText.Length - len)
            then
                let l0 =
                    &
                        Unsafe.Add(
                            &Unsafe.AsRef(&MemoryMarshal.GetReference leftText),
                            leftToken.Start
                        )

                let r0 =
                    &
                        Unsafe.Add(
                            &Unsafe.AsRef(&MemoryMarshal.GetReference rightText),
                            rightToken.Start
                        )

                if len = 2 then
                    Unsafe.ReadUnaligned<uint32>(&Unsafe.As<char, byte>(&l0)) =
                        Unsafe.ReadUnaligned<uint32>(&Unsafe.As<char, byte>(&r0))
                elif len = 3 then
                    Unsafe.ReadUnaligned<uint32>(&Unsafe.As<char, byte>(&l0)) =
                        Unsafe.ReadUnaligned<uint32>(&Unsafe.As<char, byte>(&r0))
                    && Unsafe.Add(&l0, 2) = Unsafe.Add(&r0, 2)
                elif len = 4 then
                    Unsafe.ReadUnaligned<uint64>(&Unsafe.As<char, byte>(&l0)) =
                        Unsafe.ReadUnaligned<uint64>(&Unsafe.As<char, byte>(&r0))
                elif len <= 8 then
                    let last = len - 4

                    Unsafe.ReadUnaligned<uint64>(&Unsafe.As<char, byte>(&l0)) =
                        Unsafe.ReadUnaligned<uint64>(&Unsafe.As<char, byte>(&r0))
                    && Unsafe.ReadUnaligned<uint64>(&Unsafe.As<char, byte>(&Unsafe.Add(&l0, last))) =
                        Unsafe.ReadUnaligned<uint64>(&Unsafe.As<char, byte>(&Unsafe.Add(&r0, last)))
                else
                    let last = unativeint (len - 8)

                    Vector128.LoadUnsafe(&Unsafe.As<char, uint16>(&l0)) =
                        Vector128.LoadUnsafe(&Unsafe.As<char, uint16>(&r0))
                    && Vector128.LoadUnsafe(&Unsafe.As<char, uint16>(&l0), last) =
                        Vector128.LoadUnsafe(&Unsafe.As<char, uint16>(&r0), last)
            else
                leftText
                    .Slice(leftToken.Start, len)
                    .SequenceEqual(rightText.Slice(rightToken.Start, len))

    let inline private sameTokenText
        (leftText: string)
        (leftToken: inref<Token>)
        (rightText: string)
        (rightToken: inref<Token>)
        =
        sameTokenTextSpan (leftText.AsSpan()) &leftToken (rightText.AsSpan()) &rightToken

    let private describe text (tree: SyntaxTree) index =
        if index < tree.TokenCount then
            let token = tree.Token index
            Diagnostics.describe text $"{token.Kind}" token.Start token.Length
        else
            "<missing token>"

    let inline private directive kind =
        (kind >= TriviaKind.IfDirectiveTrivia && kind <= TriviaKind.BadDirectiveTrivia)
        || kind = TriviaKind.ShebangDirectiveTrivia
        || kind = TriviaKind.LoadDirectiveTrivia
        || kind = TriviaKind.NullableDirectiveTrivia
        || kind = TriviaKind.LineSpanDirectiveTrivia
        || kind = TriviaKind.IgnoredDirectiveTrivia

    let inline private commentTrivia (kind: TriviaKind) =
        kind >= TriviaKind.SingleLineCommentTrivia
        && kind <= TriviaKind.MultiLineDocumentationCommentTrivia
        && kind <> TriviaKind.DocumentationCommentExteriorTrivia

    let inline private contentTrivia (kind: TriviaKind) = kind > TriviaKind.WhitespaceTrivia

    let inline private nonCommentContentTrivia (kind: TriviaKind) =
        kind > TriviaKind.MultiLineDocumentationCommentTrivia

    let inline private nonCommentContentTriviaForProof (allowConditional: bool) (kind: TriviaKind) =
        kind >
            (if allowConditional then
                 TriviaKind.DisabledTextTrivia
             else
                 TriviaKind.MultiLineDocumentationCommentTrivia)

    let inline private layoutOnlyRun (trivia: ReadOnlySpan<Trivia>) (start: int) (count: int) =
        match count with
        | 0 -> true
        | 1 -> trivia[start].Kind <= TriviaKind.WhitespaceTrivia
        | 2 ->
            trivia[start].Kind <= TriviaKind.WhitespaceTrivia
            && trivia[start + 1].Kind <= TriviaKind.WhitespaceTrivia
        | 3 ->
            trivia[start].Kind <= TriviaKind.WhitespaceTrivia
            && trivia[start + 1].Kind <= TriviaKind.WhitespaceTrivia
            && trivia[start + 2].Kind <= TriviaKind.WhitespaceTrivia
        | _ ->
            let mutable ok = true
            let mutable idx = 0

            while ok && idx < count do
                ok <- trivia[start + idx].Kind <= TriviaKind.WhitespaceTrivia
                idx <- idx + 1

            ok

    let inline private isNewLineChar ch =
        ch = '\r' || ch = '\n' || ch = '\u0085' || ch = '\u2028' || ch = '\u2029'

    let inline private isValidShebang (text: string) (item: inref<Trivia>) =
        let finish = item.Start + item.Length

        item.Start = 0
        && item.Length > 0
        && (finish = text.Length || isNewLineChar text[finish - 1])

    let private disabledRunMayOpen (text: ReadOnlySpan<char>) (item: Trivia) =
        let finish = item.Start + item.Length
        let mutable index = item.Start
        let mutable state = 0
        let mutable found = false

        while not found && index < finish do
            let c = text[index]

            if isNewLineChar c then
                state <- 0
            elif state = 0 then
                if c = '/' && index + 1 < finish && text[index + 1] = '/' then
                    state <- 1
                    index <- index + 1
                elif c = '/' && index + 1 < finish && text[index + 1] = '*' then
                    found <- true
                elif c = '"' then
                    if
                        (index > item.Start && (text[index - 1] = '@' || text[index - 1] = '$'))
                        || (index + 2 < finish && text[index + 1] = '"' && text[index + 2] = '"')
                    then
                        found <- true
                    else
                        state <- 2
                elif c = '\'' then
                    state <- 3
            elif state <> 1 then
                if c = '\\' then
                    if index + 1 < finish && not (isNewLineChar text[index + 1]) then
                        index <- index + 1
                elif (state = 2 && c = '"') || (state = 3 && c = '\'') then
                    state <- 0

            index <- index + 1

        found

    let private disabledTextMayOpen (text: ReadOnlySpan<char>) (buffer: TokenBuffer) =
        if not buffer.HasDisabledText then
            false
        else
            let trivia = buffer.TriviaSpan()
            let mutable index = 0
            let mutable found = false

            while not found && index < trivia.Length do
                if trivia[index].Kind = TriviaKind.DisabledTextTrivia then
                    found <- disabledRunMayOpen text trivia[index]

                index <- index + 1

            found

    let private trimmedRunSpan (whole: ReadOnlySpan<char>) (item: Trivia) =
        let mutable length = item.Length

        while length > 0 && isNewLineChar whole[item.Start + length - 1] do
            length <- length - 1

        length

    let private runBeginsLineSpan (whole: ReadOnlySpan<char>) (start: int) =
        let mutable index = start

        while index > 0 && CommentContent.indent whole[index - 1] do
            index <- index - 1

        index = 0 || isNewLineChar whole[index - 1]

    let private triviaRunsAgreeSpan
        (source: ReadOnlySpan<char>)
        (formatted: ReadOnlySpan<char>)
        (input: TokenBuffer)
        (output: TokenBuffer)
        leftStart
        leftCount
        rightStart
        rightCount
        =
        let inputTrivia = input.TriviaSpan()
        let outputTrivia = output.TriviaSpan()
        let leftEnd = leftStart + leftCount
        let rightEnd = rightStart + rightCount
        let mutable left = leftStart
        let mutable right = rightStart
        let mutable same = true

        while same && (left < leftEnd || right < rightEnd) do
            while left < leftEnd && not (contentTrivia inputTrivia[left].Kind) do
                left <- left + 1

            while right < rightEnd && not (contentTrivia outputTrivia[right].Kind) do
                right <- right + 1

            if left < leftEnd && right < rightEnd then
                let a = inputTrivia[left]
                let b = outputTrivia[right]
                let aLength = trimmedRunSpan source a
                let bLength = trimmedRunSpan formatted b

                same <-
                    a.Kind = b.Kind
                    && (if
                            aLength = bLength
                            && source
                                .Slice(a.Start, aLength)
                                .SequenceEqual(formatted.Slice(b.Start, bLength))
                        then
                            true
                        else
                            commentTrivia a.Kind
                            && CommentContent.equivalentSpan source a formatted b)
                    && runBeginsLineSpan source a.Start = runBeginsLineSpan formatted b.Start
                    && (a.Kind <> TriviaKind.ShebangDirectiveTrivia || (a.Start = 0 && b.Start = 0))

                left <- left + 1
                right <- right + 1
            else
                same <- left = leftEnd && right = rightEnd

        same

    let private lexicallyEqualBuffersBounded
        (source: ReadOnlySpan<char>)
        (formatted: ReadOnlySpan<char>)
        (input: TokenBuffer)
        (output: TokenBuffer)
        (startIdx: int)
        (endLimit: int)
        : struct (bool * int) =
        let inputTokens = input.TokenSpan()
        let outputTokens = output.TokenSpan()

        if inputTokens.Length <> outputTokens.Length then
            struct (false, 0)
        else
            let sIdx = max 0 (min startIdx inputTokens.Length)
            let limit = min endLimit inputTokens.Length

            if
                not input.HasComments
                && not output.HasComments
                && not input.HasNonCommentContent
                && not output.HasNonCommentContent
            then
                let mutable same = true
                let mutable index = sIdx

                while same && index < limit do
                    let left = &inputTokens[index]
                    let right = &outputTokens[index]

                    same <-
                        left.Kind = right.Kind
                        && left.Kind <> TokenKind.BadToken
                        && left.Length = right.Length
                        && sameTokenTextSpan source &left formatted &right
                        && (left.Kind <> TokenKind.GreaterThanGreaterThanGreaterThanToken
                            || let leftAdj =
                                index + 1 < inputTokens.Length
                                && inputTokens[index + 1].Start = left.End
                                && inputTokens[index + 1].LeadingCount = 0 in

                               let rightAdj =
                                   index + 1 < outputTokens.Length
                                   && outputTokens[index + 1].Start = right.End
                                   && outputTokens[index + 1].LeadingCount = 0 in

                               leftAdj = rightAdj)

                    if same then
                        index <- index + 1

                struct (same, (if same then inputTokens.Length else index))
            else
                let inputTrivia = input.TriviaSpan()
                let outputTrivia = output.TriviaSpan()
                let lastLeftContent = max input.LastCommentTrivia input.LastNonCommentTrivia
                let lastRightContent = max output.LastCommentTrivia output.LastNonCommentTrivia

                let mutable nextLeftContent =
                    if lastLeftContent < 0 || sIdx >= inputTokens.Length then
                        inputTrivia.Length
                    else
                        let st = inputTokens[sIdx].TriviaStart
                        if st > lastLeftContent then inputTrivia.Length else st

                if nextLeftContent <= lastLeftContent then
                    while nextLeftContent <= lastLeftContent
                          && inputTrivia[nextLeftContent].Kind <= TriviaKind.WhitespaceTrivia do
                        nextLeftContent <- nextLeftContent + 1

                    if nextLeftContent > lastLeftContent then
                        nextLeftContent <- inputTrivia.Length

                let mutable nextRightContent =
                    if lastRightContent < 0 || sIdx >= outputTokens.Length then
                        outputTrivia.Length
                    else
                        let st = outputTokens[sIdx].TriviaStart
                        if st > lastRightContent then outputTrivia.Length else st

                if nextRightContent <= lastRightContent then
                    while nextRightContent <= lastRightContent
                          && outputTrivia[nextRightContent].Kind <= TriviaKind.WhitespaceTrivia do
                        nextRightContent <- nextRightContent + 1

                    if nextRightContent > lastRightContent then
                        nextRightContent <- outputTrivia.Length

                let mutable same = true
                let mutable index = sIdx

                while same && index < limit do
                    let left = &inputTokens[index]
                    let right = &outputTokens[index]

                    if
                        left.Kind = right.Kind
                        && left.Kind <> TokenKind.BadToken
                        && left.Length = right.Length
                        && sameTokenTextSpan source &left formatted &right
                        && (left.Kind <> TokenKind.GreaterThanGreaterThanGreaterThanToken
                            || let leftAdj =
                                index + 1 < inputTokens.Length
                                && inputTokens[index + 1].Start = left.End
                                && inputTokens[index + 1].LeadingCount = 0 in

                               let rightAdj =
                                   index + 1 < outputTokens.Length
                                   && outputTokens[index + 1].Start = right.End
                                   && outputTokens[index + 1].LeadingCount = 0 in

                               leftAdj = rightAdj)
                    then
                        let leftEnd = left.TriviaStart + left.LeadingCount + left.TrailingCount
                        let rightEnd = right.TriviaStart + right.LeadingCount + right.TrailingCount

                        if leftEnd > nextLeftContent || rightEnd > nextRightContent then
                            same <-
                                (((left.LeadingCount ||| right.LeadingCount) = 0)
                                 || (layoutOnlyRun inputTrivia left.TriviaStart left.LeadingCount
                                     && layoutOnlyRun
                                         outputTrivia
                                         right.TriviaStart
                                         right.LeadingCount)
                                 || triviaRunsAgreeSpan
                                     source
                                     formatted
                                     input
                                     output
                                     left.TriviaStart
                                     left.LeadingCount
                                     right.TriviaStart
                                     right.LeadingCount)
                                && (((left.TrailingCount ||| right.TrailingCount) = 0)
                                    || (layoutOnlyRun
                                            inputTrivia
                                            (left.TriviaStart + left.LeadingCount)
                                            left.TrailingCount
                                        && layoutOnlyRun
                                            outputTrivia
                                            (right.TriviaStart + right.LeadingCount)
                                            right.TrailingCount)
                                    || triviaRunsAgreeSpan
                                        source
                                        formatted
                                        input
                                        output
                                        (left.TriviaStart + left.LeadingCount)
                                        left.TrailingCount
                                        (right.TriviaStart + right.LeadingCount)
                                        right.TrailingCount)

                            if same then
                                if leftEnd > nextLeftContent then
                                    if leftEnd > lastLeftContent then
                                        nextLeftContent <- inputTrivia.Length
                                    else
                                        nextLeftContent <- leftEnd

                                        while nextLeftContent <= lastLeftContent
                                              && inputTrivia[nextLeftContent].Kind
                                                 <= TriviaKind.WhitespaceTrivia do
                                            nextLeftContent <- nextLeftContent + 1

                                        if nextLeftContent > lastLeftContent then
                                            nextLeftContent <- inputTrivia.Length

                                if rightEnd > nextRightContent then
                                    if rightEnd > lastRightContent then
                                        nextRightContent <- outputTrivia.Length
                                    else
                                        nextRightContent <- rightEnd

                                        while nextRightContent <= lastRightContent
                                              && outputTrivia[nextRightContent].Kind
                                                 <= TriviaKind.WhitespaceTrivia do
                                            nextRightContent <- nextRightContent + 1

                                        if nextRightContent > lastRightContent then
                                            nextRightContent <- outputTrivia.Length
                    else
                        same <- false

                    if same then
                        index <- index + 1

                struct (same, (if same then inputTokens.Length else index))

    let private lexicallyEqualBuffers
        (source: ReadOnlySpan<char>)
        (formatted: ReadOnlySpan<char>)
        (input: TokenBuffer)
        (output: TokenBuffer)
        : struct (bool * int) =
        lexicallyEqualBuffersBounded source formatted input output 0 input.TokenCount

    let private lexicallyEqualSuffixRange
        (source: ReadOnlySpan<char>)
        (formatted: ReadOnlySpan<char>)
        (input: TokenBuffer)
        (inputStartTok: int)
        (output: TokenBuffer)
        (outputStartTok: int)
        =
        let inputTokens = input.TokenSpan()
        let outputTokens = output.TokenSpan()
        let rem = inputTokens.Length - inputStartTok

        if rem < 2 || outputTokens.Length - outputStartTok <> rem then
            false
        else
            let inputTrivia = input.TriviaSpan()
            let outputTrivia = output.TriviaSpan()
            let mutable same = true
            let mutable k = 0

            while same && k < rem do
                let i = inputStartTok + k
                let j = outputStartTok + k
                let left = &inputTokens[i]
                let right = &outputTokens[j]

                same <-
                    left.Kind = right.Kind
                    && left.Kind <> TokenKind.BadToken
                    && left.Length = right.Length
                    && sameTokenTextSpan source &left formatted &right
                    && (left.Kind <> TokenKind.GreaterThanGreaterThanGreaterThanToken
                        || let leftAdj =
                            i + 1 < inputTokens.Length
                            && inputTokens[i + 1].Start = left.End
                            && inputTokens[i + 1].LeadingCount = 0 in

                           let rightAdj =
                               j + 1 < outputTokens.Length
                               && outputTokens[j + 1].Start = right.End
                               && outputTokens[j + 1].LeadingCount = 0 in

                           leftAdj = rightAdj)
                    && (((left.LeadingCount ||| right.LeadingCount) = 0)
                        || (layoutOnlyRun inputTrivia left.TriviaStart left.LeadingCount
                            && layoutOnlyRun outputTrivia right.TriviaStart right.LeadingCount)
                        || triviaRunsAgreeSpan
                            source
                            formatted
                            input
                            output
                            left.TriviaStart
                            left.LeadingCount
                            right.TriviaStart
                            right.LeadingCount)
                    && (((left.TrailingCount ||| right.TrailingCount) = 0)
                        || (layoutOnlyRun
                                inputTrivia
                                (left.TriviaStart + left.LeadingCount)
                                left.TrailingCount
                            && layoutOnlyRun
                                outputTrivia
                                (right.TriviaStart + right.LeadingCount)
                                right.TrailingCount)
                        || triviaRunsAgreeSpan
                            source
                            formatted
                            input
                            output
                            (left.TriviaStart + left.LeadingCount)
                            left.TrailingCount
                            (right.TriviaStart + right.LeadingCount)
                            right.TrailingCount)

                k <- k + 1

            same

    let inline private nonCommentLayoutOnlyRun
        (allowConditional: bool)
        (trivia: ReadOnlySpan<Trivia>)
        (start: int)
        (count: int)
        =
        let limit =
            if allowConditional then
                TriviaKind.DisabledTextTrivia
            else
                TriviaKind.MultiLineDocumentationCommentTrivia

        match count with
        | 0 -> true
        | 1 -> trivia[start].Kind <= limit
        | 2 -> trivia[start].Kind <= limit && trivia[start + 1].Kind <= limit
        | 3 ->
            trivia[start].Kind <= limit
            && trivia[start + 1].Kind <= limit
            && trivia[start + 2].Kind <= limit
        | _ -> false

    let private commentLabel (kind: TriviaKind) =
        match kind with
        | TriviaKind.SingleLineCommentTrivia -> "//"
        | TriviaKind.MultiLineCommentTrivia -> "/* */"
        | TriviaKind.SingleLineDocumentationCommentTrivia -> "///"
        | _ -> "/** */"

    let private commentKey (text: string) (item: Trivia) =
        let builder = StringBuilder()
        builder.Append(commentLabel item.Kind).Append(' ') |> ignore
        let finish = item.Start + item.Length
        let mutable position = item.Start
        let mutable more = true

        while more do
            let struct (start, length, next) = CommentContent.line text finish position
            builder.Append(text, start, length) |> ignore
            more <- next < finish

            if more then
                builder.Append('\n') |> ignore

            position <- next

        builder.ToString()

    let inline private isUsingOrGlobalUsingTokenSpan
        (source: ReadOnlySpan<char>)
        (tokens: ReadOnlySpan<Token>)
        (tokIdx: int)
        =
        if tokIdx < 0 || tokIdx >= tokens.Length then
            false
        else
            let k = tokens[tokIdx].Kind

            if k = TokenKind.UsingKeyword || k = TokenKind.GlobalKeyword then
                true
            elif
                k = TokenKind.IdentifierToken
                && tokens[tokIdx].Length = 6
                && tokIdx + 1 < tokens.Length
                && tokens[tokIdx + 1].Kind = TokenKind.UsingKeyword
            then
                source.Slice(tokens[tokIdx].Start, 6).SequenceEqual("global".AsSpan())
            else
                false

    let inline private isUsingOrGlobalUsingToken
        (source: string)
        (tokens: ReadOnlySpan<Token>)
        (tokIdx: int)
        =
        isUsingOrGlobalUsingTokenSpan (source.AsSpan()) tokens tokIdx

    let private isUsingDirectiveHeadToken
        (tokens: ReadOnlySpan<Token>)
        (span: ReadOnlySpan<char>)
        (index: int)
        =
        if not (isUsingOrGlobalUsingTokenSpan span tokens index) then
            false
        else
            let u =
                if tokens[index].Kind = TokenKind.UsingKeyword then
                    index
                else
                    index + 1

            tokens[index].Kind <> TokenKind.UsingKeyword
            || u + 1 >= tokens.Length
            || tokens[u + 1].Kind <> TokenKind.OpenParenToken

    let private findUsingRunAnchor
        (tokens: ReadOnlySpan<Token>)
        (span: ReadOnlySpan<char>)
        (firstTok: int)
        =
        if firstTok <= 0 then
            struct (0, true)
        else
            let mutable anchor = firstTok
            let mutable keepWalking = true

            while keepWalking && anchor > 0 do
                let prev = anchor - 1

                if tokens[prev].Kind = TokenKind.SemicolonToken then
                    let mutable clauseHead = prev - 1

                    while clauseHead >= 0
                          && tokens[clauseHead].Kind <> TokenKind.SemicolonToken
                          && tokens[clauseHead].Kind <> TokenKind.OpenBraceToken
                          && tokens[clauseHead].Kind <> TokenKind.CloseBraceToken do
                        clauseHead <- clauseHead - 1

                    let headIdx = clauseHead + 1

                    if
                        headIdx < prev
                        && (isUsingDirectiveHeadToken tokens span headIdx
                            || tokens[headIdx].Kind = TokenKind.ExternKeyword)
                    then
                        anchor <- headIdx
                    else
                        keepWalking <- false
                else
                    keepWalking <- false

            if anchor = 0 then
                struct (0, true)
            else
                let prevKind = tokens[anchor - 1].Kind

                if prevKind = TokenKind.OpenBraceToken || prevKind = TokenKind.SemicolonToken then
                    let mutable h = anchor - 2

                    while h >= 0
                          && (tokens[h].Kind = TokenKind.IdentifierToken
                              || tokens[h].Kind = TokenKind.DotToken
                              || tokens[h].Kind = TokenKind.ColonColonToken
                              || tokens[h].Kind = TokenKind.GlobalKeyword) do
                        h <- h - 1

                    struct (anchor, h >= 0 && tokens[h].Kind = TokenKind.NamespaceKeyword)
                else
                    struct (anchor, false)

    let inline private canBridgeMergedDocRuns (tokKind: TokenKind) (kind: TriviaKind) =
        kind = TriviaKind.WhitespaceTrivia
        || kind = TriviaKind.EndOfLineTrivia
        || ((tokKind = TokenKind.UsingKeyword || tokKind = TokenKind.GlobalKeyword)
            && (kind = TriviaKind.IfDirectiveTrivia
                || kind = TriviaKind.ElifDirectiveTrivia
                || kind = TriviaKind.ElseDirectiveTrivia
                || kind = TriviaKind.EndIfDirectiveTrivia
                || kind = TriviaKind.DisabledTextTrivia))

    let private isIdentContinue (c: char) = Char.IsLetterOrDigit c || c = '_'

    let private trimCSharpWhitespaceStart (span: ReadOnlySpan<char>) =
        let mutable start = 0

        while start < span.Length && Lexer.Classify.whitespace span[start] do
            start <- start + 1

        span.Slice start

    let private trimCSharpWhitespace (span: ReadOnlySpan<char>) =
        let trimmedStart = trimCSharpWhitespaceStart span
        let mutable stop = trimmedStart.Length

        while stop > 0 && Lexer.Classify.whitespace trimmedStart[stop - 1] do
            stop <- stop - 1

        trimmedStart.Slice(0, stop)

    let private isFalseDirectiveExpr (trimmed: ReadOnlySpan<char>) (exprOffset: int) =
        let expr = trimCSharpWhitespace (trimmed.Slice exprOffset)

        expr.Equals("false".AsSpan(), StringComparison.OrdinalIgnoreCase)
        || expr.Equals("0".AsSpan(), StringComparison.Ordinal)

    let private conditionalDirectiveInfo (line: ReadOnlySpan<char>) =
        let trimmed = trimCSharpWhitespace line

        if trimmed.Length >= 3 && trimmed[0] = '#' then
            let rest = trimCSharpWhitespaceStart (trimmed.Slice 1)

            if
                rest.StartsWith("if".AsSpan(), StringComparison.Ordinal)
                && (rest.Length = 2 || not (isIdentContinue rest[2]))
            then
                struct (1, isFalseDirectiveExpr rest 2)
            elif
                rest.StartsWith("elif".AsSpan(), StringComparison.Ordinal)
                && (rest.Length = 4 || not (isIdentContinue rest[4]))
            then
                struct (2, isFalseDirectiveExpr rest 4)
            elif
                rest.StartsWith("else".AsSpan(), StringComparison.Ordinal)
                && (rest.Length = 4 || not (isIdentContinue rest[4]))
            then
                struct (3, false)
            elif
                rest.StartsWith("endif".AsSpan(), StringComparison.Ordinal)
                && (rest.Length = 5 || not (isIdentContinue rest[5]))
            then
                struct (4, false)
            else
                struct (0, false)
        else
            struct (0, false)

    [<NoComparison; NoEquality>]
    type private CommentArmState(canSkip: bool, headerLine: string, bodyStart: int) =
        let raw = ResizeArray<string>()
        let kept = ResizeArray<string>()
        let leaves = ResizeArray<struct (int * int * ResizeArray<string>)>()
        let mutable hasNonEmpty = false
        let mutable hasSkippedWsLeaf = false

        do
            raw.Add headerLine
            kept.Add headerLine

        member _.CanSkip = canSkip
        member _.RawLines = raw
        member _.KeptEntries = kept
        member _.Leaves = leaves
        member _.HasSkippedWsLeaf = hasSkippedWsLeaf
        member _.MarkNonEmpty() = hasNonEmpty <- true
        member _.MarkSkippedWsLeaf() = hasSkippedWsLeaf <- true
        member val CurStart = bodyStart with get, set
        member val CurLines = ResizeArray<string>() with get, set

        member this.FlushLeaf(endPos: int) =
            if canSkip && this.CurLines.Count > 0 then
                if not hasNonEmpty then
                    hasSkippedWsLeaf <- true
                elif this.CurStart < endPos then
                    leaves.Add(struct (this.CurStart, endPos, this.CurLines))
                else
                    kept.AddRange this.CurLines

                this.CurLines <- ResizeArray()
                hasNonEmpty <- false

    let private sameDirectiveCommentSegmentList
        (xs: ResizeArray<string>)
        (ys: ResizeArray<string>)
        =
        if xs.Count <> ys.Count then
            false
        else
            let mutable i = 0
            let mutable eq = true

            while eq && i < xs.Count do
                eq <- String.Equals(xs[i], ys[i], StringComparison.Ordinal)
                i <- i + 1

            eq

    let private extractDirectiveCommentSegments (span: ReadOnlySpan<char>) =
        let kept = ResizeArray<string>()
        let closedLeaves = ResizeArray<struct (int * int * ResizeArray<string>)>()
        let mutable exitedOpening = false
        let mutable hasSkippedWsLeaf = false
        let mutable pos = 0
        let armStack = ResizeArray<CommentArmState>()

        while pos < span.Length do
            let lineStart = pos
            let nextBreak = span.Slice(pos).IndexOfAny(lineTerminatorChars)

            let mutable lineEnd = if nextBreak < 0 then span.Length else pos + nextBreak

            let rawLine = span.Slice(pos, lineEnd - pos)
            let csharpTrimmed = trimCSharpWhitespace rawLine
            let line = rawLine.Trim()
            let struct (kind, isFalseExpr) = conditionalDirectiveInfo csharpTrimmed
            let normalized = String(if kind <> 0 then csharpTrimmed else line)

            if lineEnd < span.Length then
                if
                    span[lineEnd] = '\r' && lineEnd + 1 < span.Length && span[lineEnd + 1] = '\n'
                then
                    lineEnd <- lineEnd + 2
                else
                    lineEnd <- lineEnd + 1

            match kind with
            | 1 ->
                if armStack.Count > 0 then
                    armStack[armStack.Count - 1].FlushLeaf lineStart

                let parentSkip = armStack.Count = 0 || armStack[armStack.Count - 1].CanSkip
                let canSkip = exitedOpening && not isFalseExpr && parentSkip
                armStack.Add(CommentArmState(canSkip, normalized, lineEnd))
            | 2
            | 3 ->
                if armStack.Count = 0 then
                    exitedOpening <- true
                    let canSkip = kind = 3 || not isFalseExpr
                    armStack.Add(CommentArmState(canSkip, normalized, lineEnd))
                else
                    let topIdx = armStack.Count - 1
                    let closing = armStack[topIdx]
                    armStack.RemoveAt topIdx
                    closing.FlushLeaf lineStart

                    let nextCanSkip =
                        exitedOpening
                        && (kind = 3 || not isFalseExpr)
                        && (armStack.Count = 0 || armStack[armStack.Count - 1].CanSkip)

                    if armStack.Count > 0 then
                        let parent = armStack[armStack.Count - 1]
                        parent.RawLines.AddRange closing.RawLines

                        if closing.CanSkip then
                            parent.KeptEntries.AddRange closing.KeptEntries
                            parent.Leaves.AddRange closing.Leaves

                            if closing.HasSkippedWsLeaf then
                                parent.MarkSkippedWsLeaf()
                        else
                            parent.KeptEntries.AddRange closing.RawLines
                    elif closing.CanSkip then
                        kept.AddRange closing.KeptEntries
                        closedLeaves.AddRange closing.Leaves

                        if closing.HasSkippedWsLeaf then
                            hasSkippedWsLeaf <- true
                    else
                        kept.AddRange closing.RawLines

                    armStack.Add(CommentArmState(nextCanSkip, normalized, lineEnd))
            | 4 ->
                if armStack.Count = 0 then
                    exitedOpening <- true
                    kept.Add normalized
                else
                    let topIdx = armStack.Count - 1
                    let closing = armStack[topIdx]
                    armStack.RemoveAt topIdx
                    closing.FlushLeaf lineStart
                    closing.RawLines.Add normalized
                    closing.KeptEntries.Add normalized

                    if armStack.Count > 0 then
                        let parent = armStack[armStack.Count - 1]
                        parent.RawLines.AddRange closing.RawLines

                        if closing.CanSkip then
                            parent.KeptEntries.AddRange closing.KeptEntries
                            parent.Leaves.AddRange closing.Leaves

                            if closing.HasSkippedWsLeaf then
                                parent.MarkSkippedWsLeaf()
                        else
                            parent.KeptEntries.AddRange closing.RawLines

                        parent.CurStart <- lineEnd
                    elif closing.CanSkip then
                        kept.AddRange closing.KeptEntries
                        closedLeaves.AddRange closing.Leaves

                        if closing.HasSkippedWsLeaf then
                            hasSkippedWsLeaf <- true
                    else
                        kept.AddRange closing.RawLines
            | _ ->
                if armStack.Count > 0 then
                    let arm = armStack[armStack.Count - 1]
                    arm.RawLines.Add normalized

                    if arm.CanSkip then
                        if arm.CurLines.Count = 0 then
                            arm.CurStart <- lineStart

                        if csharpTrimmed.Length > 0 then
                            arm.MarkNonEmpty()

                        arm.CurLines.Add normalized
                    else
                        arm.KeptEntries.Add normalized
                else
                    kept.Add normalized

            pos <- lineEnd

        for idx = 0 to armStack.Count - 1 do
            let arm = armStack[idx]

            if arm.CanSkip then
                kept.AddRange arm.KeptEntries
                kept.AddRange arm.CurLines
                closedLeaves.AddRange arm.Leaves

                if arm.HasSkippedWsLeaf then
                    hasSkippedWsLeaf <- true
            else
                kept.AddRange arm.RawLines

        struct (exitedOpening, kept, closedLeaves, hasSkippedWsLeaf)

    let private hasConditionalDirectiveSpanningLine (span: ReadOnlySpan<char>) =
        if span.IndexOf '#' < 0 then
            false
        else
            let mutable pos = 0
            let mutable found = false

            while not found && pos < span.Length do
                let nextBreak = span.Slice(pos).IndexOfAny(lineTerminatorChars)
                let lineEnd = if nextBreak < 0 then span.Length else pos + nextBreak
                let struct (kind, _) = conditionalDirectiveInfo (span.Slice(pos, lineEnd - pos))

                if kind >= 2 then
                    found <- true
                elif lineEnd < span.Length then
                    if
                        span[lineEnd] = '\r'
                        && lineEnd + 1 < span.Length
                        && span[lineEnd + 1] = '\n'
                    then
                        pos <- lineEnd + 2
                    else
                        pos <- lineEnd + 1
                else
                    pos <- span.Length

            found

    let private directiveSpanningMultiLineEquivalent
        (leftSpan: ReadOnlySpan<char>)
        (rightSpan: ReadOnlySpan<char>)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        outerSpans.Clear()

        if
            not (hasConditionalDirectiveSpanningLine leftSpan)
            || not (hasConditionalDirectiveSpanningLine rightSpan)
        then
            false
        else
            let struct (lExited, lKept, lLeaves, lSkippedWs) =
                extractDirectiveCommentSegments leftSpan

            let struct (rExited, rKept, rLeaves, rSkippedWs) =
                extractDirectiveCommentSegments rightSpan

            if
                lExited
                && rExited
                && lLeaves.Count = rLeaves.Count
                && (rLeaves.Count > 0 || lSkippedWs || rSkippedWs)
                && sameDirectiveCommentSegmentList lKept rKept
            then
                for i = 0 to lLeaves.Count - 1 do
                    let struct (lStart, lEnd, lLines) = lLeaves[i]
                    let struct (rStart, rEnd, rLines) = rLeaves[i]

                    if not (sameDirectiveCommentSegmentList lLines rLines) then
                        outerSpans.Add(struct (lStart, lEnd, rStart, rEnd))

                true
            else
                false

    let private mergedDocCommentEquivalentSpan
        (source: ReadOnlySpan<char>)
        (input: TokenBuffer)
        (inputStart: int)
        (inputEnd: int)
        (tokStart: int)
        (formatted: ReadOnlySpan<char>)
        (rightItem: Trivia)
        =
        let inputTrivia = input.TriviaSpan()
        let inputTokens = input.TokenSpan()
        let mutable tokIdx = tokStart

        while tokIdx < inputTokens.Length
              && (let tok = inputTokens[tokIdx] in
                  tok.TriviaStart + tok.LeadingCount + tok.TrailingCount <= inputStart) do
            tokIdx <- tokIdx + 1

        let mutable limit, tokKind =
            if tokIdx < inputTokens.Length then
                let tok = inputTokens[tokIdx]

                let tk =
                    if isUsingOrGlobalUsingTokenSpan source inputTokens tokIdx then
                        TokenKind.UsingKeyword
                    else
                        tok.Kind

                min inputEnd (tok.TriviaStart + tok.LeadingCount + tok.TrailingCount), tk
            else
                inputEnd, TokenKind.None

        let rightFinish = rightItem.Start + rightItem.Length
        let mutable scanTok = tokIdx
        let mutable b = rightItem.Start
        let mutable leftIdx = inputStart
        let mutable same = true
        let mutable matchedRuns = 0
        let mutable canContinue = true

        while same && b < rightFinish && canContinue do
            while leftIdx < limit && canBridgeMergedDocRuns tokKind inputTrivia[leftIdx].Kind do
                leftIdx <- leftIdx + 1

            if leftIdx >= limit then
                if tokKind = TokenKind.UsingKeyword && scanTok < inputTokens.Length then
                    let mutable semiTok = scanTok

                    while semiTok < inputTokens.Length
                          && inputTokens[semiTok].Kind <> TokenKind.SemicolonToken
                          && inputTokens[semiTok].Kind <> TokenKind.OpenBraceToken do
                        semiTok <- semiTok + 1

                    if
                        semiTok < inputTokens.Length
                        && inputTokens[semiTok].Kind = TokenKind.SemicolonToken
                        && semiTok + 1 < inputTokens.Length
                        && isUsingOrGlobalUsingTokenSpan source inputTokens (semiTok + 1)
                    then
                        let nextTok = inputTokens[semiTok + 1]
                        let spanStart = inputTokens[scanTok].TriviaStart
                        let spanEnd = nextTok.TriviaStart + nextTok.LeadingCount
                        let mutable sawDirective = false
                        let mutable bridgeClean = true
                        let mutable tIdx = spanStart

                        while bridgeClean && tIdx < spanEnd && tIdx < inputTrivia.Length do
                            let kind = inputTrivia[tIdx].Kind

                            if
                                kind = TriviaKind.IfDirectiveTrivia
                                || kind = TriviaKind.ElifDirectiveTrivia
                                || kind = TriviaKind.ElseDirectiveTrivia
                                || kind = TriviaKind.EndIfDirectiveTrivia
                                || kind = TriviaKind.DisabledTextTrivia
                            then
                                sawDirective <- true
                            elif
                                kind = TriviaKind.SingleLineCommentTrivia
                                || kind = TriviaKind.MultiLineCommentTrivia
                                || kind = TriviaKind.MultiLineDocumentationCommentTrivia
                            then
                                bridgeClean <- false

                            tIdx <- tIdx + 1

                        if sawDirective && bridgeClean then
                            limit <-
                                min
                                    inputEnd
                                    (nextTok.TriviaStart
                                     + nextTok.LeadingCount
                                     + nextTok.TrailingCount)

                            scanTok <- semiTok + 1
                        else
                            canContinue <- false
                    else
                        canContinue <- false
                else
                    canContinue <- false
            elif inputTrivia[leftIdx].Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                let leftItem = inputTrivia[leftIdx]
                let leftFinish = leftItem.Start + leftItem.Length
                let mutable a = leftItem.Start

                while same && a < leftFinish do
                    if b >= rightFinish then
                        same <- false
                    else
                        let struct (aStart, aLength, aNext) =
                            CommentContent.lineSpan source leftFinish a

                        let struct (bStart, bLength, bNext) =
                            CommentContent.lineSpan formatted rightFinish b

                        same <-
                            aLength = bLength
                            && source
                                .Slice(aStart, aLength)
                                .SequenceEqual(formatted.Slice(bStart, bLength))

                        a <- aNext
                        b <- bNext

                if same then
                    matchedRuns <- matchedRuns + 1
                    leftIdx <- leftIdx + 1
            else
                same <- false

        if same && b >= rightFinish && matchedRuns >= 2 then
            struct (leftIdx, tokIdx)
        else
            struct (-1, tokIdx)

    let private mergedDocCommentEquivalent
        (source: string)
        (input: TokenBuffer)
        (inputStart: int)
        (inputEnd: int)
        (tokStart: int)
        (formatted: string)
        (rightItem: Trivia)
        =
        mergedDocCommentEquivalentSpan
            (source.AsSpan())
            input
            inputStart
            inputEnd
            tokStart
            (formatted.AsSpan())
            rightItem

    let private rawCommentKeysRange
        (text: string)
        (trivia: ReadOnlySpan<Trivia>)
        (startIdx: int)
        (endIdx: int)
        =
        if startIdx > endIdx then
            ResizeArray<string>(0)
        else
            let items = ResizeArray<string>(max 4 (endIdx - startIdx + 1))

            for index = startIdx to endIdx do
                let item = trivia[index]

                if commentTrivia item.Kind then
                    items.Add(commentKey text item)

            items

    [<Struct>]
    type private DocGroup =
        {
            CombinedBody: string
            CombinedKey: string
            PartKeys: string array
            PartBodies: string array
            TokenIndex: int
            TokenKind: TokenKind
            IsFirstOnToken: bool
            IsLastOnToken: bool
            IsLastInHeader: bool
            IsBeforeIfOnToken: bool
            ExcludeGroupA: int
            ExcludeGroupB: int
        }

    let private sameUsingDirective
        (source: string)
        (inputTokens: ReadOnlySpan<Token>)
        (inTok: int)
        (formatted: string)
        (outputTokens: ReadOnlySpan<Token>)
        (outTok: int)
        =
        if inTok < 0 || outTok < 0 then
            false
        else
            let mutable t1 = inTok
            let mutable t2 = outTok
            let mutable same = true
            let mutable doneScan = false

            while same && not doneScan do
                if t1 >= inputTokens.Length || t2 >= outputTokens.Length then
                    same <- false
                else
                    let tok1 = inputTokens[t1]
                    let tok2 = outputTokens[t2]

                    if
                        tok1.Length <> tok2.Length
                        || not (
                            source
                                .AsSpan(tok1.Start, tok1.Length)
                                .SequenceEqual(formatted.AsSpan(tok2.Start, tok2.Length))
                        )
                    then
                        same <- false
                    elif
                        tok1.Kind = TokenKind.SemicolonToken || tok2.Kind = TokenKind.SemicolonToken
                    then
                        same <-
                            tok1.Kind = TokenKind.SemicolonToken
                            && tok2.Kind = TokenKind.SemicolonToken

                        doneScan <- true
                    else
                        t1 <- t1 + 1
                        t2 <- t2 + 1

            same

    let private countIfOrSingleLineComments (trivia: ReadOnlySpan<Trivia>) (tok: Token) =
        let mutable c = 0

        for i = tok.TriviaStart to tok.TriviaStart + tok.LeadingCount - 1 do
            let k = trivia[i].Kind

            if k = TriviaKind.IfDirectiveTrivia || k = TriviaKind.SingleLineCommentTrivia then
                c <- c + 1

        c

    let private computeUsingRunIdsRange
        (source: string)
        (input: TokenBuffer)
        (startTok: int)
        (initialCanStart: bool)
        (maxUsingToken: int)
        =
        let tokens = input.TokenSpan()
        let trivia = input.TriviaSpan()
        let count = tokens.Length
        let baseTok = max 0 startTok
        let limit = min (count - 1) maxUsingToken

        if limit < baseTok then
            struct (baseTok,
                    Array.empty<int>,
                    Array.empty<bool>,
                    0,
                    Array.empty<int>,
                    Array.empty<bool>)
        else
            let arrLen = min (count - baseTok) (limit - baseTok + 2)
            let runIds = Array.create arrLen -1
            let isFirstInRun = Array.zeroCreate<bool> arrLen
            let runFirstTokens = ResizeArray<int>(4)
            let runPreserved = ResizeArray<bool>(4)
            let mutable canStartUsing = initialCanStart
            let mutable currentRun = -1
            let mutable nextRun = 0
            let mutable t = baseTok

            while t <= limit do
                let kind = tokens[t].Kind

                if canStartUsing && kind = TokenKind.ExternKeyword then
                    currentRun <- -1
                    t <- t + 1

                    while t < count
                          && tokens[t].Kind <> TokenKind.SemicolonToken
                          && tokens[t].Kind <> TokenKind.OpenBraceToken
                          && tokens[t].Kind <> TokenKind.CloseBraceToken do
                        t <- t + 1

                    if t < count && tokens[t].Kind = TokenKind.SemicolonToken then
                        t <- t + 1
                    else
                        canStartUsing <- false
                elif canStartUsing && isUsingOrGlobalUsingToken source tokens t then
                    let u = if kind = TokenKind.UsingKeyword then t else t + 1

                    if u + 1 < count && tokens[u + 1].Kind <> TokenKind.OpenParenToken then
                        let mutable k = u + 1
                        let mutable equalsCount = 0
                        let mutable equalsPos = -1
                        let mutable bad = false

                        while k < count && tokens[k].Kind <> TokenKind.SemicolonToken && not bad do
                            let kk = tokens[k].Kind

                            if kk = TokenKind.OpenBraceToken || kk = TokenKind.CloseBraceToken then
                                bad <- true
                            elif kk = TokenKind.EqualsToken then
                                equalsCount <- equalsCount + 1
                                equalsPos <- k

                            k <- k + 1

                        let validAlias =
                            equalsCount = 0
                            || (equalsCount = 1
                                && ((equalsPos = u + 2
                                     && tokens[u + 1].Kind = TokenKind.IdentifierToken)
                                    || (equalsPos = u + 3
                                        && tokens[u + 1].Kind = TokenKind.UnsafeKeyword
                                        && tokens[u + 2].Kind = TokenKind.IdentifierToken)))

                        if
                            not bad
                            && k < count
                            && tokens[k].Kind = TokenKind.SemicolonToken
                            && validAlias
                        then
                            let tok = tokens[t]
                            let mutable hasContextDir = false

                            for tr = tok.TriviaStart to tok.TriviaStart + tok.LeadingCount - 1 do
                                let tk = trivia[tr].Kind

                                if
                                    tk = TriviaKind.DefineDirectiveTrivia
                                    || tk = TriviaKind.UndefDirectiveTrivia
                                    || tk = TriviaKind.NullableDirectiveTrivia
                                    || tk = TriviaKind.LineDirectiveTrivia
                                    || tk = TriviaKind.LineSpanDirectiveTrivia
                                    || tk = TriviaKind.ErrorDirectiveTrivia
                                    || tk = TriviaKind.WarningDirectiveTrivia
                                    || tk = TriviaKind.PragmaWarningDirectiveTrivia
                                    || tk = TriviaKind.PragmaChecksumDirectiveTrivia
                                    || tk = TriviaKind.BadDirectiveTrivia
                                then
                                    hasContextDir <- true

                            if currentRun < 0 then
                                currentRun <- nextRun
                                nextRun <- nextRun + 1
                                runFirstTokens.Add t
                                runPreserved.Add false
                                isFirstInRun[t - baseTok] <- true
                                isFirstInRun[u - baseTok] <- true
                            elif hasContextDir then
                                runPreserved[currentRun] <- true

                            runIds[t - baseTok] <- currentRun
                            runIds[u - baseTok] <- currentRun
                            t <- k + 1
                        else
                            currentRun <- -1
                            canStartUsing <- false
                            t <- t + 1
                    else
                        currentRun <- -1
                        canStartUsing <- false
                        t <- t + 1
                elif kind = TokenKind.NamespaceKeyword then
                    currentRun <- -1
                    canStartUsing <- false
                    t <- t + 1

                    while t < count
                          && tokens[t].Kind <> TokenKind.OpenBraceToken
                          && tokens[t].Kind <> TokenKind.SemicolonToken
                          && tokens[t].Kind <> TokenKind.CloseBraceToken do
                        t <- t + 1

                    if
                        t < count
                        && (tokens[t].Kind = TokenKind.OpenBraceToken
                            || tokens[t].Kind = TokenKind.SemicolonToken)
                    then
                        canStartUsing <- true
                        t <- t + 1
                else
                    currentRun <- -1
                    canStartUsing <- false
                    t <- t + 1

            struct (baseTok,
                    runIds,
                    isFirstInRun,
                    nextRun,
                    runFirstTokens.ToArray(),
                    runPreserved.ToArray())

    let private computeRunHeaderInfo
        (source: string)
        (input: TokenBuffer)
        (groups: ResizeArray<DocGroup>)
        (startTok: int)
        (initialCanStart: bool)
        (maxUsingDocToken: int)
        =
        if maxUsingDocToken < 0 then
            struct (0, null, null, 0, null, null, null)
        else
            let struct (baseTok, rIds, firstFlags, rCount, rFirstTokens, rPreserved) =
                computeUsingRunIdsRange source input startTok initialCanStart maxUsingDocToken

            if rCount <= 0 then
                struct (baseTok, rIds, firstFlags, 0, null, null, null)
            else
                let runHeaderGroup = Array.create rCount -1
                let runHasSorted = Array.zeroCreate<bool> rCount

                for g = 0 to groups.Count - 1 do
                    let rel = groups[g].TokenIndex - baseTok

                    if rel >= 0 && rel < rIds.Length then
                        let runId = rIds[rel]

                        if runId >= 0 && not rPreserved[runId] then
                            if firstFlags[rel] && groups[g].IsLastInHeader then
                                runHeaderGroup[runId] <- g
                            elif not firstFlags[rel] && groups[g].IsFirstOnToken then
                                runHasSorted[runId] <- true

                struct (baseTok,
                        rIds,
                        firstFlags,
                        rCount,
                        runHeaderGroup,
                        runHasSorted,
                        rFirstTokens)

    let inline private tokenIndexForTrivia (tokens: ReadOnlySpan<Token>) (trivIndex: int) =
        let mutable lo = 0
        let mutable hi = tokens.Length

        while lo < hi do
            let mid = lo + ((hi - lo) >>> 1)
            let tok = tokens[mid]

            if tok.TriviaStart + tok.LeadingCount + tok.TrailingCount <= trivIndex then
                lo <- mid + 1
            else
                hi <- mid

        lo

    let private commentKeyPair
        (source: string)
        (input: TokenBuffer)
        (startLeft: int)
        (endLeft: int)
        (formatted: string)
        (output: TokenBuffer)
        (startRight: int)
        (endRight: int)
        =
        let inputTrivia = input.TriviaSpan()
        let outputTrivia = output.TriviaSpan()
        let inputTokens = input.TokenSpan()
        let tokenCount = input.TokenCount
        let expectedItems = ResizeArray<string>(max 4 (endLeft - startLeft + 1))
        let groups = ResizeArray<DocGroup>()
        let partKeysBuf = ResizeArray<string>(4)
        let partBodiesBuf = ResizeArray<string>(4)
        let sb = StringBuilder()

        let mutable tokIdx =
            if startLeft > 0 then
                tokenIndexForTrivia inputTokens startLeft
            else
                0

        let mutable currentTok = -1
        let mutable firstCommentOnToken = true
        let mutable sawIfOnToken = false
        let mutable firstBridgedIdx = -1
        let mutable canBridgeIfOnTok = false
        let mutable sawDisabledInBridge = false
        let mutable groupToken = -1
        let mutable groupFirstOnToken = false

        let flushGroup (lastOnToken: bool) (lastInHeader: bool) =
            if partKeysBuf.Count > 0 then
                let combinedBody =
                    if partBodiesBuf.Count = 1 then
                        partBodiesBuf[0]
                    else
                        sb.Clear() |> ignore

                        for p = 0 to partBodiesBuf.Count - 1 do
                            if p > 0 then
                                sb.Append('\n') |> ignore

                            sb.Append(partBodiesBuf[p]) |> ignore

                        sb.ToString()

                let combinedKey =
                    if partKeysBuf.Count = 1 then
                        partKeysBuf[0]
                    else
                        "/// " + combinedBody

                let tk =
                    if groupToken >= 0 && groupToken < tokenCount then
                        let k = (input.Token groupToken).Kind

                        if k = TokenKind.UsingKeyword || k = TokenKind.GlobalKeyword then
                            TokenKind.UsingKeyword
                        elif
                            k = TokenKind.IdentifierToken
                            && (input.Token groupToken).Length = 6
                            && groupToken + 1 < tokenCount
                            && (input.Token(groupToken + 1)).Kind = TokenKind.UsingKeyword
                            && source
                                .AsSpan((input.Token groupToken).Start, 6)
                                .SequenceEqual("global".AsSpan())
                        then
                            TokenKind.UsingKeyword
                        else
                            k
                    else
                        TokenKind.None

                groups.Add
                    {
                        CombinedBody = combinedBody
                        CombinedKey = combinedKey
                        PartKeys = partKeysBuf.ToArray()
                        PartBodies = partBodiesBuf.ToArray()
                        TokenIndex = groupToken
                        TokenKind = tk
                        IsFirstOnToken = groupFirstOnToken
                        IsLastOnToken = lastOnToken
                        IsLastInHeader = lastInHeader
                        IsBeforeIfOnToken = not sawIfOnToken
                        ExcludeGroupA = -1
                        ExcludeGroupB = -1
                    }

                partKeysBuf.Clear()
                partBodiesBuf.Clear()

        let tryCloseBridged () =
            if
                canBridgeIfOnTok
                && sawDisabledInBridge
                && firstBridgedIdx >= 0
                && groups.Count - 1 = firstBridgedIdx + 1
            then
                let gFirst = firstBridgedIdx
                let gLast = groups.Count - 1
                let fGrp = groups[gFirst]
                let lGrp = groups[gLast]

                if fGrp.TokenIndex = lGrp.TokenIndex then
                    let bIdx = groups.Count
                    let bBody = fGrp.CombinedBody + "\n" + lGrp.CombinedBody
                    let bKey = "/// " + bBody
                    let bPartKeys = Array.append fGrp.PartKeys lGrp.PartKeys
                    let bPartBodies = Array.append fGrp.PartBodies lGrp.PartBodies
                    groups[gFirst] <- { fGrp with ExcludeGroupA = bIdx }
                    groups[gLast] <- { lGrp with ExcludeGroupA = bIdx }

                    groups.Add
                        {
                            CombinedBody = bBody
                            CombinedKey = bKey
                            PartKeys = bPartKeys
                            PartBodies = bPartBodies
                            TokenIndex = fGrp.TokenIndex
                            TokenKind = fGrp.TokenKind
                            IsFirstOnToken = fGrp.IsFirstOnToken
                            IsLastOnToken = lGrp.IsLastOnToken
                            IsLastInHeader = false
                            IsBeforeIfOnToken = false
                            ExcludeGroupA = gFirst
                            ExcludeGroupB = gLast
                        }

            firstBridgedIdx <- -1
            canBridgeIfOnTok <- false
            sawDisabledInBridge <- false

        let switchToken (newTok: int) (upToTrivia: int) =
            flushGroup true (not sawIfOnToken)
            tryCloseBridged ()
            currentTok <- newTok
            firstCommentOnToken <- true
            sawIfOnToken <- false

            if newTok < tokenCount then
                for prev = (input.Token newTok).TriviaStart to upToTrivia - 1 do
                    let pk = (input.Trivia prev).Kind

                    if commentTrivia pk then
                        firstCommentOnToken <- false
                    elif pk = TriviaKind.IfDirectiveTrivia then
                        sawIfOnToken <- true

        if startLeft <= endLeft then
            for index = startLeft to endLeft do
                let item = inputTrivia[index]

                if commentTrivia item.Kind then
                    while tokIdx < tokenCount
                          && (let tok = inputTokens[tokIdx] in
                              tok.TriviaStart + tok.LeadingCount + tok.TrailingCount <= index) do
                        tokIdx <- tokIdx + 1

                    if tokIdx <> currentTok then
                        switchToken tokIdx index

                    let key = commentKey source item
                    expectedItems.Add key

                    if item.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                        if partKeysBuf.Count = 0 then
                            groupToken <- tokIdx
                            groupFirstOnToken <- firstCommentOnToken

                        partKeysBuf.Add key
                        partBodiesBuf.Add(key.Substring 4)
                        firstCommentOnToken <- false
                    else
                        flushGroup false false
                        tryCloseBridged ()
                        firstCommentOnToken <- false
                elif
                    item.Kind <> TriviaKind.WhitespaceTrivia
                    && item.Kind <> TriviaKind.EndOfLineTrivia
                then
                    while tokIdx < tokenCount
                          && (let tok = inputTokens[tokIdx] in
                              tok.TriviaStart + tok.LeadingCount + tok.TrailingCount <= index) do
                        tokIdx <- tokIdx + 1

                    if tokIdx <> currentTok then
                        switchToken tokIdx index

                    let isUsingTok = isUsingOrGlobalUsingToken source inputTokens currentTok

                    let isCondTrivia =
                        item.Kind = TriviaKind.IfDirectiveTrivia
                        || item.Kind = TriviaKind.ElifDirectiveTrivia
                        || item.Kind = TriviaKind.ElseDirectiveTrivia
                        || item.Kind = TriviaKind.EndIfDirectiveTrivia
                        || item.Kind = TriviaKind.DisabledTextTrivia

                    if isUsingTok && isCondTrivia then
                        if partKeysBuf.Count > 0 then
                            let isHeaderEnd =
                                item.Kind = TriviaKind.IfDirectiveTrivia && not sawIfOnToken

                            flushGroup false isHeaderEnd

                            if firstBridgedIdx < 0 then
                                firstBridgedIdx <- groups.Count - 1
                                canBridgeIfOnTok <- true
                                sawDisabledInBridge <- false
                            else
                                canBridgeIfOnTok <- false

                        if canBridgeIfOnTok && item.Kind = TriviaKind.DisabledTextTrivia then
                            sawDisabledInBridge <- true

                        if item.Kind = TriviaKind.IfDirectiveTrivia then
                            sawIfOnToken <- true
                    else
                        flushGroup false false
                        tryCloseBridged ()

                        if item.Kind = TriviaKind.IfDirectiveTrivia then
                            sawIfOnToken <- true

            let mutable hasLaterCommentOnCurrentTok = false
            let mutable nextNonWsIsFirstIf = false

            if partKeysBuf.Count > 0 && currentTok >= 0 && currentTok < tokenCount then
                let tok = inputTokens[currentTok]
                let tokEnd = tok.TriviaStart + tok.LeadingCount + tok.TrailingCount - 1
                let mutable seenNonWs = false

                for next = endLeft + 1 to tokEnd do
                    let nk = inputTrivia[next].Kind

                    if commentTrivia nk then
                        hasLaterCommentOnCurrentTok <- true

                    if
                        not seenNonWs
                        && nk <> TriviaKind.WhitespaceTrivia
                        && nk <> TriviaKind.EndOfLineTrivia
                    then
                        seenNonWs <- true

                        if nk = TriviaKind.IfDirectiveTrivia && not sawIfOnToken then
                            nextNonWsIsFirstIf <- true

            let finalLastOnTok = not hasLaterCommentOnCurrentTok

            let finalLastInHeader = (finalLastOnTok && not sawIfOnToken) || nextNonWsIsFirstIf

            flushGroup finalLastOnTok finalLastInHeader
            tryCloseBridged ()

        let actualItems = rawCommentKeysRange formatted outputTrivia startRight endRight
        let mutable hasMultiLineDoc = false

        for i = 0 to actualItems.Count - 1 do
            let key = actualItems[i]

            if
                not hasMultiLineDoc
                && key.StartsWith("/// ", StringComparison.Ordinal)
                && key.IndexOf('\n') >= 0
            then
                hasMultiLineDoc <- true

        let rawExpected = expectedItems.ToArray()
        let rawActual = actualItems.ToArray()
        Array.sortInPlaceWith (fun left right -> String.CompareOrdinal(left, right)) rawExpected
        Array.sortInPlaceWith (fun left right -> String.CompareOrdinal(left, right)) rawActual
        let mutable rawEqual = rawExpected.Length = rawActual.Length
        let mutable ri = 0

        while rawEqual && ri < rawExpected.Length do
            rawEqual <- String.Equals(rawExpected[ri], rawActual[ri], StringComparison.Ordinal)
            ri <- ri + 1

        if rawEqual then
            struct (rawExpected, rawActual)
        else if
            hasMultiLineDoc
            && (groups.Count > 1 || (groups.Count = 1 && groups[0].PartKeys.Length > 1))
        then
            let availUnmerged =
                Dictionary<string, int>(expectedItems.Count, StringComparer.Ordinal)

            for i = 0 to expectedItems.Count - 1 do
                let k = expectedItems[i]

                if k.StartsWith("/// ", StringComparison.Ordinal) then
                    match availUnmerged.TryGetValue k with
                    | true, c -> availUnmerged[k] <- c + 1
                    | false, _ -> availUnmerged[k] <- 1

            let remainingActual =
                Dictionary<string, int>(actualItems.Count, StringComparer.Ordinal)

            let multiIndices = ResizeArray<int>()

            for i = 0 to actualItems.Count - 1 do
                let k = actualItems[i]

                if k.StartsWith("/// ", StringComparison.Ordinal) then
                    match remainingActual.TryGetValue k with
                    | true, c -> remainingActual[k] <- c + 1
                    | false, _ -> remainingActual[k] <- 1

                    if k.IndexOf('\n') >= 0 then
                        multiIndices.Add i

            let mutable hasAnyExcess = false

            for idx = 0 to multiIndices.Count - 1 do
                let k = actualItems[multiIndices[idx]]
                let rem = remainingActual[k]

                let avail =
                    match availUnmerged.TryGetValue k with
                    | true, c -> c
                    | false, _ -> 0

                if rem > avail then
                    hasAnyExcess <- true

            if not hasAnyExcess then
                struct (rawExpected, rawActual)
            else
                let usedGroup = Array.zeroCreate<bool> groups.Count
                let replacements = Array.zeroCreate<string array> actualItems.Count
                let mutable anySplit = false
                let mutable minUsingDocToken = Int32.MaxValue
                let mutable maxUsingDocToken = -1

                for g = 0 to groups.Count - 1 do
                    if groups[g].TokenKind = TokenKind.UsingKeyword then
                        let gt = groups[g].TokenIndex

                        if gt < minUsingDocToken then
                            minUsingDocToken <- gt

                        if gt > maxUsingDocToken then
                            maxUsingDocToken <- gt

                let mutable usingRunsReady = false
                let mutable usingRunBase = 0
                let mutable usingRunIds: int array = null
                let mutable isFirstInRun: bool array = null
                let mutable runCount = 0
                let mutable runHeaderGroup: int array = null
                let mutable runHasSorted: bool array = null
                let mutable inRunFirstToken: int array = null

                let ensureUsingRuns () =
                    if not usingRunsReady && maxUsingDocToken >= 0 then
                        usingRunsReady <- true

                        let struct (inStart, inCanStart) =
                            if startLeft = 0 && startRight = 0 then
                                struct (0, true)
                            else
                                findUsingRunAnchor
                                    (input.TokenSpan())
                                    (source.AsSpan())
                                    minUsingDocToken

                        let struct (rBase, rIds, firstFlags, rCount, rHeader, rHasSorted,
                                    rFirstTokens) =
                            computeRunHeaderInfo
                                source
                                input
                                groups
                                inStart
                                inCanStart
                                maxUsingDocToken

                        usingRunBase <- rBase
                        usingRunIds <- rIds
                        isFirstInRun <- firstFlags
                        runCount <- rCount
                        runHeaderGroup <- rHeader
                        runHasSorted <- rHasSorted
                        inRunFirstToken <- rFirstTokens

                let isUncompactedHeader (grp: DocGroup) =
                    if grp.TokenKind = TokenKind.UsingKeyword && grp.IsBeforeIfOnToken then
                        ensureUsingRuns ()
                        let rel = grp.TokenIndex - usingRunBase

                        not (isNull isFirstInRun)
                        && rel >= 0
                        && rel < isFirstInRun.Length
                        && isFirstInRun[rel]
                    else
                        false

                let byCombinedKey =
                    Dictionary<string, ResizeArray<int>>(groups.Count, StringComparer.Ordinal)

                let unusedCombinedCount =
                    Dictionary<string, int>(groups.Count, StringComparer.Ordinal)

                for pass = 0 to 1 do
                    let wantBridged = pass = 1

                    for g = 0 to groups.Count - 1 do
                        let grp = groups[g]

                        if
                            grp.PartKeys.Length > 1
                            && (grp.ExcludeGroupA >= 0) = wantBridged
                            && not (isUncompactedHeader grp)
                        then
                            let key = grp.CombinedKey

                            match byCombinedKey.TryGetValue key with
                            | true, list ->
                                list.Add g
                                unusedCombinedCount[key] <- unusedCombinedCount[key] + 1
                            | false, _ ->
                                let list = ResizeArray<int>(4)
                                list.Add 2
                                list.Add 2
                                list.Add g
                                byCombinedKey[key] <- list
                                unusedCombinedCount[key] <- 1

                let sameParts (a: string array) (b: string array) =
                    if isNull a || isNull b || a.Length <> b.Length then
                        false
                    else
                        let mutable eq = true
                        let mutable p = 0

                        while eq && p < a.Length do
                            eq <- String.Equals(a[p], b[p], StringComparison.Ordinal)
                            p <- p + 1

                        eq

                let mutable mergedHashReady = false
                let mutable itemMergeRun: int array = null
                let mutable runCandidates: ResizeArray<struct (int * int * int * bool)> array = null
                let mutable groupMergedRun: int array = null
                let mutable unusedMergedCount: Dictionary<string, int> = null

                let isRunKeyActive (r: int) (key: string) =
                    let cands = runCandidates[r]
                    let mutable k = 0
                    let mutable active = false

                    while not active && k < cands.Count do
                        let struct (itemIdx, hC, sC, _) = cands[k]

                        if
                            isNull replacements[itemIdx]
                            && not usedGroup[hC]
                            && not usedGroup[sC]
                            && String.Equals(actualItems[itemIdx], key, StringComparison.Ordinal)
                        then
                            active <- true

                        k <- k + 1

                    active

                let isFirstOfKeyInRun
                    (cands: ResizeArray<struct (int * int * int * bool)>)
                    (idx: int)
                    (mk: string)
                    =
                    let mutable prev = 0
                    let mutable dup = false

                    while not dup && prev < idx do
                        let struct (pItem, _, _, _) = cands[prev]

                        if String.Equals(actualItems[pItem], mk, StringComparison.Ordinal) then
                            dup <- true

                        prev <- prev + 1

                    not dup

                let adjustRunMergedCount (r: int) (delta: int) =
                    let cands = runCandidates[r]

                    for cIdx = 0 to cands.Count - 1 do
                        let struct (itemIdx, _, _, _) = cands[cIdx]
                        let mk = actualItems[itemIdx]

                        if isFirstOfKeyInRun cands cIdx mk && isRunKeyActive r mk then
                            match unusedMergedCount.TryGetValue mk with
                            | true, c -> unusedMergedCount[mk] <- c + delta
                            | false, _ -> unusedMergedCount[mk] <- delta

                let usedTrail = ResizeArray<int>()

                let markOne (idx: int) =
                    if idx >= 0 && not usedGroup[idx] then
                        let r =
                            if not (isNull groupMergedRun) then
                                groupMergedRun[idx]
                            else
                                -1

                        if r >= 0 then
                            adjustRunMergedCount r -1

                        usedGroup[idx] <- true
                        usedTrail.Add idx
                        let grp = groups[idx]

                        if grp.PartKeys.Length > 1 && not (isUncompactedHeader grp) then
                            let ck = grp.CombinedKey

                            match unusedCombinedCount.TryGetValue ck with
                            | true, c -> unusedCombinedCount[ck] <- c - 1
                            | false, _ -> ()

                        if r >= 0 then
                            adjustRunMergedCount r 1

                let markUsed (g: int) =
                    markOne g
                    markOne groups[g].ExcludeGroupA
                    markOne groups[g].ExcludeGroupB

                let undoUsedTo (savedCount: int) =
                    for t = usedTrail.Count - 1 downto savedCount do
                        let idx = usedTrail[t]

                        let r =
                            if not (isNull groupMergedRun) then
                                groupMergedRun[idx]
                            else
                                -1

                        if r >= 0 then
                            adjustRunMergedCount r -1

                        usedGroup[idx] <- false
                        let grp = groups[idx]

                        if grp.PartKeys.Length > 1 && not (isUncompactedHeader grp) then
                            let ck = grp.CombinedKey

                            match unusedCombinedCount.TryGetValue ck with
                            | true, c -> unusedCombinedCount[ck] <- c + 1
                            | false, _ -> ()

                        if r >= 0 then
                            adjustRunMergedCount r 1

                    if usedTrail.Count > savedCount then
                        usedTrail.RemoveRange(savedCount, usedTrail.Count - savedCount)

                let ensureMergedHash () =
                    if not mergedHashReady then
                        mergedHashReady <- true
                        ensureUsingRuns ()

                        if runCount > 0 then
                            let inTrivia = input.TriviaSpan()
                            let outTrivia = output.TriviaSpan()
                            let inTokens = input.TokenSpan()
                            let outputTokens = output.TokenSpan()
                            let outTokenCount = outputTokens.Length
                            let tokIndices = Array.create actualItems.Count -1

                            let mutable outTokIdx =
                                if startRight > 0 then
                                    tokenIndexForTrivia outputTokens startRight
                                else
                                    0

                            let mutable itemIdx = 0
                            let mutable minOutUsingTok = Int32.MaxValue
                            let mutable maxOutUsingTok = -1

                            if startRight <= endRight then
                                for index = startRight to endRight do
                                    let item = outTrivia[index]

                                    if commentTrivia item.Kind then
                                        while outTokIdx < outTokenCount
                                              && (let tok = outputTokens[outTokIdx] in

                                                  tok.TriviaStart
                                                  + tok.LeadingCount
                                                  + tok.TrailingCount
                                                  <= index) do
                                            outTokIdx <- outTokIdx + 1

                                        if
                                            outTokIdx < outTokenCount
                                            && index <
                                                outputTokens[outTokIdx].TriviaStart
                                                + outputTokens[outTokIdx].LeadingCount
                                        then
                                            tokIndices[itemIdx] <- outTokIdx

                                            if
                                                isUsingOrGlobalUsingToken
                                                    formatted
                                                    outputTokens
                                                    outTokIdx
                                            then
                                                if outTokIdx < minOutUsingTok then
                                                    minOutUsingTok <- outTokIdx

                                                if outTokIdx > maxOutUsingTok then
                                                    maxOutUsingTok <- outTokIdx

                                        itemIdx <- itemIdx + 1

                            if maxOutUsingTok >= 0 then
                                let struct (outStart, outCanStart) =
                                    if startLeft = 0 && startRight = 0 then
                                        struct (0, true)
                                    else
                                        findUsingRunAnchor
                                            outputTokens
                                            (formatted.AsSpan())
                                            minOutUsingTok

                                let struct (outRunBase, outRunIds, outFirstFlags, outRunCount,
                                            outRunFirstToken, _) =
                                    computeUsingRunIdsRange
                                        formatted
                                        output
                                        outStart
                                        outCanStart
                                        maxOutUsingTok

                                let usableRuns = min runCount outRunCount

                                if usableRuns > 0 then
                                    let imRun = Array.create actualItems.Count -1

                                    let runSuffixMap =
                                        Array.zeroCreate<Dictionary<string, int>> usableRuns

                                    let runMoved = Array.zeroCreate<int> usableRuns
                                    let mutable anyRun = false

                                    for m = 0 to multiIndices.Count - 1 do
                                        let i = multiIndices[m]
                                        let outTok = tokIndices[i]
                                        let outRel = outTok - outRunBase

                                        if
                                            outRel >= 0
                                            && outRel < outRunIds.Length
                                            && outFirstFlags[outRel]
                                        then
                                            let r = outRunIds[outRel]

                                            if
                                                r >= 0
                                                && r < usableRuns
                                                && runHeaderGroup[r] >= 0
                                                && runHasSorted[r]
                                            then
                                                let moved =
                                                    if runMoved[r] <> 0 then
                                                        runMoved[r] > 0
                                                    else
                                                        let inFirstTok = inRunFirstToken[r]
                                                        let outFirstTok = outRunFirstToken[r]

                                                        let mv =
                                                            inFirstTok >= 0
                                                            && outFirstTok >= 0
                                                            && (not (
                                                                    sameUsingDirective
                                                                        source
                                                                        inTokens
                                                                        inFirstTok
                                                                        formatted
                                                                        outputTokens
                                                                        outFirstTok
                                                                )
                                                                || countIfOrSingleLineComments
                                                                    inTrivia
                                                                    inTokens[inFirstTok]
                                                                    >
                                                                    countIfOrSingleLineComments
                                                                        outTrivia
                                                                        outputTokens[outFirstTok])

                                                        runMoved[r] <- if mv then 1 else -1
                                                        mv

                                                if moved then
                                                    let h = runHeaderGroup[r]
                                                    let hParts = groups[h].PartBodies
                                                    let hBody = hParts[hParts.Length - 1]
                                                    let hLen = hBody.Length
                                                    let bodySpan = actualItems[i].AsSpan 4

                                                    if
                                                        bodySpan.Length > hLen + 1
                                                        && bodySpan[hLen] = '\n'
                                                        && bodySpan
                                                            .Slice(0, hLen)
                                                            .SequenceEqual(hBody.AsSpan())
                                                    then
                                                        anyRun <- true

                                                        if isNull runSuffixMap[r] then
                                                            runSuffixMap[r] <-
                                                                Dictionary<string, int>(
                                                                    2,
                                                                    StringComparer.Ordinal
                                                                )

                                                        let suffix =
                                                            actualItems[i].Substring(4 + hLen + 1)

                                                        runSuffixMap[r].TryAdd(suffix, i) |> ignore

                                    if anyRun then
                                        let candsPerRun =
                                            Array.zeroCreate<
                                                ResizeArray<struct (int * int * int * bool)>
                                             >
                                                usableRuns

                                        let grpRun = Array.create groups.Count -1
                                        let mutable anyCand = false

                                        for pass = 0 to 2 do
                                            let wantFirstSorted = pass = 2
                                            let wantSinglePart = pass = 0

                                            for bPass = 0 to 1 do
                                                let wantBridged = bPass = 1

                                                for g = 0 to groups.Count - 1 do
                                                    let grp = groups[g]
                                                    let isSinglePart = grp.PartKeys.Length = 1

                                                    let passMatch =
                                                        if wantFirstSorted then
                                                            not isSinglePart
                                                            && grp.ExcludeGroupB < 0
                                                        else
                                                            isSinglePart = wantSinglePart

                                                    if
                                                        passMatch
                                                        && (grp.ExcludeGroupA >= 0) = wantBridged
                                                        && grp.IsFirstOnToken
                                                    then
                                                        let tokIdx = grp.TokenIndex
                                                        let inRel = tokIdx - usingRunBase

                                                        if
                                                            inRel >= 0
                                                            && inRel < usingRunIds.Length
                                                            && not isFirstInRun[inRel]
                                                        then
                                                            let r = usingRunIds[inRel]

                                                            if
                                                                r >= 0
                                                                && r < usableRuns
                                                                && not (isNull runSuffixMap[r])
                                                            then
                                                                let h = runHeaderGroup[r]

                                                                if
                                                                    h >= 0
                                                                    && tokIdx > groups[h].TokenIndex
                                                                    && sameUsingDirective
                                                                        source
                                                                        inTokens
                                                                        tokIdx
                                                                        formatted
                                                                        outputTokens
                                                                        outRunFirstToken[r]
                                                                then
                                                                    let sBody =
                                                                        if wantFirstSorted then
                                                                            grp.PartBodies[0]
                                                                        else
                                                                            grp.CombinedBody

                                                                    match
                                                                        runSuffixMap[r].TryGetValue
                                                                            sBody
                                                                    with
                                                                    | true, itemIdx ->
                                                                        let mutable list =
                                                                            candsPerRun[r]

                                                                        if isNull list then
                                                                            list <-
                                                                                ResizeArray<
                                                                                    struct (int *
                                                                                    int *
                                                                                    int *
                                                                                    bool)
                                                                                 >(
                                                                                    2
                                                                                )

                                                                            candsPerRun[r] <- list

                                                                        if list.Count < 16 then
                                                                            let mutable sameCount =
                                                                                0

                                                                            for cIdx = 0 to list
                                                                                                .Count
                                                                                            - 1 do
                                                                                let struct (cItem, _,
                                                                                            cS,
                                                                                            cFirst) =
                                                                                    list[cIdx]

                                                                                if
                                                                                    cItem = itemIdx
                                                                                    && cFirst =
                                                                                        wantFirstSorted
                                                                                    && (groups[cS]
                                                                                            .ExcludeGroupA
                                                                                        >= 0)
                                                                                        =
                                                                                        wantBridged
                                                                                    && sameParts
                                                                                        groups[cS]
                                                                                            .PartKeys
                                                                                        grp.PartKeys
                                                                                then
                                                                                    sameCount <-
                                                                                        sameCount
                                                                                        + 1

                                                                            if sameCount < 2 then
                                                                                list.Add(
                                                                                    struct (itemIdx,
                                                                                            h,
                                                                                            g,
                                                                                            wantFirstSorted)
                                                                                )

                                                                                imRun[itemIdx] <- r
                                                                                grpRun[h] <- r
                                                                                grpRun[g] <- r
                                                                                anyCand <- true
                                                                    | false, _ -> ()

                                        if anyCand then
                                            itemMergeRun <- imRun
                                            runCandidates <- candsPerRun
                                            groupMergedRun <- grpRun

                                            unusedMergedCount <-
                                                Dictionary<string, int>(
                                                    usableRuns,
                                                    StringComparer.Ordinal
                                                )

                                            for r = 0 to usableRuns - 1 do
                                                if not (isNull candsPerRun[r]) then
                                                    adjustRunMergedCount r 1

                let checkKeySupply
                    (k: string)
                    (neededFromAvail: int)
                    (requireSurplusForMulti: bool)
                    =
                    let avail =
                        match availUnmerged.TryGetValue k with
                        | true, c -> c
                        | false, _ -> 0

                    if avail < neededFromAvail then
                        false
                    else
                        let rem =
                            match remainingActual.TryGetValue k with
                            | true, c -> c
                            | false, _ -> 0

                        if k.IndexOf('\n') < 0 then
                            avail - rem >= neededFromAvail
                        else
                            let combAfter =
                                match unusedCombinedCount.TryGetValue k with
                                | true, c -> c
                                | false, _ -> 0

                            let supplyAfter = (avail - neededFromAvail) + combAfter

                            if requireSurplusForMulti && neededFromAvail > 0 then
                                avail - rem >= neededFromAvail && supplyAfter >= rem
                            elif supplyAfter >= rem then
                                true
                            else
                                let mergedAfter =
                                    if maxUsingDocToken >= 0 then
                                        ensureMergedHash ()

                                        if not (isNull unusedMergedCount) then
                                            match unusedMergedCount.TryGetValue k with
                                            | true, c -> c
                                            | false, _ -> 0
                                        else
                                            0
                                    else
                                        0

                                supplyAfter + mergedAfter >= rem

                let checkMarkedGroupsSupply
                    (savedTrail: int)
                    (currentKey: string)
                    (requireSurplusForMulti: bool)
                    =
                    let mutable ok = true
                    let mutable t = savedTrail

                    while ok && t < usedTrail.Count do
                        let idx = usedTrail[t]
                        let grp = groups[idx]

                        if grp.PartKeys.Length > 1 && not (isUncompactedHeader grp) then
                            let ck = grp.CombinedKey

                            if not (String.Equals(ck, currentKey, StringComparison.Ordinal)) then
                                if not (checkKeySupply ck 0 requireSurplusForMulti) then
                                    ok <- false

                        t <- t + 1

                    ok

                let mutable partCounts: Dictionary<string, int> = null

                let canConsumeParts
                    (savedTrail: int)
                    (currentKey: string)
                    (rep: string array)
                    (requireSurplusForMulti: bool)
                    =
                    if
                        not (checkMarkedGroupsSupply savedTrail currentKey requireSurplusForMulti)
                    then
                        false
                    elif rep.Length <= 4 then
                        let mutable ok = true
                        let mutable p = 0

                        while ok && p < rep.Length do
                            let pk = rep[p]
                            let mutable needed = 1

                            for q = 0 to p - 1 do
                                if String.Equals(rep[q], pk, StringComparison.Ordinal) then
                                    needed <- needed + 1

                            if not (checkKeySupply pk needed requireSurplusForMulti) then
                                ok <- false

                            p <- p + 1

                        ok
                    else
                        if isNull partCounts then
                            partCounts <-
                                Dictionary<string, int>(rep.Length, StringComparer.Ordinal)
                        else
                            partCounts.Clear()

                        for p = 0 to rep.Length - 1 do
                            let pk = rep[p]

                            match partCounts.TryGetValue pk with
                            | true, c -> partCounts[pk] <- c + 1
                            | false, _ -> partCounts[pk] <- 1

                        let mutable ok = true
                        use mutable e = partCounts.GetEnumerator()

                        while ok && e.MoveNext() do
                            let kv = e.Current

                            if not (checkKeySupply kv.Key kv.Value requireSurplusForMulti) then
                                ok <- false

                        ok

                let canConsumeMergedParts
                    (savedTrail: int)
                    (currentKey: string)
                    (headerKey: string)
                    (sPk: string array)
                    (isFirstSorted: bool)
                    (requireSurplusForMulti: bool)
                    =
                    if
                        not (checkMarkedGroupsSupply savedTrail currentKey requireSurplusForMulti)
                    then
                        false
                    else
                        let sCount = if isFirstSorted then 1 else sPk.Length
                        let total = 1 + sCount

                        if total <= 4 then
                            let mutable ok = true
                            let mutable p = 0

                            while ok && p < total do
                                let pk = if p = 0 then headerKey else sPk[p - 1]
                                let mutable needed = 1

                                for q = 0 to p - 1 do
                                    let qk = if q = 0 then headerKey else sPk[q - 1]

                                    if String.Equals(qk, pk, StringComparison.Ordinal) then
                                        needed <- needed + 1

                                if not (checkKeySupply pk needed requireSurplusForMulti) then
                                    ok <- false

                                p <- p + 1

                            ok
                        else
                            if isNull partCounts then
                                partCounts <- Dictionary<string, int>(total, StringComparer.Ordinal)
                            else
                                partCounts.Clear()

                            partCounts[headerKey] <- 1

                            for p = 0 to sCount - 1 do
                                let pk = sPk[p]

                                match partCounts.TryGetValue pk with
                                | true, c -> partCounts[pk] <- c + 1
                                | false, _ -> partCounts[pk] <- 1

                            let mutable ok = true
                            use mutable e = partCounts.GetEnumerator()

                            while ok && e.MoveNext() do
                                let kv = e.Current

                                if not (checkKeySupply kv.Key kv.Value requireSurplusForMulti) then
                                    ok <- false

                            ok

                let consumeParts (i: int) (key: string) (rep: string array) =
                    let r = if not (isNull itemMergeRun) then itemMergeRun[i] else -1

                    if r >= 0 && not (isNull runCandidates[r]) then
                        adjustRunMergedCount r -1

                    replacements[i] <- rep
                    remainingActual[key] <- remainingActual[key] - 1

                    for p = 0 to rep.Length - 1 do
                        let pk = rep[p]
                        availUnmerged[pk] <- availUnmerged[pk] - 1

                    if r >= 0 && not (isNull runCandidates[r]) then
                        adjustRunMergedCount r 1

                let unconsumeParts (i: int) (key: string) (rep: string array) =
                    let r = if not (isNull itemMergeRun) then itemMergeRun[i] else -1

                    if r >= 0 && not (isNull runCandidates[r]) then
                        adjustRunMergedCount r -1

                    replacements[i] <- null
                    remainingActual[key] <- remainingActual[key] + 1

                    for p = 0 to rep.Length - 1 do
                        let pk = rep[p]
                        availUnmerged[pk] <- availUnmerged[pk] + 1

                    if r >= 0 && not (isNull runCandidates[r]) then
                        adjustRunMergedCount r 1

                if maxUsingDocToken >= 0 then
                    ensureMergedHash ()

                let nextDiffInList = Array.zeroCreate<int> groups.Count

                let isPlainGroup (g: int) =
                    groups[g].ExcludeGroupA < 0 && (isNull groupMergedRun || groupMergedRun[g] < 0)

                let mutable plainBuckets: Dictionary<string, ResizeArray<int>> = null
                let mutable plainKeyOrder: ResizeArray<string> = null
                let mutable nonPlainBuf: ResizeArray<int> = null

                for kv in byCombinedKey do
                    let list = kv.Value
                    let count = list.Count

                    if count > 4 then
                        let firstG = list[2]
                        let firstPks = groups[firstG].PartKeys
                        let mutable allSamePlain = isPlainGroup firstG
                        let mutable idx = 3

                        while allSamePlain && idx < count do
                            let g = list[idx]

                            if not (isPlainGroup g && sameParts groups[g].PartKeys firstPks) then
                                allSamePlain <- false

                            idx <- idx + 1

                        if not allSamePlain then
                            if isNull plainBuckets then
                                plainBuckets <-
                                    Dictionary<string, ResizeArray<int>>(4, StringComparer.Ordinal)

                                plainKeyOrder <- ResizeArray<string>(4)
                                nonPlainBuf <- ResizeArray<int>(4)
                            else
                                plainBuckets.Clear()
                                plainKeyOrder.Clear()
                                nonPlainBuf.Clear()

                            for k = 2 to count - 1 do
                                let g = list[k]

                                if isPlainGroup g then
                                    let pks = groups[g].PartKeys
                                    let bKey = String.Join("\u0000", pks)

                                    match plainBuckets.TryGetValue bKey with
                                    | true, bList -> bList.Add g
                                    | false, _ ->
                                        let bList = ResizeArray<int>(2)
                                        bList.Add g
                                        plainBuckets[bKey] <- bList
                                        plainKeyOrder.Add bKey
                                else
                                    nonPlainBuf.Add g

                            let mutable writeIdx = 2

                            for b = 0 to plainKeyOrder.Count - 1 do
                                let bList = plainBuckets[plainKeyOrder[b]]

                                for j = 0 to bList.Count - 1 do
                                    list[writeIdx] <- bList[j]
                                    writeIdx <- writeIdx + 1

                            for j = 0 to nonPlainBuf.Count - 1 do
                                list[writeIdx] <- nonPlainBuf[j]
                                writeIdx <- writeIdx + 1

                    let mutable nextDiff = count

                    for idx = count - 1 downto 2 do
                        let g = list[idx]

                        if idx + 1 < count then
                            let gNext = list[idx + 1]

                            if
                                not (
                                    isPlainGroup g
                                    && isPlainGroup gNext
                                    && sameParts groups[g].PartKeys groups[gNext].PartKeys
                                )
                            then
                                nextDiff <- idx + 1

                        nextDiffInList[g] <- nextDiff

                let tryMatchCombined (i: int) (key: string) (requireSurplusForMulti: bool) =
                    match byCombinedKey.TryGetValue key with
                    | true, list ->
                        let headSlot = if requireSurplusForMulti then 1 else 0
                        let mutable idx = list[headSlot]
                        let mutable found = false

                        while idx < list.Count && not found do
                            let gCand = list[idx]

                            if usedGroup[gCand] then
                                idx <- idx + 1
                                list[headSlot] <- idx
                            else
                                let pks = groups[gCand].PartKeys
                                let savedTrail = usedTrail.Count
                                markUsed gCand

                                if canConsumeParts savedTrail key pks requireSurplusForMulti then
                                    anySplit <- true
                                    consumeParts i key pks
                                    list[headSlot] <- idx + 1
                                    found <- true
                                else
                                    undoUsedTo savedTrail
                                    idx <- nextDiffInList[gCand]
                                    list[headSlot] <- idx

                        found
                    | false, _ -> false

                let tryMatchMerged (i: int) (key: string) (requireSurplusForMulti: bool) =
                    ensureMergedHash ()

                    if not (isNull itemMergeRun) then
                        let r = itemMergeRun[i]

                        if r >= 0 && not (isNull runCandidates[r]) then
                            let cands = runCandidates[r]
                            let mutable idx = 0
                            let mutable foundPair = false

                            while idx < cands.Count && not foundPair do
                                let struct (itemIdx, hCand, sCand, isFirstSorted) = cands[idx]

                                if itemIdx = i && not usedGroup[hCand] && not usedGroup[sCand] then
                                    let hPk = groups[hCand].PartKeys
                                    let headerKey = hPk[hPk.Length - 1]
                                    let sPk = groups[sCand].PartKeys
                                    let savedTrail = usedTrail.Count
                                    markUsed hCand
                                    markUsed sCand

                                    if
                                        canConsumeMergedParts
                                            savedTrail
                                            key
                                            headerKey
                                            sPk
                                            isFirstSorted
                                            requireSurplusForMulti
                                    then
                                        anySplit <- true

                                        let rep =
                                            if isFirstSorted then
                                                [| headerKey; sPk[0] |]
                                            else
                                                let arr = Array.zeroCreate<string>(1 + sPk.Length)

                                                arr[0] <- headerKey
                                                Array.Copy(sPk, 0, arr, 1, sPk.Length)
                                                arr

                                        consumeParts i key rep
                                        foundPair <- true
                                    else
                                        undoUsedTo savedTrail

                                idx <- idx + 1

                            foundPair
                        else
                            false
                    else
                        false

                let order = multiIndices.ToArray()

                Array.sortInPlaceWith
                    (fun a b ->
                        let cmp = actualItems[b].Length.CompareTo(actualItems[a].Length)

                        if cmp <> 0 then
                            cmp
                        else
                            let kcmp = String.CompareOrdinal(actualItems[a], actualItems[b])

                            if kcmp <> 0 then
                                kcmp
                            else
                                let ma =
                                    if not (isNull itemMergeRun) && itemMergeRun[a] >= 0 then
                                        0
                                    else
                                        1

                                let mb =
                                    if not (isNull itemMergeRun) && itemMergeRun[b] >= 0 then
                                        0
                                    else
                                        1

                                let mcmp = ma.CompareTo mb
                                if mcmp <> 0 then mcmp else a.CompareTo b)
                    order

                let mutable allMatched = true
                let mutable ordIdx = 0

                while allMatched && ordIdx < order.Length do
                    let i = order[ordIdx]
                    let key = actualItems[i]
                    let rem = remainingActual[key]

                    let avail =
                        match availUnmerged.TryGetValue key with
                        | true, c -> c
                        | false, _ -> 0

                    if rem > avail then
                        let mutable matched =
                            if maxUsingDocToken >= 0 then
                                tryMatchMerged i key true
                            else
                                false

                        if not matched then
                            matched <- tryMatchCombined i key true

                        if not matched && maxUsingDocToken >= 0 then
                            matched <- tryMatchMerged i key false

                        if not matched then
                            matched <- tryMatchCombined i key false

                        if not matched then
                            allMatched <- false

                    ordIdx <- ordIdx + 1

                let countsBalanced () =
                    let mutable eq = true
                    use mutable e = availUnmerged.GetEnumerator()

                    while eq && e.MoveNext() do
                        let kv = e.Current

                        let rem =
                            match remainingActual.TryGetValue kv.Key with
                            | true, c -> c
                            | false, _ -> 0

                        if kv.Value <> rem then
                            eq <- false

                    if eq then
                        use mutable e2 = remainingActual.GetEnumerator()

                        while eq && e2.MoveNext() do
                            let kv = e2.Current

                            let avail =
                                match availUnmerged.TryGetValue kv.Key with
                                | true, c -> c
                                | false, _ -> 0

                            if kv.Value <> avail then
                                eq <- false

                    eq

                if not allMatched || not (countsBalanced ()) then
                    anySplit <- false

                    if order.Length <= 512 then
                        for i = 0 to actualItems.Count - 1 do
                            let rep = replacements[i]

                            if not (isNull rep) then
                                unconsumeParts i actualItems[i] rep

                        undoUsedTo 0

                        for kv in byCombinedKey do
                            kv.Value[0] <- 2
                            kv.Value[1] <- 2

                        let mutable backtrackSteps = 0
                        let maxBacktrackSteps = 512

                        let rec solve (ordIdx: int) =
                            if ordIdx >= order.Length then
                                countsBalanced ()
                            elif backtrackSteps >= maxBacktrackSteps then
                                false
                            else
                                let i = order[ordIdx]
                                let key = actualItems[i]
                                let rem = remainingActual[key]

                                let avail =
                                    match availUnmerged.TryGetValue key with
                                    | true, c -> c
                                    | false, _ -> 0

                                let isLastOfKey =
                                    ordIdx + 1 >= order.Length
                                    || not (
                                        String.Equals(
                                            actualItems[order[ordIdx + 1]],
                                            key,
                                            StringComparison.Ordinal
                                        )
                                    )

                                if rem <= avail then
                                    if isLastOfKey && rem < avail then
                                        backtrackSteps <- backtrackSteps + 1
                                        false
                                    else
                                        solve (ordIdx + 1)
                                else
                                    let mutable solved = false

                                    if
                                        maxUsingDocToken >= 0 && backtrackSteps < maxBacktrackSteps
                                    then
                                        ensureMergedHash ()

                                        if not (isNull itemMergeRun) then
                                            let r = itemMergeRun[i]

                                            if r >= 0 && not (isNull runCandidates[r]) then
                                                let cands = runCandidates[r]
                                                let mutable idx = 0

                                                while idx < cands.Count
                                                      && not solved
                                                      && backtrackSteps < maxBacktrackSteps do
                                                    let struct (itemIdx, hCand, sCand, isFirstSorted) =
                                                        cands[idx]

                                                    if
                                                        itemIdx = i
                                                        && not usedGroup[hCand]
                                                        && not usedGroup[sCand]
                                                    then
                                                        let hPk = groups[hCand].PartKeys
                                                        let headerKey = hPk[hPk.Length - 1]
                                                        let sPk = groups[sCand].PartKeys
                                                        let savedTrail = usedTrail.Count
                                                        markUsed hCand
                                                        markUsed sCand

                                                        if
                                                            canConsumeMergedParts
                                                                savedTrail
                                                                key
                                                                headerKey
                                                                sPk
                                                                isFirstSorted
                                                                false
                                                        then
                                                            let rep =
                                                                if isFirstSorted then
                                                                    [| headerKey; sPk[0] |]
                                                                else
                                                                    let arr =
                                                                        Array.zeroCreate<string>(
                                                                            1 + sPk.Length
                                                                        )

                                                                    arr[0] <- headerKey

                                                                    Array.Copy(
                                                                        sPk,
                                                                        0,
                                                                        arr,
                                                                        1,
                                                                        sPk.Length
                                                                    )

                                                                    arr

                                                            consumeParts i key rep

                                                            if solve (ordIdx + 1) then
                                                                anySplit <- true
                                                                solved <- true
                                                            else
                                                                unconsumeParts i key rep
                                                                undoUsedTo savedTrail

                                                                backtrackSteps <- backtrackSteps + 1
                                                        else
                                                            undoUsedTo savedTrail
                                                            backtrackSteps <- backtrackSteps + 1

                                                    idx <- idx + 1

                                    if not solved then
                                        match byCombinedKey.TryGetValue key with
                                        | true, list ->
                                            let mutable idx = 2

                                            while idx < list.Count
                                                  && not solved
                                                  && backtrackSteps < maxBacktrackSteps do
                                                let gCand = list[idx]

                                                if usedGroup[gCand] then
                                                    idx <- idx + 1
                                                else
                                                    let pks = groups[gCand].PartKeys
                                                    let savedTrail = usedTrail.Count
                                                    markUsed gCand

                                                    if canConsumeParts savedTrail key pks false then
                                                        consumeParts i key pks

                                                        if solve (ordIdx + 1) then
                                                            anySplit <- true
                                                            solved <- true
                                                        else
                                                            unconsumeParts i key pks
                                                            undoUsedTo savedTrail
                                                            backtrackSteps <- backtrackSteps + 1
                                                            idx <- nextDiffInList[gCand]
                                                    else
                                                        undoUsedTo savedTrail
                                                        backtrackSteps <- backtrackSteps + 1
                                                        idx <- nextDiffInList[gCand]
                                        | false, _ -> ()

                                    solved

                        solve 0 |> ignore

                if anySplit then
                    let expanded = ResizeArray<string>(actualItems.Count + 2)

                    for i = 0 to actualItems.Count - 1 do
                        let rep = replacements[i]

                        if not (isNull rep) then
                            for j = 0 to rep.Length - 1 do
                                expanded.Add rep[j]
                        else
                            expanded.Add actualItems[i]

                    let actual = expanded.ToArray()

                    Array.sortInPlaceWith
                        (fun left right -> String.CompareOrdinal(left, right))
                        actual

                    struct (rawExpected, actual)
                else
                    struct (rawExpected, rawActual)
        else
            struct (rawExpected, rawActual)

    let private commentKeyPairFull
        (source: string)
        (input: TokenBuffer)
        (formatted: string)
        (output: TokenBuffer)
        =
        commentKeyPair
            source
            input
            0
            input.LastCommentTrivia
            formatted
            output
            0
            output.LastCommentTrivia

    let private quoteKey (key: string) =
        let text = key.Replace("\n", "\\n")

        if text.Length > 72 then
            "\"" + text.Substring(0, 72) + "...\""
        else
            "\"" + text + "\""

    let inline private isCloseDelimiter (kind: TokenKind) =
        kind = TokenKind.CloseBraceToken
        || kind = TokenKind.CloseBracketToken
        || kind = TokenKind.CloseParenToken

    let inline private greaterWidth (kind: TokenKind) =
        match kind with
        | TokenKind.GreaterThanToken -> 1
        | TokenKind.GreaterThanGreaterThanToken -> 2
        | TokenKind.GreaterThanGreaterThanGreaterThanToken -> 3
        | _ -> 0

    let private sliceHasComment
        (buf: TokenBuffer)
        (triv: ReadOnlySpan<Trivia>)
        (start: int)
        (count: int)
        =
        if count <= 0 || start > buf.LastCommentTrivia then
            false
        elif count = 1 then
            commentTrivia triv[start].Kind
        else
            let mutable k = start
            let lim = min (buf.LastCommentTrivia + 1) (start + count)

            while k < lim && not (commentTrivia triv[k].Kind) do
                k <- k + 1

            k < lim

    let inline private gapRangeHasComment
        (buf: TokenBuffer)
        (triv: ReadOnlySpan<Trivia>)
        (s0: int)
        (c0: int)
        (s1: int)
        (c1: int)
        (s2: int)
        (c2: int)
        (s3: int)
        (c3: int)
        =
        let mutable lo = Int32.MaxValue
        let mutable hi = Int32.MinValue

        if c0 > 0 then
            lo <- min lo s0
            hi <- max hi (s0 + c0)

        if c1 > 0 then
            lo <- min lo s1
            hi <- max hi (s1 + c1)

        if c2 > 0 then
            lo <- min lo s2
            hi <- max hi (s2 + c2)

        if c3 > 0 then
            lo <- min lo s3
            hi <- max hi (s3 + c3)

        if lo >= hi || lo > buf.LastCommentTrivia then
            false
        else
            let lim = min (buf.LastCommentTrivia + 1) hi
            let mutable k = lo

            while k < lim && not (commentTrivia triv[k].Kind) do
                k <- k + 1

            k < lim

    let private formatCommentKey (item: Trivia) (text: ReadOnlySpan<char>) =
        quoteKey (String(text.Slice(item.Start, item.Length)).TrimEnd('\r', '\n'))

    let private firstCommentKey
        (text: ReadOnlySpan<char>)
        (triv: ReadOnlySpan<Trivia>)
        (start: int)
        (count: int)
        =
        let mutable k = start
        let lim = start + count

        while k < lim && not (commentTrivia triv[k].Kind) do
            k <- k + 1

        if k < lim then formatCommentKey triv[k] text else ""

    let private rangeHasComment (buf: TokenBuffer) (startIdx: int) (endIdx: int) =
        if startIdx > endIdx || startIdx > buf.LastCommentTrivia || endIdx < 0 then
            false
        else
            let triv = buf.TriviaSpan()
            let lim = min (buf.LastCommentTrivia + 1) (endIdx + 1)
            let mutable idx = startIdx

            while idx < lim && not (commentTrivia triv[idx].Kind) do
                idx <- idx + 1

            idx < lim

    let private symmetricCommentDiff (expected: string array) (actual: string array) =
        let mutable left = 0
        let mutable right = 0
        let mutable lost = 0
        let mutable gained = 0
        let mutable lostKey = ""
        let mutable gainedKey = ""

        while left < expected.Length || right < actual.Length do
            let order =
                if left >= expected.Length then 1
                elif right >= actual.Length then -1
                else String.CompareOrdinal(expected[left], actual[right])

            if order = 0 then
                left <- left + 1
                right <- right + 1
            elif order < 0 then
                if lost = 0 then
                    lostKey <- quoteKey expected[left]

                lost <- lost + 1
                left <- left + 1
            else
                if gained = 0 then
                    gainedKey <- quoteKey actual[right]

                gained <- gained + 1
                right <- right + 1

        struct (lost, gained, lostKey, gainedKey)

    let private checkGapComments
        (allowMergedDoc: bool)
        (allowDirectiveSpanning: bool)
        (deferredRawSpans: ResizeArray<struct (int * int * int * int)>)
        (lSrcSpan: ReadOnlySpan<char>)
        (rSrcSpan: ReadOnlySpan<char>)
        (lBuf: TokenBuffer)
        (rBuf: TokenBuffer)
        (lTokIdx: int)
        (lS0: int, lC0: int, lS1: int, lC1: int, lS2: int, lC2: int, lS3: int, lC3: int)
        (rS0: int, rC0: int, rS1: int, rC1: int, rS2: int, rC2: int, rS3: int, rC3: int)
        =
        let lTriv = lBuf.TriviaSpan()
        let rTriv = rBuf.TriviaSpan()

        let hasLeft =
            sliceHasComment lBuf lTriv lS0 lC0
            || sliceHasComment lBuf lTriv lS1 lC1
            || sliceHasComment lBuf lTriv lS2 lC2
            || sliceHasComment lBuf lTriv lS3 lC3

        let hasRight =
            sliceHasComment rBuf rTriv rS0 rC0
            || sliceHasComment rBuf rTriv rS1 rC1
            || sliceHasComment rBuf rTriv rS2 rC2
            || sliceHasComment rBuf rTriv rS3 rC3

        if not hasLeft && not hasRight then
            struct (true, "")
        else
            let lLim = lBuf.LastCommentTrivia + 1
            let rLim = rBuf.LastCommentTrivia + 1
            let mutable li = 0
            let mutable lt = lS0
            let mutable lcEnd = min lLim (lS0 + lC0)
            let mutable ri = 0
            let mutable rt = rS0
            let mutable rcEnd = min rLim (rS0 + rC0)
            let mutable ok = true
            let mutable mismatchDesc = ""
            let mutable outerSpans: ResizeArray<struct (int * int * int * int)> = null

            while ok && (li < 4 || ri < 4) do
                while li < 4 && (lt >= lcEnd || not (commentTrivia lTriv[lt].Kind)) do
                    if lt < lcEnd then
                        lt <- lt + 1
                    else
                        li <- li + 1

                        if li < 4 then
                            let s =
                                if li = 1 then lS1
                                elif li = 2 then lS2
                                else lS3

                            let c =
                                if li = 1 then lC1
                                elif li = 2 then lC2
                                else lC3

                            lt <- s
                            lcEnd <- min lLim (s + c)

                while ri < 4 && (rt >= rcEnd || not (commentTrivia rTriv[rt].Kind)) do
                    if rt < rcEnd then
                        rt <- rt + 1
                    else
                        ri <- ri + 1

                        if ri < 4 then
                            let s =
                                if ri = 1 then rS1
                                elif ri = 2 then rS2
                                else rS3

                            let c =
                                if ri = 1 then rC1
                                elif ri = 2 then rC2
                                else rC3

                            rt <- s
                            rcEnd <- min rLim (s + c)

                if li < 4 && ri < 4 then
                    let a = lTriv[lt]
                    let b = rTriv[rt]

                    if a.Kind = b.Kind && CommentContent.equivalentSpan lSrcSpan a rSrcSpan b then
                        lt <- lt + 1
                        rt <- rt + 1
                    elif
                        allowMergedDoc
                        && li = 3
                        && ri = 3
                        && a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                        && b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                    then
                        let struct (nextLeft, _) =
                            mergedDocCommentEquivalentSpan
                                lSrcSpan
                                lBuf
                                lt
                                (lS3 + lC3)
                                lTokIdx
                                rSrcSpan
                                b

                        if nextLeft > lt then
                            lt <- nextLeft
                            rt <- rt + 1
                        else
                            mismatchDesc <- formatCommentKey a lSrcSpan
                            ok <- false
                    elif
                        allowDirectiveSpanning
                        && (a.Kind = TriviaKind.MultiLineCommentTrivia
                            || a.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                        && a.Kind = b.Kind
                    then
                        if isNull outerSpans then
                            outerSpans <- ResizeArray()

                        if
                            directiveSpanningMultiLineEquivalent
                                (lSrcSpan.Slice(a.Start, a.Length))
                                (rSrcSpan.Slice(b.Start, b.Length))
                                outerSpans
                        then
                            if not (isNull deferredRawSpans) then
                                for oi = 0 to outerSpans.Count - 1 do
                                    let struct (relLS, relLE, relRS, relRE) = outerSpans[oi]

                                    deferredRawSpans.Add(
                                        struct (a.Start + relLS,
                                                a.Start + relLE,
                                                b.Start + relRS,
                                                b.Start + relRE)
                                    )

                            lt <- lt + 1
                            rt <- rt + 1
                        else
                            mismatchDesc <- formatCommentKey a lSrcSpan
                            ok <- false
                    else
                        mismatchDesc <- formatCommentKey a lSrcSpan
                        ok <- false
                elif li < 4 then
                    mismatchDesc <- formatCommentKey lTriv[lt] lSrcSpan
                    ok <- false
                elif ri < 4 then
                    mismatchDesc <- formatCommentKey rTriv[rt] rSrcSpan
                    ok <- false

            struct (ok, mismatchDesc)

    let private checkSingleSliceComments
        (allowDirectiveSpanning: bool)
        (deferredRawSpans: ResizeArray<struct (int * int * int * int)>)
        (lSrcSpan: ReadOnlySpan<char>)
        (rSrcSpan: ReadOnlySpan<char>)
        (lBuf: TokenBuffer)
        (rBuf: TokenBuffer)
        (lTokIdx: int)
        (lStart: int)
        (lCount: int)
        (rStart: int)
        (rCount: int)
        =
        checkGapComments
            true
            allowDirectiveSpanning
            deferredRawSpans
            lSrcSpan
            rSrcSpan
            lBuf
            rBuf
            lTokIdx
            (0, 0, 0, 0, 0, 0, lStart, lCount)
            (0, 0, 0, 0, 0, 0, rStart, rCount)

    let private suffixedIgnoreMarker (text: ReadOnlySpan<char>) (length: int) =
        text.Length = length
        || (text.Length > length + 3
            && text.Slice(length).StartsWith(" - ".AsSpan(), StringComparison.Ordinal))

    let private ignoreCommentKind (text: ReadOnlySpan<char>) (item: Trivia) =
        if item.Kind <> TriviaKind.SingleLineCommentTrivia || item.Length < 14 then
            0
        else
            let trimmed = text.Slice(item.Start, item.Length).Trim()

            if trimmed.Length < 14 || trimmed[2] <> ' ' || trimmed[3] <> 'c' then
                0
            elif
                trimmed.StartsWith("// csff-ignore-start".AsSpan(), StringComparison.Ordinal)
                && suffixedIgnoreMarker trimmed 20
            then
                2
            elif
                trimmed.StartsWith("// csff-ignore-end".AsSpan(), StringComparison.Ordinal)
                && suffixedIgnoreMarker trimmed 18
            then
                3
            elif
                trimmed.StartsWith("// csff-ignore".AsSpan(), StringComparison.Ordinal)
                && suffixedIgnoreMarker trimmed 14
            then
                1
            else
                0

    let private ignoreEndPrefixCount
        (text: ReadOnlySpan<char>)
        (triv: ReadOnlySpan<Trivia>)
        (tok: Token)
        =
        let t0 = tok.TriviaStart
        let lim = t0 + tok.LeadingCount
        let mutable k = t0
        let mutable lastEnd = t0
        let mutable stop = false

        while not stop && k < lim do
            let item = triv[k]

            if
                item.Kind = TriviaKind.WhitespaceTrivia
                || item.Kind = TriviaKind.EndOfLineTrivia
            then
                k <- k + 1
            elif ignoreCommentKind text item = 3 then
                k <- k + 1
                lastEnd <- k
            else
                stop <- true

        lastEnd - t0

    let private isIgnoreStartComment (text: ReadOnlySpan<char>) (item: Trivia) =
        ignoreCommentKind text item = 2

    let private isIgnoreEndComment (text: ReadOnlySpan<char>) (item: Trivia) =
        ignoreCommentKind text item = 3

    let private hasFooterDirectiveOrIgnoreEnd
        (text: ReadOnlySpan<char>)
        (triv: ReadOnlySpan<Trivia>)
        (tok: Token)
        =
        let mutable found = false
        let mutable k = tok.TriviaStart
        let lim = k + tok.LeadingCount

        while not found && k < lim do
            let item = triv[k]

            match item.Kind with
            | TriviaKind.IfDirectiveTrivia
            | TriviaKind.ElifDirectiveTrivia
            | TriviaKind.ElseDirectiveTrivia
            | TriviaKind.EndIfDirectiveTrivia -> found <- true
            | TriviaKind.SingleLineCommentTrivia when isIgnoreEndComment text item -> found <- true
            | _ -> ()

            k <- k + 1

        found

    let private countDocLines (span: ReadOnlySpan<char>) (t: Trivia) =
        let finish = t.Start + t.Length
        let mutable pos = t.Start
        let mutable count = 0

        while pos < finish do
            let struct (_, _, nextPos) = CommentContent.lineSpan span finish pos
            count <- count + 1
            pos <- nextPos

        count

    let private noDirectiveBetween (triv: ReadOnlySpan<Trivia>) (idxA: int) (idxB: int) =
        let mutable ok = true
        let mutable k = idxA + 1

        while ok && k < idxB do
            if triv[k].Kind > TriviaKind.MultiLineDocumentationCommentTrivia then
                ok <- false

            k <- k + 1

        ok

    let private docTriviaMatchesPrefix
        (lSpan: ReadOnlySpan<char>)
        (a: Trivia)
        (rSpan: ReadOnlySpan<char>)
        (bPos: byref<int>)
        (bFinish: int)
        =
        let aFinish = a.Start + a.Length
        let mutable aPos = a.Start
        let mutable same = true

        while same && aPos < aFinish do
            if bPos >= bFinish then
                same <- false
            else
                let struct (aStart, aLen, aNext) = CommentContent.lineSpan lSpan aFinish aPos
                let struct (bStart, bLen, bNext) = CommentContent.lineSpan rSpan bFinish bPos

                same <-
                    aLen = bLen
                    && lSpan.Slice(aStart, aLen).SequenceEqual(rSpan.Slice(bStart, bLen))

                aPos <- aNext
                bPos <- bNext

        same

    let private analyzeUsingFooterSide
        (text: string)
        (span: ReadOnlySpan<char>)
        (triv: ReadOnlySpan<Trivia>)
        (tok: Token)
        =
        let t0 = tok.TriviaStart
        let lim = t0 + tok.LeadingCount
        let comments = ResizeArray<int>()
        let mutable relDepth = 0
        let mutable sawDisabledUsing = false
        let mutable hasCondFooter = false
        let mutable sawCommentAfterFooter = false
        let mutable sawIgnoreStart = false
        let ignoreEndCount = ignoreEndPrefixCount span triv tok
        let mutable mandatoryEnd = t0 + ignoreEndCount
        let mutable tmpBuf = ValueNone

        for k = t0 to lim - 1 do
            let item = triv[k]

            if commentTrivia item.Kind then
                comments.Add k

                if isIgnoreStartComment span item then
                    sawIgnoreStart <- true
                    sawCommentAfterFooter <- true
                elif
                    not sawIgnoreStart
                    && not sawCommentAfterFooter
                    && (hasCondFooter || k < mandatoryEnd)
                    && isIgnoreEndComment span item
                    && k + 1 > mandatoryEnd
                then
                    mandatoryEnd <- k + 1
                elif k >= mandatoryEnd then
                    sawCommentAfterFooter <- true
            elif item.Kind = TriviaKind.IfDirectiveTrivia then
                if relDepth = 0 then
                    sawDisabledUsing <- false

                relDepth <- relDepth + 1
            elif item.Kind = TriviaKind.DisabledTextTrivia then
                if
                    relDepth > 0
                    && not sawDisabledUsing
                    && span
                        .Slice(item.Start, item.Length)
                        .IndexOf("using".AsSpan(), StringComparison.Ordinal)
                       >= 0
                then
                    let buf =
                        match tmpBuf with
                        | ValueSome b -> b
                        | ValueNone ->
                            let b = TokenBuffer()
                            tmpBuf <- ValueSome b
                            b

                    Lexer.lexRange text item.Start (item.Start + item.Length) buf
                    let mutable ti = 0

                    while not sawDisabledUsing && ti < buf.TokenCount do
                        if (buf.Token ti).Kind = TokenKind.UsingKeyword then
                            sawDisabledUsing <- true

                        ti <- ti + 1
            elif
                item.Kind = TriviaKind.ElifDirectiveTrivia
                || item.Kind = TriviaKind.ElseDirectiveTrivia
            then
                if relDepth <= 0 then
                    relDepth <- 0
                    hasCondFooter <- true

                    if k + 1 > mandatoryEnd then
                        mandatoryEnd <- k + 1
                        sawCommentAfterFooter <- false
            elif item.Kind = TriviaKind.EndIfDirectiveTrivia then
                if relDepth <= 0 then
                    relDepth <- 0
                    hasCondFooter <- true

                    if k + 1 > mandatoryEnd then
                        mandatoryEnd <- k + 1
                        sawCommentAfterFooter <- false
                else
                    relDepth <- relDepth - 1

                    if relDepth = 0 && sawDisabledUsing then
                        hasCondFooter <- true
                        sawDisabledUsing <- false

                        if k + 1 > mandatoryEnd then
                            mandatoryEnd <- k + 1
                            sawCommentAfterFooter <- false

        match tmpBuf with
        | ValueSome b -> b.ReleasePooledBuffers()
        | ValueNone -> ()

        struct (comments, hasCondFooter, mandatoryEnd, ignoreEndCount)

    let private skipUsingFooterSide
        (triv: ReadOnlySpan<Trivia>)
        (tok: Token)
        (mandatoryEnd: int)
        (comments: ResizeArray<int>)
        (suffixPos: int)
        =
        let t0 = tok.TriviaStart

        let suffixLim =
            if suffixPos < comments.Count then
                comments[suffixPos]
            else
                t0 + tok.LeadingCount

        let mutable lastAbsorbed = t0

        for k = t0 to suffixLim - 1 do
            if k < mandatoryEnd || commentTrivia triv[k].Kind then
                lastAbsorbed <- k + 1

        lastAbsorbed - t0

    let private usingFooterPrefixLengths
        (lText: string)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (inTok: Token)
        (rText: string)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outTok: Token)
        =
        if
            not (hasFooterDirectiveOrIgnoreEnd lSpan lTriv inTok)
            && not (hasFooterDirectiveOrIgnoreEnd rSpan rTriv outTok)
        then
            struct (0, 0, false)
        else
            let struct (inComments, inHasCondFooter, inMandatoryEnd, inIgnoreEndCount) =
                analyzeUsingFooterSide lText lSpan lTriv inTok

            let struct (outComments, outHasCondFooter, outMandatoryEnd, outIgnoreEndCount) =
                analyzeUsingFooterSide rText rSpan rTriv outTok

            if not inHasCondFooter && not outHasCondFooter then
                struct (inIgnoreEndCount, outIgnoreEndCount, false)
            else
                let inSkip =
                    if inHasCondFooter then
                        inMandatoryEnd - inTok.TriviaStart
                    else
                        inIgnoreEndCount

                let outSkip =
                    if not outHasCondFooter then
                        outIgnoreEndCount
                    else
                        let mutable pi = inComments.Count - 1
                        let mutable pj = outComments.Count - 1
                        let mutable matchedSuffix = true

                        while matchedSuffix && pi >= 0 && pj >= 0 do
                            let lIdx = inComments[pi]
                            let rIdx = outComments[pj]

                            if lIdx < inMandatoryEnd || rIdx < outMandatoryEnd then
                                matchedSuffix <- false
                            else
                                let lc = lTriv[lIdx]
                                let rc = rTriv[rIdx]

                                if
                                    lc.Kind = rc.Kind
                                    && CommentContent.equivalentSpan lSpan lc rSpan rc
                                then
                                    pi <- pi - 1
                                    pj <- pj - 1
                                elif
                                    lc.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                                    && rc.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                                then
                                    let rLines = countDocLines rSpan rc
                                    let mutable p = pi
                                    let mutable lLines = countDocLines lSpan lc
                                    let mutable validChain = true

                                    while validChain && lLines < rLines && p > 0 do
                                        let nextIdx = inComments[p - 1]

                                        if
                                            nextIdx < inMandatoryEnd
                                            || lTriv[nextIdx].Kind
                                               <> TriviaKind.SingleLineDocumentationCommentTrivia
                                            || not (noDirectiveBetween lTriv nextIdx inComments[p])
                                        then
                                            validChain <- false
                                        else
                                            p <- p - 1
                                            lLines <- lLines + countDocLines lSpan lTriv[nextIdx]

                                    let mutable matchedGroup = false

                                    if validChain && lLines = rLines then
                                        let rFinish = rc.Start + rc.Length
                                        let mutable rPos = rc.Start
                                        let mutable t = p
                                        let mutable allOk = true

                                        while allOk && t <= pi do
                                            if
                                                not (
                                                    docTriviaMatchesPrefix
                                                        lSpan
                                                        lTriv[inComments[t]]
                                                        rSpan
                                                        &rPos
                                                        rFinish
                                                )
                                            then
                                                allOk <- false

                                            t <- t + 1

                                        if allOk && rPos >= rFinish then
                                            pi <- p - 1
                                            pj <- pj - 1
                                            matchedGroup <- true

                                    if not matchedGroup then
                                        let lLinesSingle = countDocLines lSpan lc
                                        let mutable q = pj
                                        let mutable rAcc = countDocLines rSpan rc
                                        let mutable validRChain = true

                                        while validRChain && rAcc < lLinesSingle && q > 0 do
                                            let nextIdx = outComments[q - 1]

                                            if
                                                nextIdx < outMandatoryEnd
                                                || rTriv[nextIdx].Kind
                                                   <> TriviaKind
                                                       .SingleLineDocumentationCommentTrivia
                                                || not (
                                                    noDirectiveBetween rTriv nextIdx outComments[q]
                                                )
                                            then
                                                validRChain <- false
                                            else
                                                q <- q - 1
                                                rAcc <- rAcc + countDocLines rSpan rTriv[nextIdx]

                                        if validRChain && rAcc = lLinesSingle then
                                            let lFinish = lc.Start + lc.Length
                                            let mutable lPos = lc.Start
                                            let mutable t = q
                                            let mutable allOk = true

                                            while allOk && t <= pj do
                                                if
                                                    not (
                                                        docTriviaMatchesPrefix
                                                            rSpan
                                                            rTriv[outComments[t]]
                                                            lSpan
                                                            &lPos
                                                            lFinish
                                                    )
                                                then
                                                    allOk <- false

                                                t <- t + 1

                                            if allOk && lPos >= lFinish then
                                                pi <- pi - 1
                                                pj <- q - 1
                                                matchedGroup <- true

                                    if not matchedGroup then
                                        matchedSuffix <- false
                                else
                                    matchedSuffix <- false

                        skipUsingFooterSide rTriv outTok outMandatoryEnd outComments (pj + 1)

                struct (inSkip, outSkip, true)

    let private commaChildSlot (tree: SyntaxTree) (node: Node) (commas: HashSet<int>) =
        let mutable slot = -1
        let mutable ambiguous = false
        let mutable index = 0

        while index < node.ChildCount do
            let child = tree.Child(node.ChildStart + index)

            if child < 0 && commas.Contains(~~~child) then
                ambiguous <- ambiguous || slot >= 0
                slot <- index

            index <- index + 1

        if ambiguous then -1 else slot

    let private grownIndices (array: int array) (needed: int) =
        if array.Length >= needed then
            array
        else
            let next = Array.zeroCreate (max needed (array.Length * 2))
            Array.Copy(array, 0, next, 0, array.Length)
            next

    let private grownFlags (array: bool array) (needed: int) =
        if array.Length >= needed then
            array
        else
            let next = Array.zeroCreate (max needed (array.Length * 2))
            Array.Copy(array, 0, next, 0, array.Length)
            next

    let private grownHashes (array: uint64 array) (needed: int) =
        if array.Length >= needed then
            array
        else
            let next = Array.zeroCreate (max needed (array.Length * 2))
            Array.Copy(array, 0, next, 0, array.Length)
            next

    let inline private contextDirective (kind: TriviaKind) =
        kind = TriviaKind.DefineDirectiveTrivia
        || kind = TriviaKind.UndefDirectiveTrivia
        || kind = TriviaKind.NullableDirectiveTrivia
        || kind = TriviaKind.LineDirectiveTrivia
        || kind = TriviaKind.LineSpanDirectiveTrivia
        || kind = TriviaKind.PragmaWarningDirectiveTrivia
        || kind = TriviaKind.PragmaChecksumDirectiveTrivia

    let inline private holdsUsings (kind: NodeKind) =
        kind = NodeKind.CompilationUnit
        || kind = NodeKind.NamespaceDeclaration
        || kind = NodeKind.FileScopedNamespaceDeclaration

    let inline private listClosing (kind: NodeKind) =
        match kind with
        | NodeKind.ObjectInitializerExpression
        | NodeKind.CollectionInitializerExpression
        | NodeKind.ArrayInitializerExpression
        | NodeKind.WithInitializerExpression
        | NodeKind.AnonymousObjectCreationExpression
        | NodeKind.SwitchExpression
        | NodeKind.EnumDeclaration
        | NodeKind.PropertyPatternClause -> TokenKind.CloseBraceToken
        | NodeKind.CollectionExpression
        | NodeKind.ListPattern
        | NodeKind.AttributeList -> TokenKind.CloseBracketToken
        | _ -> TokenKind.None

    let private trailingCommaSlot (tree: SyntaxTree) (node: Node) =
        let closing = listClosing node.Kind

        if closing = TokenKind.None then
            -1
        else
            let mutable slot = -1
            let mutable index = node.ChildCount - 1

            while slot < 0 && index > 0 do
                let child = tree.Child(node.ChildStart + index)
                let previous = tree.Child(node.ChildStart + index - 1)

                if
                    child < 0
                    && previous < 0
                    && tree.Token(~~~child).Kind = closing
                    && tree.Token(~~~previous).Kind = TokenKind.CommaToken
                then
                    slot <- index - 1
                else
                    index <- index - 1

            slot

    let private importShaped (tree: SyntaxTree) (node: Node) =
        let mutable index = 0
        let mutable shaped = node.TokenCount > 0
        let mutable aliased = false

        while shaped && index < node.TokenCount do
            let token = tree.Token(node.TokenStart + index)

            shaped <-
                match token.Kind with
                | TokenKind.UsingKeyword
                | TokenKind.GlobalKeyword
                | TokenKind.StaticKeyword
                | TokenKind.IdentifierToken
                | TokenKind.DotToken
                | TokenKind.ColonColonToken
                | TokenKind.EqualsToken
                | TokenKind.LessThanToken
                | TokenKind.GreaterThanToken
                | TokenKind.CommaToken
                | TokenKind.SemicolonToken -> token.Length > 0
                | TokenKind.OmittedArraySizeExpressionToken -> aliased && token.Length = 0
                | TokenKind.QuestionToken
                | TokenKind.OpenBracketToken
                | TokenKind.CloseBracketToken -> aliased && token.Length > 0
                | kind ->
                    aliased
                    && token.Length > 0
                    && kind >= TokenKind.BoolKeyword
                    && kind <= TokenKind.ObjectKeyword
                    && kind <> TokenKind.VoidKeyword

            if token.Kind = TokenKind.EqualsToken then
                aliased <- true

            index <- index + 1

        shaped

    [<Sealed>]
    type private UsingPlacement() =
        let mutable frame = Array.zeroCreate<int> 256
        let mutable segment = Array.zeroCreate<int> 256
        let mutable ownedStamp = Array.zeroCreate<int> 2048
        let mutable currentStamp = 0
        let mutable maxOwnedToken = 0
        let mutable directiveFrame = Array.zeroCreate<int> 64
        let mutable directiveSegment = Array.zeroCreate<int> 64
        let mutable nodes = Array.zeroCreate<int> 64
        let mutable imports = 0
        let mutable directives_ = 0
        let open_ = Stack<int>()
        let scopeStack = Stack<int>()

        member _.Load(tree: SyntaxTree, directives: ResizeArray<Trivia>) =
            let count = directives.Count

            let outer = tree.LexerBuffer.TriviaCount
            let mutable nested = false

            for index = outer to tree.TriviaCount - 1 do
                let kind = (tree.Trivia index).Kind

                if
                    kind = TriviaKind.IfDirectiveTrivia
                    || kind = TriviaKind.ElifDirectiveTrivia
                    || kind = TriviaKind.ElseDirectiveTrivia
                    || kind = TriviaKind.EndIfDirectiveTrivia
                then
                    nested <- true

            if nested then
                false
            else
                directiveFrame <- grownIndices directiveFrame (count + 1)
                directiveSegment <- grownIndices directiveSegment (count + 1)
                open_.Clear()
                let mutable current = -1
                let mutable context = 0

                for index = 0 to count - 1 do
                    let kind = directives[index].Kind

                    if kind = TriviaKind.IfDirectiveTrivia then
                        open_.Push current
                        current <- index
                    elif
                        kind = TriviaKind.ElifDirectiveTrivia
                        || kind = TriviaKind.ElseDirectiveTrivia
                    then
                        current <- index
                    elif kind = TriviaKind.EndIfDirectiveTrivia then
                        current <- if open_.Count > 0 then open_.Pop() else -1

                    if contextDirective kind then
                        context <- context + 1

                    directiveFrame[index] <- current
                    directiveSegment[index] <- context

                directives_ <- count
                imports <- 0
                let mutable maxNodeIndex = 0
                let mutable maxTokenEnd = 0
                scopeStack.Clear()

                if tree.RootIndex >= 0 then
                    scopeStack.Push tree.RootIndex

                    while scopeStack.Count > 0 do
                        let scopeIndex = scopeStack.Pop()
                        let scopeNode = tree.Node scopeIndex

                        if holdsUsings scopeNode.Kind then
                            for s = scopeNode.ChildCount - 1 downto 0 do
                                let child = tree.Child(scopeNode.ChildStart + s)

                                if child >= 0 then
                                    let childNode = tree.Node child

                                    if childNode.Kind = NodeKind.UsingDirective then
                                        nodes <- grownIndices nodes (imports + 1)
                                        nodes[imports] <- child
                                        imports <- imports + 1

                                        if child > maxNodeIndex then
                                            maxNodeIndex <- child

                                        let tokEnd = childNode.TokenStart + childNode.TokenCount

                                        if tokEnd > maxTokenEnd then
                                            maxTokenEnd <- tokEnd
                                    elif holdsUsings childNode.Kind then
                                        scopeStack.Push child

                if imports = 0 then
                    maxOwnedToken <- 0
                    true
                else

                    frame <- grownIndices frame (maxNodeIndex + 1)
                    segment <- grownIndices segment (maxNodeIndex + 1)
                    ownedStamp <- grownIndices ownedStamp (maxTokenEnd + 1)
                    currentStamp <- currentStamp + 1

                    if currentStamp <= 0 then
                        Array.fill ownedStamp 0 ownedStamp.Length 0
                        currentStamp <- 1

                    maxOwnedToken <- maxTokenEnd
                    let stamp = currentStamp
                    let mutable valid = true

                    for slot = 0 to imports - 1 do
                        let index = nodes[slot]
                        let node = tree.Node index
                        let struct (start, length) = tree.SourceSpan index

                        for token = node.TokenStart to node.TokenStart + node.TokenCount - 1 do
                            ownedStamp[token] <- stamp

                        let mutable low = 0
                        let mutable high = count

                        while low < high do
                            let middle = low + (high - low) / 2

                            if directives[middle].Start < start then
                                low <- middle + 1
                            else
                                high <- middle

                        valid <- valid && (low = count || directives[low].Start >= start + length)
                        frame[index] <- if low = 0 then -1 else directiveFrame[low - 1]
                        segment[index] <- if low = 0 then 0 else directiveSegment[low - 1]

                    valid

        member _.Frame(node: int) = frame[node]

        member _.Segment(node: int) = segment[node]

        member _.Owns(token: int) =
            imports > 0 && token < maxOwnedToken && ownedStamp[token] = currentStamp

        member _.Imports = imports

        member _.SamePlacements(other: UsingPlacement) =
            if imports <> other.Imports then
                false
            else
                let mutable same = true
                let mutable slot = 0

                while same && slot < imports do
                    let idx = nodes[slot]

                    same <-
                        other.NodeAt slot = idx
                        && frame[idx] = other.Frame idx
                        && segment[idx] = other.Segment idx

                    slot <- slot + 1

                same

        member internal _.NodeAt(slot: int) = nodes[slot]

    let private hasClosingIgnoreEndInScope
        (tokens: ReadOnlySpan<Token>)
        (triv: ReadOnlySpan<Trivia>)
        (span: ReadOnlySpan<char>)
        (contentLim: int)
        (startTok: int)
        (startDepth: int)
        (scopeDepth: int)
        =
        let mutable k = startTok
        let mutable depth = startDepth
        let mutable found = false
        let mutable doneScan = false

        while not found && not doneScan && k < tokens.Length do
            let t = tokens[k]
            let leadStart = t.TriviaStart
            let leadEnd = leadStart + t.LeadingCount
            let leadStop = min contentLim leadEnd
            let mutable j = leadStart

            while not found && j < leadStop do
                if ignoreCommentKind span triv[j] = 3 && depth <= scopeDepth then
                    found <- true
                else
                    j <- j + 1

            if not found then
                if t.Kind = TokenKind.OpenBraceToken then
                    depth <- depth + 1
                elif t.Kind = TokenKind.CloseBraceToken then
                    depth <- max 0 (depth - 1)

                    if depth < scopeDepth then
                        doneScan <- true

                if not doneScan then
                    let trailStop = min contentLim (leadEnd + t.TrailingCount)
                    let mutable tj = leadEnd

                    while not found && tj < trailStop do
                        if ignoreCommentKind span triv[tj] = 3 && depth <= scopeDepth then
                            found <- true
                        else
                            tj <- tj + 1

                    k <- k + 1

        found

    [<Struct>]
    type private UsingRunComment =
        {
            TriviaIndex: int
            Frame: int
            Ctx: int
            RegionDepth: int
            RegionSeq: int
            DirSeq: int
            EffDirSeq: int
            IsInertIgnoreEnd: bool
            SlotRelFrame: int
        }

    let inline private markEffStackContent (effStack: ResizeArray<struct (int * bool)>) =
        let mutable i = effStack.Count - 1

        while i >= 0 do
            let struct (savedEff, hasContent) = effStack[i]

            if hasContent then
                i <- -1
            else
                effStack[i] <- struct (savedEff, true)
                i <- i - 1

    let inline private stepEffDirective
        (kind: TriviaKind)
        (span: ReadOnlySpan<char>)
        (item: Trivia)
        (effStack: ResizeArray<struct (int * bool)>)
        (effDirSeq: byref<int>)
        =
        if kind = TriviaKind.IfDirectiveTrivia then
            effStack.Add(struct (effDirSeq, false))
            effDirSeq <- effDirSeq + 1
        elif kind = TriviaKind.EndIfDirectiveTrivia then
            if effStack.Count > 0 then
                let top = effStack.Count - 1
                let struct (savedEff, hasContent) = effStack[top]
                effStack.RemoveAt top

                if hasContent then
                    effDirSeq <- effDirSeq + 1
                    markEffStackContent effStack
                else
                    effDirSeq <- savedEff
            else
                effDirSeq <- effDirSeq + 1
        elif kind = TriviaKind.ElifDirectiveTrivia || kind = TriviaKind.ElseDirectiveTrivia then
            effDirSeq <- effDirSeq + 1
        elif kind = TriviaKind.DisabledTextTrivia then
            if effStack.Count > 0 && span.Slice(item.Start, item.Length).Trim().Length > 0 then
                markEffStackContent effStack
        else
            markEffStackContent effStack

    let inline private usingCommentDirSeqMatches (inC: UsingRunComment) (outC: UsingRunComment) =
        inC.DirSeq = outC.DirSeq
        || (inC.IsInertIgnoreEnd
            && outC.IsInertIgnoreEnd
            && inC.DirSeq <= outC.DirSeq
            && inC.EffDirSeq = outC.EffDirSeq)

    let inline private stepUsingRunDirectiveState
        (kind: TriviaKind)
        (stack: ResizeArray<struct (int * int)>)
        (curFrame: byref<int>)
        (curCtx: byref<int>)
        (regionDepth: byref<int>)
        (regionSeq: byref<int>)
        (nextFrame: byref<int>)
        (outerNextFrame: byref<int>)
        (dirSeq: byref<int>)
        =
        if kind = TriviaKind.IfDirectiveTrivia then
            stack.Add(struct (curFrame, curCtx))
            curFrame <- nextFrame
            nextFrame <- nextFrame + 1
            curCtx <- 0
            dirSeq <- dirSeq + 1
        elif kind = TriviaKind.ElifDirectiveTrivia || kind = TriviaKind.ElseDirectiveTrivia then
            if stack.Count > 0 then
                curFrame <- nextFrame
                nextFrame <- nextFrame + 1
            else
                curFrame <- outerNextFrame
                outerNextFrame <- outerNextFrame - 1

            curCtx <- 0
            dirSeq <- dirSeq + 1
        elif kind = TriviaKind.EndIfDirectiveTrivia then
            if stack.Count > 0 then
                let last = stack.Count - 1
                let struct (pf, pc) = stack[last]
                stack.RemoveAt last
                curFrame <- pf
                curCtx <- pc
            else
                curFrame <- outerNextFrame
                outerNextFrame <- outerNextFrame - 1
                curCtx <- 0

            dirSeq <- dirSeq + 1
        elif kind = TriviaKind.RegionDirectiveTrivia then
            regionDepth <- regionDepth + 1
            regionSeq <- regionSeq + 1
        elif kind = TriviaKind.EndRegionDirectiveTrivia then
            regionDepth <- regionDepth - 1
            regionSeq <- regionSeq + 1
        elif contextDirective kind then
            curCtx <- curCtx + 1

    [<NoComparison; NoEquality>]
    type private DirectiveSpanningFooterEntry =
        {
            Comment: UsingRunComment
            Kind: TriviaKind
            LeavesCount: int
            HasSkippedWs: bool
            Kept: ResizeArray<string>
            RequiresPreCond: bool
        }

    [<AllowNullLiteral; Sealed>]
    type private UsingFooterIndex() =
        member val Hashes = Array.zeroCreate<uint64> 64 with get, set
        member val BucketMask = 63 with get, set
        member val BucketCounts = Array.zeroCreate<int> 64 with get, set
        member val BucketOffsets = Array.zeroCreate<int> 65 with get, set
        member val BucketItems = Array.zeroCreate<int> 64 with get, set
        member val DocPrefixHashes = Array.zeroCreate<uint64> 64 with get, set
        member val DocPrefixBfIdxs = ResizeArray<int>()
        member val DocPrefixBucketMask = 63 with get, set
        member val DocPrefixBucketCounts = Array.zeroCreate<int> 64 with get, set
        member val DocPrefixBucketOffsets = Array.zeroCreate<int> 65 with get, set
        member val DocPrefixBucketItems = Array.zeroCreate<int> 64 with get, set
        member val DocMidHashes = Array.zeroCreate<uint64> 64 with get, set
        member val DocMidBfIdxs = ResizeArray<int>()
        member val DocMidStarts = ResizeArray<int>()
        member val DocMidBucketMask = 63 with get, set
        member val DocMidBucketCounts = Array.zeroCreate<int> 64 with get, set
        member val DocMidBucketOffsets = Array.zeroCreate<int> 65 with get, set
        member val DocMidBucketItems = Array.zeroCreate<int> 64 with get, set
        member val DocMidMultiHashes = Array.zeroCreate<uint64> 64 with get, set
        member val DocMidMultiBfIdxs = ResizeArray<int>()
        member val DocMidMultiStarts = ResizeArray<int>()
        member val DocMidMultiBucketMask = 63 with get, set
        member val DocMidMultiBucketCounts = Array.zeroCreate<int> 64 with get, set
        member val DocMidMultiBucketOffsets = Array.zeroCreate<int> 65 with get, set
        member val DocMidMultiBucketItems = Array.zeroCreate<int> 64 with get, set
        member val IndexedMidLens = HashSet<int>()
        member val DocMidLineIdxs = ResizeArray<int>()
        member val DocMidMultiLineIdxs = ResizeArray<int>()
        member val DocAllStarts = ResizeArray<int>()
        member val DocAllPolys = ResizeArray<uint64>()
        member val BfDocStartOff = Array.zeroCreate<int> 64 with get, set
        member val BfDocPolyOff = Array.zeroCreate<int> 64 with get, set
        member val BfDocLineCounts = Array.zeroCreate<int> 64 with get, set
        member val PowBase = ResizeArray<uint64>()
        member val MaxBfDocLines = 0 with get, set
        member val SpanningBfIndices = ResizeArray<int>()
        member val InertHashes = Array.zeroCreate<uint64> 64 with get, set
        member val InertBfIdxs = ResizeArray<int>()
        member val InertBucketMask = 63 with get, set
        member val InertBucketCounts = Array.zeroCreate<int> 64 with get, set
        member val InertBucketOffsets = Array.zeroCreate<int> 65 with get, set
        member val InertBucketItems = Array.zeroCreate<int> 64 with get, set

    [<AllowNullLiteral; Sealed>]
    type private UsingSlotRetryState() =
        member val RetryMode = 0 with get, set
        member val PreferSkipIn2 = false with get, set
        member val Crossed1 = false with get, set
        member val OutS = 0 with get, set
        member val OutE = -1 with get, set
        member val OutHasDoc = false with get, set
        member val In1S = 0 with get, set
        member val In1E = -1 with get, set
        member val In2S = 0 with get, set
        member val In2E = -1 with get, set
        member val InClauseFrame = 0 with get, set
        member val InClauseRegionDepth = 0 with get, set
        member val InClauseRegionSeq = 0 with get, set
        member val OutClauseFrame = 0 with get, set
        member val OutClauseRegionDepth = 0 with get, set
        member val OutClauseRegionSeq = 0 with get, set
        member val BfStartIdx = 0 with get, set
        member val BfStartPos = 0 with get, set
        member val AllowMidDoc = false with get, set
        member val SavedRawStart = 0 with get, set
        member val PrefixSavedRaw = 0 with get, set
        member val EndBfIdx = 0 with get, set
        member val EndBfPos = 0 with get, set
        member val PrefixOi = 0 with get, set
        member val PrefixIn2 = 0 with get, set
        member val PrefixBfIdx = 0 with get, set
        member val PrefixBfPos = 0 with get, set
        member val FrameStack = ResizeArray<struct (int * int * int * int * int)>()
        member val BfStack = ResizeArray<struct (int * int)>()
        member val MatchedRanges = ResizeArray<struct (int * int)>()
        member val Memo3 = HashSet<struct (int * int * uint64)>()
        member val NoSkipMemo = HashSet<struct (int * int)>()
        member val NoSkipVisited = ResizeArray<int>()
        member val PrefixConsumed = ResizeArray<int>()

    [<AllowNullLiteral; Sealed>]
    type private UsingIgnoreStateCursor() =
        let mutable buffer = Unchecked.defaultof<TokenBuffer>
        let mutable version = -1
        let mutable tokenCount = -1
        let mutable triviaCount = -1
        let mutable curTok = 0
        let mutable braceDepth = 0
        let mutable openIgnore = false
        let mutable openIgnoreBraceDepth = -1

        member _.Reset() =
            buffer <- Unchecked.defaultof<TokenBuffer>
            version <- -1
            tokenCount <- -1
            triviaCount <- -1
            curTok <- 0
            braceDepth <- 0
            openIgnore <- false
            openIgnoreBraceDepth <- -1

        member this.AdvanceTo(buf: TokenBuffer, span: ReadOnlySpan<char>, targetTok: int) =
            if
                not (Object.ReferenceEquals(buffer, buf))
                || version <> buf.Version
                || tokenCount <> buf.TokenCount
                || triviaCount <> buf.TriviaCount
                || targetTok < curTok
            then
                this.Reset()
                buffer <- buf
                version <- buf.Version
                tokenCount <- buf.TokenCount
                triviaCount <- buf.TriviaCount

            if curTok < targetTok then
                let tokens = buf.TokenSpan()
                let triv = buf.TriviaSpan()
                let hasComments = buf.HasComments

                while curTok < targetTok do
                    let tok = tokens[curTok]

                    if hasComments then
                        let lim = tok.TriviaStart + tok.LeadingCount + tok.TrailingCount

                        for k = tok.TriviaStart to lim - 1 do
                            let item = triv[k]

                            if item.Kind = TriviaKind.SingleLineCommentTrivia then
                                let mk = ignoreCommentKind span item

                                if mk = 2 then
                                    if not openIgnore then
                                        openIgnore <- true
                                        openIgnoreBraceDepth <- braceDepth
                                elif mk = 3 then
                                    if openIgnore && braceDepth <= openIgnoreBraceDepth then
                                        openIgnore <- false

                    if tok.Kind = TokenKind.OpenBraceToken then
                        braceDepth <- braceDepth + 1
                    elif tok.Kind = TokenKind.CloseBraceToken then
                        if braceDepth > 0 then
                            braceDepth <- braceDepth - 1

                        if openIgnore && braceDepth < openIgnoreBraceDepth then
                            openIgnore <- false

                    curTok <- curTok + 1

            struct (braceDepth, openIgnore, openIgnoreBraceDepth)

    let private collectUsingRunComments
        (buf: TokenBuffer)
        (ignoreCursor: UsingIgnoreStateCursor)
        (span: ReadOnlySpan<char>)
        (tokens: ReadOnlySpan<Token>)
        (triv: ReadOnlySpan<Trivia>)
        (useInLengths: bool)
        (startTok: int)
        (inUsingLengths: int array)
        (childSlots: int array)
        (usingSlots: int array)
        (count: int)
        (footerTokIdx: int)
        (footerSkip: int)
        (dirStack: ResizeArray<struct (int * int)>)
        (effStack: ResizeArray<struct (int * bool)>)
        (commentsOut: ResizeArray<UsingRunComment>)
        (slotStartsOut: int array)
        (slotEndsOut: int array)
        (clauseFramesOut: int array)
        (clauseRegionDepthsOut: int array)
        (clauseRegionSeqsOut: int array)
        (clauseDirSeqsOut: int array)
        (boundaryEndIfDirSeqsOut: int array)
        =
        commentsOut.Clear()
        dirStack.Clear()
        effStack.Clear()
        let mutable curFrame = -1
        let mutable curCtx = 0
        let mutable regionDepth = 0
        let mutable regionSeq = 0
        let mutable nextFrame = 0
        let mutable outerNextFrame = -2
        let mutable dirSeq = 0
        let mutable effDirSeq = 0
        let mutable sawIgnoreEnd = false
        let mutable tokCursor = startTok
        let mutable lastClauseEndTok = startTok

        for s = 0 to count - 1 do
            let clauseStart = if useInLengths then tokCursor else childSlots[s]
            let clauseLen = if useInLengths then inUsingLengths[s] else usingSlots[s]
            lastClauseEndTok <- clauseStart + clauseLen - 1
            slotStartsOut[s] <- commentsOut.Count
            let slotStartNextFrame = nextFrame
            let headTok = tokens[clauseStart]
            let headLim = headTok.TriviaStart + headTok.LeadingCount
            let mutable lastEndIfDir = -1

            for k = headTok.TriviaStart to headLim - 1 do
                let item = triv[k]

                if commentTrivia item.Kind then
                    markEffStackContent effStack

                    if not sawIgnoreEnd && isIgnoreEndComment span item then
                        sawIgnoreEnd <- true

                    commentsOut.Add
                        {
                            TriviaIndex = k
                            Frame = curFrame
                            Ctx = curCtx
                            RegionDepth = regionDepth
                            RegionSeq = regionSeq
                            DirSeq = dirSeq
                            EffDirSeq = effDirSeq
                            IsInertIgnoreEnd = false
                            SlotRelFrame = -1
                        }
                elif item.Kind > TriviaKind.MultiLineDocumentationCommentTrivia then
                    stepUsingRunDirectiveState
                        item.Kind
                        dirStack
                        &curFrame
                        &curCtx
                        &regionDepth
                        &regionSeq
                        &nextFrame
                        &outerNextFrame
                        &dirSeq

                    stepEffDirective item.Kind span item effStack &effDirSeq

                    if item.Kind = TriviaKind.EndIfDirectiveTrivia then
                        lastEndIfDir <- dirSeq

            slotEndsOut[s] <- commentsOut.Count - 1
            let mutable relIdx = slotStartsOut[s]

            while relIdx <= slotEndsOut[s] do
                let c = commentsOut[relIdx]

                if c.Frame >= slotStartNextFrame && c.Frame <> curFrame then
                    commentsOut[relIdx] <-
                        { c with
                            SlotRelFrame = nextFrame - c.Frame
                        }

                relIdx <- relIdx + 1

            if effStack.Count > 0 then
                markEffStackContent effStack

            if not (isNull clauseFramesOut) then
                clauseFramesOut[s] <- curFrame

            if not (isNull clauseRegionDepthsOut) then
                clauseRegionDepthsOut[s] <- regionDepth

            if not (isNull clauseRegionSeqsOut) then
                clauseRegionSeqsOut[s] <- regionSeq

            if not (isNull clauseDirSeqsOut) then
                clauseDirSeqsOut[s] <- dirSeq

            if not (isNull boundaryEndIfDirSeqsOut) then
                boundaryEndIfDirSeqsOut[s] <- lastEndIfDir

            let headTrailEnd = headLim + headTok.TrailingCount

            for k = headLim to headTrailEnd - 1 do
                let item = triv[k]
                let kind = item.Kind

                if kind > TriviaKind.MultiLineDocumentationCommentTrivia then
                    stepUsingRunDirectiveState
                        kind
                        dirStack
                        &curFrame
                        &curCtx
                        &regionDepth
                        &regionSeq
                        &nextFrame
                        &outerNextFrame
                        &dirSeq

                    stepEffDirective kind span item effStack &effDirSeq

            for ti = 1 to clauseLen - 1 do
                let tok = tokens[clauseStart + ti]
                let tEnd = tok.TriviaStart + tok.LeadingCount + tok.TrailingCount

                for k = tok.TriviaStart to tEnd - 1 do
                    let item = triv[k]
                    let kind = item.Kind

                    if kind > TriviaKind.MultiLineDocumentationCommentTrivia then
                        stepUsingRunDirectiveState
                            kind
                            dirStack
                            &curFrame
                            &curCtx
                            &regionDepth
                            &regionSeq
                            &nextFrame
                            &outerNextFrame
                            &dirSeq

                        stepEffDirective kind span item effStack &effDirSeq

            if useInLengths then
                tokCursor <- tokCursor + clauseLen

        slotStartsOut[count] <- commentsOut.Count

        if footerSkip > 0 then
            let ftok = tokens[footerTokIdx]
            let lim = ftok.TriviaStart + footerSkip

            for k = ftok.TriviaStart to lim - 1 do
                let item = triv[k]

                if commentTrivia item.Kind then
                    markEffStackContent effStack

                    if not sawIgnoreEnd && isIgnoreEndComment span item then
                        sawIgnoreEnd <- true

                    commentsOut.Add
                        {
                            TriviaIndex = k
                            Frame = curFrame
                            Ctx = curCtx
                            RegionDepth = regionDepth
                            RegionSeq = regionSeq
                            DirSeq = dirSeq
                            EffDirSeq = effDirSeq
                            IsInertIgnoreEnd = false
                            SlotRelFrame = -1
                        }
                elif item.Kind > TriviaKind.MultiLineDocumentationCommentTrivia then
                    stepUsingRunDirectiveState
                        item.Kind
                        dirStack
                        &curFrame
                        &curCtx
                        &regionDepth
                        &regionSeq
                        &nextFrame
                        &outerNextFrame
                        &dirSeq

                    stepEffDirective item.Kind span item effStack &effDirSeq

        slotEndsOut[count] <- commentsOut.Count - 1

        if sawIgnoreEnd && commentsOut.Count > 0 then
            let runFirstTok =
                if useInLengths then startTok
                elif count > 0 then childSlots[0]
                else footerTokIdx

            let lastScanTok = if footerSkip > 0 then footerTokIdx else lastClauseEndTok

            let struct (initBraceDepth, initOpenIgnore, initOpenIgnoreBraceDepth) =
                if isNull ignoreCursor then
                    struct (0, false, -1)
                else
                    ignoreCursor.AdvanceTo(buf, span, runFirstTok)

            let mutable braceDepth = initBraceDepth
            let mutable openIgnore = initOpenIgnore
            let mutable openIgnoreBraceDepth = initOpenIgnoreBraceDepth
            let mutable ci = 0
            let mutable lastNonEndIgnoreTrivia = -1

            for t = runFirstTok to lastScanTok do
                let tok = tokens[t]

                let lim =
                    if footerSkip > 0 && t = footerTokIdx then
                        tok.TriviaStart + footerSkip
                    else
                        tok.TriviaStart + tok.LeadingCount + tok.TrailingCount

                for k = tok.TriviaStart to lim - 1 do
                    let item = triv[k]

                    if item.Kind = TriviaKind.SingleLineCommentTrivia then
                        let mk = ignoreCommentKind span item

                        if mk = 2 then
                            if not openIgnore then
                                openIgnore <- true
                                openIgnoreBraceDepth <- braceDepth

                            if t >= runFirstTok then
                                lastNonEndIgnoreTrivia <- k
                        elif mk = 1 then
                            if t >= runFirstTok then
                                lastNonEndIgnoreTrivia <- k
                        elif mk = 3 then
                            while ci < commentsOut.Count && commentsOut[ci].TriviaIndex < k do
                                ci <- ci + 1

                            if ci < commentsOut.Count && commentsOut[ci].TriviaIndex = k then
                                let cur = commentsOut[ci]

                                if not openIgnore then
                                    commentsOut[ci] <- { cur with IsInertIgnoreEnd = true }

                                ci <- ci + 1

                            if openIgnore && braceDepth <= openIgnoreBraceDepth then
                                openIgnore <- false

                if tok.Kind = TokenKind.OpenBraceToken then
                    braceDepth <- braceDepth + 1
                elif tok.Kind = TokenKind.CloseBraceToken then
                    if braceDepth > 0 then
                        braceDepth <- braceDepth - 1

                    if openIgnore && braceDepth < openIgnoreBraceDepth then
                        openIgnore <- false

            if lastNonEndIgnoreTrivia >= 0 then
                for idx = 0 to commentsOut.Count - 1 do
                    let cur = commentsOut[idx]

                    if cur.IsInertIgnoreEnd && cur.TriviaIndex < lastNonEndIgnoreTrivia then
                        commentsOut[idx] <- { cur with IsInertIgnoreEnd = false }

    let private hashUsingCommentKey
        (text: ReadOnlySpan<char>)
        (item: Trivia)
        (c: UsingRunComment)
        (dirSeq: int)
        =
        let mutable h = 14695981039346656037UL
        h <- (h ^^^ uint64 c.Frame) * 1099511628211UL
        h <- (h ^^^ uint64 c.Ctx) * 1099511628211UL
        h <- (h ^^^ uint64 c.RegionDepth) * 1099511628211UL
        h <- (h ^^^ uint64 dirSeq) * 1099511628211UL
        h <- (h ^^^ uint64 (int item.Kind)) * 1099511628211UL
        let mutable pos = item.Start
        let finish = item.Start + item.Length

        while pos < finish do
            let struct (ls, len, next) = CommentContent.lineSpan text finish pos
            h <- (h ^^^ 0xFFUL) * 1099511628211UL

            for i = 0 to len - 1 do
                h <- (h ^^^ uint64 (int text[ls + i])) * 1099511628211UL

            pos <- next

        h

    let private hashDirectiveSpanningKey
        (c: UsingRunComment)
        (kind: TriviaKind)
        (leavesCount: int)
        (kept: ResizeArray<string>)
        =
        let mutable h = 14695981039346656037UL
        h <- (h ^^^ uint64 c.Frame) * 1099511628211UL
        h <- (h ^^^ uint64 c.Ctx) * 1099511628211UL
        h <- (h ^^^ uint64 c.RegionDepth) * 1099511628211UL
        h <- (h ^^^ uint64 c.DirSeq) * 1099511628211UL
        h <- (h ^^^ uint64 (int kind)) * 1099511628211UL
        h <- (h ^^^ uint64 leavesCount) * 1099511628211UL

        for i = 0 to kept.Count - 1 do
            let s = kept[i]
            h <- (h ^^^ 0xFFUL) * 1099511628211UL

            for j = 0 to s.Length - 1 do
                h <- (h ^^^ uint64 (int s[j])) * 1099511628211UL

        h

    let inline private usingFooterBucketIndex (hash: uint64) (bucketMask: int) =
        int (uint32 ((hash >>> 32) ^^^ hash)) &&& bucketMask

    let private docPolyBase = 11400714819323198485UL

    let private hashUsingDocLineFp (text: ReadOnlySpan<char>) (lineStart: int) (lineLen: int) =
        let mutable h = 14695981039346656037UL

        for i = 0 to lineLen - 1 do
            h <- (h ^^^ uint64 (int text[lineStart + i])) * 1099511628211UL

        (h ^^^ 0x9e3779b97f4a7c15UL) * 1099511628211UL

    let inline private mixUsingPreCondHash (baseHash: uint64) (reqPreCond: bool) =
        (baseHash ^^^ (if reqPreCond then 0x9e3779b97f4a7c15UL else 0UL))
        * 1099511628211UL

    let private mixUsingDocSliceKey
        (c: UsingRunComment)
        (polyHash: uint64)
        (lineCount: int)
        (reqPreCond: bool)
        =
        let mutable h = 14695981039346656037UL
        h <- (h ^^^ uint64 c.Frame) * 1099511628211UL
        h <- (h ^^^ uint64 c.Ctx) * 1099511628211UL
        h <- (h ^^^ uint64 c.RegionDepth) * 1099511628211UL
        h <- (h ^^^ uint64 c.DirSeq) * 1099511628211UL
        h <- (h ^^^ uint64 lineCount) * 1099511628211UL
        h <- (h ^^^ polyHash) * 1099511628211UL
        mixUsingPreCondHash h reqPreCond

    let private evalUsingDocPoly (text: ReadOnlySpan<char>) (item: Trivia) =
        let finish = item.Start + item.Length
        let mutable pos = item.Start
        let mutable count = 0
        let mutable poly = 0UL

        while pos < finish do
            let struct (ls, len, next) = CommentContent.lineSpan text finish pos
            let fp = hashUsingDocLineFp text ls len
            poly <- poly * docPolyBase + fp
            count <- count + 1
            pos <- next

        struct (count, poly)

    let private buildUsingFooterCsr
        (count: int)
        (hashes: uint64 array)
        (countsIn: int array)
        (offsetsIn: int array)
        (itemsIn: int array)
        =
        let mutable bucketCount = 64

        while bucketCount < count * 2 && bucketCount < (1 <<< 30) do
            bucketCount <- bucketCount <<< 1

        let counts = grownIndices countsIn bucketCount
        Array.fill counts 0 bucketCount 0
        let offsets = grownIndices offsetsIn (bucketCount + 1)
        let items = grownIndices itemsIn count
        let bucketMask = bucketCount - 1

        for i = 0 to count - 1 do
            let bucket = usingFooterBucketIndex hashes[i] bucketMask
            counts[bucket] <- counts[bucket] + 1

        let mutable offset = 0

        for b = 0 to bucketCount - 1 do
            offsets[b] <- offset
            let cnt = counts[b]
            counts[b] <- offset
            offset <- offset + cnt

        offsets[bucketCount] <- offset

        for i = 0 to count - 1 do
            let bucket = usingFooterBucketIndex hashes[i] bucketMask
            let pos = counts[bucket]
            items[pos] <- i
            counts[bucket] <- pos + 1

        struct (bucketMask, counts, offsets, items)

    let private lowerBoundSlice (items: int array) (lo0: int) (hiExcl: int) (target: int) =
        let mutable lo = lo0
        let mutable hi = hiExcl

        while lo < hi do
            let mid = lo + ((hi - lo) >>> 1)
            if items[mid] < target then lo <- mid + 1 else hi <- mid

        lo

    let private lowerBoundIndexedBf
        (items: int array)
        (bfIdxs: ResizeArray<int>)
        (docStarts: ResizeArray<int>)
        (lo0: int)
        (hiExcl: int)
        (targetBfIdx: int)
        (minSameIdxStart: int)
        =
        let mutable lo = lo0
        let mutable hi = hiExcl
        let checkSameStart = minSameIdxStart > 0 && not (isNull docStarts)

        while lo < hi do
            let mid = lo + ((hi - lo) >>> 1)
            let entryIdx = items[mid]
            let bfIdx = bfIdxs[entryIdx]

            if
                bfIdx < targetBfIdx
                || (checkSameStart && bfIdx = targetBfIdx && docStarts[entryIdx] < minSameIdxStart)
            then
                lo <- mid + 1
            else
                hi <- mid

        lo

    let private lowerBoundResize (items: ResizeArray<int>) (target: int) =
        let mutable lo = 0
        let mutable hi = items.Count

        while lo < hi do
            let mid = lo + ((hi - lo) >>> 1)
            if items[mid] < target then lo <- mid + 1 else hi <- mid

        lo

    let inline private usingCommentRegionMatches
        (inC: UsingRunComment)
        (outC: UsingRunComment)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (isFloating: bool)
        =
        if
            useRelativeRegion
            && not isFloating
            && inC.Frame = inClauseFrame
            && outC.Frame = outClauseFrame
            && inC.RegionSeq = inClauseRegionSeq
        then
            outC.RegionSeq = outClauseRegionSeq
            && (inC.RegionDepth - inClauseRegionDepth) = (outC.RegionDepth - outClauseRegionDepth)
        else
            inC.RegionDepth = outC.RegionDepth

    let inline private usingCommentFrameMatches
        (inC: UsingRunComment)
        (outC: UsingRunComment)
        (useRelativeFrame: bool)
        (isFloating: bool)
        =
        if
            useRelativeFrame
            && not isFloating
            && (inC.SlotRelFrame >= 0 || outC.SlotRelFrame >= 0)
        then
            inC.SlotRelFrame = outC.SlotRelFrame
        else
            inC.Frame = outC.Frame

    let private tryMatchSingleUsingComment
        (allowDirectiveSpanning: bool)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outC: UsingRunComment)
        (requireDirSeq: bool)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (isFloating: bool)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        (pendingRawSpans: ResizeArray<struct (int * int * int * int)>)
        =
        if
            not (usingCommentFrameMatches inC outC useRelativeRegion isFloating)
            || inC.Ctx <> outC.Ctx
            || not (
                usingCommentRegionMatches
                    inC
                    outC
                    useRelativeRegion
                    inClauseFrame
                    inClauseRegionDepth
                    inClauseRegionSeq
                    outClauseFrame
                    outClauseRegionDepth
                    outClauseRegionSeq
                    isFloating
            )
            || (requireDirSeq && not (usingCommentDirSeqMatches inC outC))
        then
            false
        else
            let a = lTriv[inC.TriviaIndex]
            let b = rTriv[outC.TriviaIndex]

            if a.Kind = b.Kind && CommentContent.equivalentSpan lSpan a rSpan b then
                true
            elif
                allowDirectiveSpanning
                && (a.Kind = TriviaKind.MultiLineCommentTrivia
                    || a.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                && a.Kind = b.Kind
                && directiveSpanningMultiLineEquivalent
                    (lSpan.Slice(a.Start, a.Length))
                    (rSpan.Slice(b.Start, b.Length))
                    outerSpans
            then
                if not (isNull pendingRawSpans) then
                    for oi = 0 to outerSpans.Count - 1 do
                        let struct (relLS, relLE, relRS, relRE) = outerSpans[oi]

                        pendingRawSpans.Add(
                            struct (a.Start + relLS,
                                    a.Start + relLE,
                                    b.Start + relRS,
                                    b.Start + relRE)
                        )

                true
            else
                false

    let private findPairedUsingBoundaryDetachEnd
        (allowDirectiveSpanning: bool)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (rawInRunComments: ResizeArray<UsingRunComment>)
        (outRunComments: ResizeArray<UsingRunComment>)
        (inS: int)
        (inE: int)
        (inCFrame: int)
        (inCDepth: int)
        (inCSeq: int)
        (inCDir: int)
        (outClauseFrame: int)
        (outCDepth: int)
        (outCSeq: int)
        (outCDir: int)
        (origOutS: int)
        (initialDetachEnd: int)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        if initialDetachEnd <= origOutS || inS > inE then
            initialDetachEnd
        else
            let mutable detachEnd = initialDetachEnd
            let mutable curIn = inE
            let mutable matchingTail = true

            while matchingTail
                  && detachEnd > origOutS
                  && curIn >= inS
                  && (outRunComments[detachEnd - 1].Frame = outClauseFrame
                      || outRunComments[detachEnd - 1].SlotRelFrame >= 0) do
                let oc = outRunComments[detachEnd - 1]
                let targetRelDir = outCDir - oc.DirSeq

                while curIn >= inS && (inCDir - rawInRunComments[curIn].DirSeq) < targetRelDir do
                    curIn <- curIn - 1

                if curIn < inS || (inCDir - rawInRunComments[curIn].DirSeq) <> targetRelDir then
                    matchingTail <- false
                elif
                    tryMatchSingleUsingComment
                        allowDirectiveSpanning
                        lSpan
                        lTriv
                        rawInRunComments[curIn]
                        rSpan
                        rTriv
                        oc
                        false
                        true
                        inCFrame
                        inCDepth
                        inCSeq
                        outClauseFrame
                        outCDepth
                        outCSeq
                        false
                        outerSpans
                        null
                then
                    detachEnd <- detachEnd - 1
                    curIn <- curIn - 1
                else
                    let b = rTriv[oc.TriviaIndex]

                    if b.Kind <> TriviaKind.SingleLineDocumentationCommentTrivia then
                        matchingTail <- false
                    else
                        let bFinish = b.Start + b.Length
                        let bLines = countDocLines rSpan b
                        let mutable sumLines = 0
                        let mutable k = curIn
                        let mutable scanValid = true

                        while scanValid && k >= inS && sumLines < bLines do
                            let cand = rawInRunComments[k]
                            let a = lTriv[cand.TriviaIndex]

                            if
                                (inCDir - cand.DirSeq) = targetRelDir
                                && usingCommentFrameMatches cand oc true false
                                && cand.Ctx = oc.Ctx
                                && a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                                && usingCommentRegionMatches
                                    cand
                                    oc
                                    true
                                    inCFrame
                                    inCDepth
                                    inCSeq
                                    outClauseFrame
                                    outCDepth
                                    outCSeq
                                    false
                            then
                                sumLines <- sumLines + countDocLines lSpan a
                                k <- k - 1
                            else
                                scanValid <- false

                        let blockStart = k + 1

                        if sumLines <> bLines || blockStart > curIn then
                            matchingTail <- false
                        else
                            let mutable bPos = b.Start
                            let mutable docOk = true
                            let mutable m = blockStart

                            while docOk && m <= curIn do
                                if
                                    bPos < bFinish
                                    && docTriviaMatchesPrefix
                                        lSpan
                                        lTriv[rawInRunComments[m].TriviaIndex]
                                        rSpan
                                        &bPos
                                        bFinish
                                then
                                    m <- m + 1
                                else
                                    docOk <- false

                            if docOk && bPos >= bFinish then
                                detachEnd <- detachEnd - 1
                                curIn <- blockStart - 1
                            else
                                matchingTail <- false

            detachEnd

    let private docTriviaContainsFirstLine
        (lSpan: ReadOnlySpan<char>)
        (a: Trivia)
        (rSpan: ReadOnlySpan<char>)
        (b: Trivia)
        =
        let aFinish = a.Start + a.Length
        let bFinish = b.Start + b.Length
        let struct (aStart, aLen, _) = CommentContent.lineSpan lSpan aFinish a.Start
        let aSlice = lSpan.Slice(aStart, aLen)
        let mutable bPos = b.Start
        let mutable found = false

        while not found && bPos < bFinish do
            let struct (bStart, bLen, bNext) = CommentContent.lineSpan rSpan bFinish bPos

            if aLen = bLen && aSlice.SequenceEqual(rSpan.Slice(bStart, bLen)) then
                found <- true

            bPos <- bNext

        found

    let private tryConsumeUsingMergedDocFast
        (inComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (outC: UsingRunComment)
        (requireDirSeq: bool)
        (in2E: int)
        (skipConsumedIn2: bool)
        (inConsumed: bool array)
        (minRemainingOut: int)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (preI2: int)
        (preBPos: int)
        (bFinish: int)
        (preMatched: int)
        (consumedIndices: ResizeArray<int>)
        =
        let savedCount = consumedIndices.Count
        let mutable i2 = preI2
        let mutable bPos = preBPos
        let mutable matchedItems = preMatched
        let mutable preOk = true

        while preOk && bPos < bFinish do
            if skipConsumedIn2 then
                while i2 <= in2E && inConsumed[i2] do
                    i2 <- i2 + 1

            if i2 > in2E then
                preOk <- false
            else
                let cand = inComments[i2]
                let a = lTriv[cand.TriviaIndex]
                let isFloat = not (isNull inIsFloating) && inIsFloating[i2]

                let reg =
                    usingCommentRegionMatches
                        cand
                        outC
                        useRelativeRegion
                        inClauseFrame
                        inClauseRegionDepth
                        inClauseRegionSeq
                        outClauseFrame
                        outClauseRegionDepth
                        outClauseRegionSeq
                        isFloat

                if
                    usingCommentFrameMatches cand outC useRelativeRegion isFloat
                    && cand.Ctx = outC.Ctx
                    && reg
                    && (not requireDirSeq || cand.DirSeq = outC.DirSeq)
                    && a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                    && docTriviaMatchesPrefix lSpan a rSpan &bPos bFinish
                then
                    consumedIndices.Add i2
                    matchedItems <- matchedItems + 1
                    i2 <- i2 + 1
                else
                    preOk <- false

        if preOk && matchedItems >= 2 && (in2E - i2 + 1) >= minRemainingOut then
            i2
        else
            if consumedIndices.Count > savedCount then
                consumedIndices.RemoveRange(savedCount, consumedIndices.Count - savedCount)

            -1

    let private populateUsingDocSuffixBounds
        (inComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (b: Trivia)
        (bFinish: int)
        (outC: UsingRunComment)
        (requireDirSeq: bool)
        (cur2: int)
        (in2E: int)
        (skipConsumedIn2: bool)
        (inConsumed: bool array)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (docLinesScratch: ResizeArray<int>)
        (docSuffixScratch: ResizeArray<int>)
        =
        docLinesScratch.Clear()
        let mutable p = b.Start

        while p < bFinish do
            docLinesScratch.Add p
            let struct (_, _, pNext) = CommentContent.lineSpan rSpan bFinish p
            p <- pNext

        docLinesScratch.Add bFinish
        let sufLen = in2E - cur2 + 2
        docSuffixScratch.Clear()

        for _ = 0 to sufLen - 1 do
            docSuffixScratch.Add 0

        for k = in2E downto cur2 do
            let cand = inComments[k]
            let a = lTriv[cand.TriviaIndex]
            let isFloat = not (isNull inIsFloating) && inIsFloating[k]

            let addLines =
                if
                    (not skipConsumedIn2 || not inConsumed[k])
                    && usingCommentFrameMatches cand outC useRelativeRegion isFloat
                    && cand.Ctx = outC.Ctx
                    && usingCommentRegionMatches
                        cand
                        outC
                        useRelativeRegion
                        inClauseFrame
                        inClauseRegionDepth
                        inClauseRegionSeq
                        outClauseFrame
                        outClauseRegionDepth
                        outClauseRegionSeq
                        isFloat
                    && (not requireDirSeq || cand.DirSeq = outC.DirSeq)
                    && a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                then
                    countDocLines lSpan a
                else
                    0

            docSuffixScratch[k - cur2] <- docSuffixScratch[k - cur2 + 1] + addLines

    let private tryConsumeUsingMergedDoc
        (inComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outC: UsingRunComment)
        (requireDirSeq: bool)
        (in1E: int)
        (canCrossToStream2: bool)
        (in2E: int)
        (skipConsumedIn2: bool)
        (inConsumed: bool array)
        (canGoFooter: bool array)
        (allowFooterSkipIn2: bool)
        (preferSkipIn2: bool)
        (minRemainingOut: int)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (rawOrigSlots: int array)
        (orderedToRaw: int array)
        (outOi: int)
        (useStream1: bool)
        (cur1: int)
        (cur2: int)
        (consumedIndices: ResizeArray<int>)
        (sharedDocFailed: HashSet<struct (int * int * int * int)>)
        (docLinesScratch: ResizeArray<int>)
        (docSuffixScratch: ResizeArray<int>)
        =
        let b = rTriv[outC.TriviaIndex]

        if b.Kind <> TriviaKind.SingleLineDocumentationCommentTrivia then
            struct (false, useStream1, cur1, cur2)
        else
            let savedCount = consumedIndices.Count
            let bFinish = b.Start + b.Length
            let mutable preS1 = useStream1
            let mutable preI1 = cur1
            let mutable preI2 = cur2
            let mutable preOk = true

            if preS1 && preI1 > in1E then
                if canCrossToStream2 then preS1 <- false else preOk <- false

            if preOk && not preS1 && skipConsumedIn2 then
                while preI2 <= in2E && inConsumed[preI2] do
                    preI2 <- preI2 + 1

            let firstMatchIdx =
                if not preOk then -1
                elif preS1 then preI1
                elif preI2 <= in2E then preI2
                else -1

            if firstMatchIdx < 0 then
                struct (false, useStream1, cur1, cur2)
            else
                let mutable preBPos = b.Start
                let mutable preMatched = 0
                let cand0 = inComments[firstMatchIdx]
                let a0 = lTriv[cand0.TriviaIndex]
                let isFloat0 = not (isNull inIsFloating) && inIsFloating[firstMatchIdx]

                let reg0 =
                    usingCommentRegionMatches
                        cand0
                        outC
                        (useRelativeRegion && not preS1)
                        inClauseFrame
                        inClauseRegionDepth
                        inClauseRegionSeq
                        outClauseFrame
                        outClauseRegionDepth
                        outClauseRegionSeq
                        isFloat0

                if
                    usingCommentFrameMatches cand0 outC (useRelativeRegion && not preS1) isFloat0
                    && cand0.Ctx = outC.Ctx
                    && reg0
                    && (not requireDirSeq || cand0.DirSeq = outC.DirSeq)
                    && a0.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                    && docTriviaMatchesPrefix lSpan a0 rSpan &preBPos bFinish
                then
                    consumedIndices.Add firstMatchIdx
                    preMatched <- 1

                    if preS1 then preI1 <- preI1 + 1 else preI2 <- preI2 + 1
                else
                    preOk <- false

                while preOk && preS1 && preBPos < bFinish do
                    if preI1 > in1E then
                        if canCrossToStream2 then preS1 <- false else preOk <- false
                    else
                        let cand = inComments[preI1]
                        let a = lTriv[cand.TriviaIndex]
                        let isFloat = not (isNull inIsFloating) && inIsFloating[preI1]

                        let reg =
                            usingCommentRegionMatches
                                cand
                                outC
                                false
                                inClauseFrame
                                inClauseRegionDepth
                                inClauseRegionSeq
                                outClauseFrame
                                outClauseRegionDepth
                                outClauseRegionSeq
                                isFloat

                        if
                            cand.Frame = outC.Frame
                            && cand.Ctx = outC.Ctx
                            && reg
                            && (not requireDirSeq || cand.DirSeq = outC.DirSeq)
                            && a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                            && docTriviaMatchesPrefix lSpan a rSpan &preBPos bFinish
                        then
                            consumedIndices.Add preI1
                            preMatched <- preMatched + 1
                            preI1 <- preI1 + 1
                        else
                            preOk <- false

                let mutable fastNextI2 = -1

                if not preOk then
                    if consumedIndices.Count > savedCount then
                        consumedIndices.RemoveRange(savedCount, consumedIndices.Count - savedCount)

                    struct (false, useStream1, cur1, cur2)
                elif preBPos >= bFinish then
                    let remInTotal =
                        (if preS1 && preI1 <= in1E then in1E - preI1 + 1 else 0)
                        + max 0 (in2E - preI2 + 1)

                    if preMatched >= 2 && remInTotal >= minRemainingOut then
                        struct (true, preS1, preI1, preI2)
                    else
                        if consumedIndices.Count > savedCount then
                            consumedIndices.RemoveRange(
                                savedCount,
                                consumedIndices.Count - savedCount
                            )

                        struct (false, useStream1, cur1, cur2)
                elif
                    not (isNull sharedDocFailed)
                    && outOi >= 0
                    && sharedDocFailed.Contains(struct (outOi, preBPos, preI2, min 2 preMatched))
                then
                    if consumedIndices.Count > savedCount then
                        consumedIndices.RemoveRange(savedCount, consumedIndices.Count - savedCount)

                    struct (false, useStream1, cur1, cur2)
                elif
                    (not allowFooterSkipIn2 || not preferSkipIn2)
                    && (let nextI2 =
                            tryConsumeUsingMergedDocFast
                                inComments
                                lSpan
                                lTriv
                                rSpan
                                outC
                                requireDirSeq
                                in2E
                                skipConsumedIn2
                                inConsumed
                                minRemainingOut
                                useRelativeRegion
                                inClauseFrame
                                inClauseRegionDepth
                                inClauseRegionSeq
                                outClauseFrame
                                outClauseRegionDepth
                                outClauseRegionSeq
                                inIsFloating
                                preI2
                                preBPos
                                bFinish
                                preMatched
                                consumedIndices

                        if nextI2 >= 0 then
                            fastNextI2 <- nextI2
                            true
                        else
                            not allowFooterSkipIn2)
                then
                    if fastNextI2 >= 0 then
                        struct (true, false, preI1, fastNextI2)
                    else
                        struct (false, useStream1, cur1, cur2)
                else
                    let mutable remBPos = preBPos
                    let mutable remMatches = preMatched
                    let mutable k2 = preI2
                    let mutable blocked = false
                    let mutable lastMatchIdx = firstMatchIdx

                    while not blocked && remBPos < bFinish && k2 <= in2E do
                        if skipConsumedIn2 && inConsumed[k2] then
                            k2 <- k2 + 1
                        else
                            let cand = inComments[k2]
                            let a = lTriv[cand.TriviaIndex]
                            let isFloat = not (isNull inIsFloating) && inIsFloating[k2]

                            let isEligible =
                                usingCommentFrameMatches cand outC useRelativeRegion isFloat
                                && cand.Ctx = outC.Ctx
                                && usingCommentRegionMatches
                                    cand
                                    outC
                                    useRelativeRegion
                                    inClauseFrame
                                    inClauseRegionDepth
                                    inClauseRegionSeq
                                    outClauseFrame
                                    outClauseRegionDepth
                                    outClauseRegionSeq
                                    isFloat
                                && (not requireDirSeq || cand.DirSeq = outC.DirSeq)
                                && a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia

                            let canSkipItem = not (isNull canGoFooter) && canGoFooter[k2]

                            if isEligible then
                                let aFinish = a.Start + a.Length
                                let mutable aPos = a.Start
                                let mutable matchedInK2 = false

                                while remBPos < bFinish && aPos < aFinish do
                                    let struct (aStart, aLen, aNext) =
                                        CommentContent.lineSpan lSpan aFinish aPos

                                    let struct (bStart, bLen, bNext) =
                                        CommentContent.lineSpan rSpan bFinish remBPos

                                    if
                                        aLen = bLen
                                        && lSpan
                                            .Slice(aStart, aLen)
                                            .SequenceEqual(rSpan.Slice(bStart, bLen))
                                    then
                                        remBPos <- bNext
                                        matchedInK2 <- true

                                    aPos <- aNext

                                if matchedInK2 then
                                    remMatches <- remMatches + 1
                                    lastMatchIdx <- k2
                                elif
                                    not canSkipItem
                                    && not (docTriviaContainsFirstLine lSpan a rSpan b)
                                then
                                    blocked <- true
                            elif not canSkipItem then
                                blocked <- true

                            k2 <- k2 + 1

                    if
                        remBPos < bFinish
                        || remMatches < 2
                        || (in2E - lastMatchIdx) < minRemainingOut
                    then
                        if not (isNull sharedDocFailed) && outOi >= 0 then
                            sharedDocFailed.Add(struct (outOi, preBPos, preI2, min 2 preMatched))
                            |> ignore

                        if consumedIndices.Count > savedCount then
                            consumedIndices.RemoveRange(
                                savedCount,
                                consumedIndices.Count - savedCount
                            )

                        struct (false, useStream1, cur1, cur2)
                    else
                        let useDocBounds =
                            not (isNull docLinesScratch)
                            && not (isNull docSuffixScratch)
                            && (in2E - cur2) >= 4

                        let mutable boundsBuilt = false
                        let mutable backtracks = 0
                        let mutable bPos = preBPos
                        let mutable i2 = preI2
                        let mutable matchedItems = preMatched
                        let mutable stack: ResizeArray<struct (int * int * int * int * int)> = null
                        let mutable failedStates: HashSet<struct (int * int)> = null
                        let mutable stepping = true
                        let mutable succeeded = false

                        while stepping do
                            let mutable needBacktrack = false

                            if bPos >= bFinish then
                                let remInTotal = max 0 (in2E - i2 + 1)

                                if matchedItems >= 2 && remInTotal >= minRemainingOut then
                                    succeeded <- true
                                    stepping <- false
                                else
                                    needBacktrack <- true
                            else
                                if skipConsumedIn2 then
                                    while i2 <= in2E && inConsumed[i2] do
                                        i2 <- i2 + 1

                                if i2 > in2E then
                                    needBacktrack <- true
                                elif
                                    (not (isNull failedStates)
                                     && failedStates.Contains(struct (bPos, i2)))
                                    || (not (isNull sharedDocFailed)
                                        && outOi >= 0
                                        && sharedDocFailed.Contains(
                                            struct (outOi, bPos, i2, min 2 matchedItems)
                                        ))
                                then
                                    needBacktrack <- true
                                else
                                    let mutable boundFail = false

                                    if boundsBuilt then
                                        let availLines = docSuffixScratch[i2 - cur2]
                                        let totalBLines = docLinesScratch.Count - 1
                                        let mutable lo = 0
                                        let mutable hi = totalBLines

                                        while lo < hi do
                                            let mid = lo + ((hi - lo) >>> 1)

                                            if docLinesScratch[mid] < bPos then
                                                lo <- mid + 1
                                            else
                                                hi <- mid

                                        let remBLines = totalBLines - lo

                                        if availLines < remBLines then
                                            boundFail <- true

                                    if boundFail then
                                        if not (isNull sharedDocFailed) && outOi >= 0 then
                                            sharedDocFailed.Add(
                                                struct (outOi, bPos, i2, min 2 matchedItems)
                                            )
                                            |> ignore

                                        needBacktrack <- true
                                    else
                                        let cand = inComments[i2]
                                        let a = lTriv[cand.TriviaIndex]

                                        let isFloating =
                                            not (isNull inIsFloating) && inIsFloating[i2]

                                        let regionMatches =
                                            usingCommentRegionMatches
                                                cand
                                                outC
                                                useRelativeRegion
                                                inClauseFrame
                                                inClauseRegionDepth
                                                inClauseRegionSeq
                                                outClauseFrame
                                                outClauseRegionDepth
                                                outClauseRegionSeq
                                                isFloating

                                        let savedBPos = bPos
                                        let mutable nextBPos = bPos

                                        let candMatches =
                                            usingCommentFrameMatches
                                                cand
                                                outC
                                                useRelativeRegion
                                                isFloating
                                            && cand.Ctx = outC.Ctx
                                            && regionMatches
                                            && (not requireDirSeq || cand.DirSeq = outC.DirSeq)
                                            && a.Kind =
                                                TriviaKind.SingleLineDocumentationCommentTrivia
                                            && docTriviaMatchesPrefix
                                                lSpan
                                                a
                                                rSpan
                                                &nextBPos
                                                bFinish

                                        if
                                            matchedItems > 0
                                            && not (isNull canGoFooter)
                                            && canGoFooter[i2]
                                        then
                                            if candMatches then
                                                if isNull stack then
                                                    stack <- ResizeArray()
                                                    failedStates <- HashSet()

                                                if preferSkipIn2 then
                                                    stack.Add(
                                                        struct (savedBPos,
                                                                i2,
                                                                consumedIndices.Count,
                                                                matchedItems,
                                                                0)
                                                    )

                                                    i2 <- i2 + 1
                                                else
                                                    stack.Add(
                                                        struct (savedBPos,
                                                                i2,
                                                                consumedIndices.Count,
                                                                matchedItems,
                                                                1)
                                                    )

                                                    bPos <- nextBPos
                                                    consumedIndices.Add i2
                                                    matchedItems <- matchedItems + 1
                                                    i2 <- i2 + 1
                                            else
                                                i2 <- i2 + 1
                                        elif candMatches then
                                            bPos <- nextBPos
                                            consumedIndices.Add i2
                                            matchedItems <- matchedItems + 1
                                            i2 <- i2 + 1
                                        else
                                            if not (isNull failedStates) then
                                                failedStates.Add(struct (savedBPos, i2)) |> ignore

                                            if not (isNull sharedDocFailed) && outOi >= 0 then
                                                sharedDocFailed.Add(
                                                    struct (outOi, savedBPos, i2, min 2 matchedItems)
                                                )
                                                |> ignore

                                            needBacktrack <- true

                            if needBacktrack then
                                backtracks <- backtracks + 1

                                if not boundsBuilt && useDocBounds && backtracks >= 8 then
                                    populateUsingDocSuffixBounds
                                        inComments
                                        lSpan
                                        lTriv
                                        rSpan
                                        b
                                        bFinish
                                        outC
                                        requireDirSeq
                                        cur2
                                        in2E
                                        skipConsumedIn2
                                        inConsumed
                                        useRelativeRegion
                                        inClauseFrame
                                        inClauseRegionDepth
                                        inClauseRegionSeq
                                        outClauseFrame
                                        outClauseRegionDepth
                                        outClauseRegionSeq
                                        inIsFloating
                                        docLinesScratch
                                        docSuffixScratch

                                    boundsBuilt <- true

                                let mutable resumed = false

                                while not resumed && not (isNull stack) && stack.Count > 0 do
                                    let topIdx = stack.Count - 1

                                    let struct (fBPos, fIdx, fSavedConsumed, fSavedMatched, fMode) =
                                        stack[topIdx]

                                    stack.RemoveAt topIdx

                                    if consumedIndices.Count > fSavedConsumed then
                                        consumedIndices.RemoveRange(
                                            fSavedConsumed,
                                            consumedIndices.Count - fSavedConsumed
                                        )

                                    if fMode = 2 then
                                        failedStates.Add(struct (fBPos, fIdx)) |> ignore

                                        if not (isNull sharedDocFailed) && outOi >= 0 then
                                            sharedDocFailed.Add(
                                                struct (outOi, fBPos, fIdx, min 2 fSavedMatched)
                                            )
                                            |> ignore
                                    elif fMode = 0 then
                                        let mutable nextBPos = fBPos
                                        let a = lTriv[inComments[fIdx].TriviaIndex]

                                        if
                                            docTriviaMatchesPrefix lSpan a rSpan &nextBPos bFinish
                                        then
                                            stack.Add(
                                                struct (fBPos,
                                                        fIdx,
                                                        fSavedConsumed,
                                                        fSavedMatched,
                                                        2)
                                            )

                                            bPos <- nextBPos
                                            consumedIndices.Add fIdx
                                            matchedItems <- fSavedMatched + 1
                                            i2 <- fIdx + 1
                                            resumed <- true
                                        else
                                            failedStates.Add(struct (fBPos, fIdx)) |> ignore

                                            if not (isNull sharedDocFailed) && outOi >= 0 then
                                                sharedDocFailed.Add(
                                                    struct (outOi, fBPos, fIdx, min 2 fSavedMatched)
                                                )
                                                |> ignore
                                    else
                                        stack.Add(
                                            struct (fBPos, fIdx, fSavedConsumed, fSavedMatched, 2)
                                        )

                                        bPos <- fBPos
                                        matchedItems <- fSavedMatched
                                        let mutable skipTo = fIdx + 1

                                        if not preferSkipIn2 then
                                            let fc = inComments[fIdx]
                                            let fa = lTriv[fc.TriviaIndex]

                                            let struct (_, _, faNext) =
                                                CommentContent.lineSpan
                                                    lSpan
                                                    (fa.Start + fa.Length)
                                                    fa.Start

                                            if faNext >= fa.Start + fa.Length then
                                                let fIsFloat =
                                                    not (isNull inIsFloating) && inIsFloating[fIdx]

                                                let hasOrigSlots =
                                                    not (isNull rawOrigSlots)
                                                    && not (isNull orderedToRaw)

                                                let fOrig =
                                                    if hasOrigSlots then
                                                        rawOrigSlots[orderedToRaw[fIdx]]
                                                    else
                                                        -1

                                                let mutable contRun = true

                                                while contRun && skipTo <= in2E do
                                                    let nc = inComments[skipTo]
                                                    let na = lTriv[nc.TriviaIndex]

                                                    let nIsFloat =
                                                        not (isNull inIsFloating)
                                                        && inIsFloating[skipTo]

                                                    let sameOrigin =
                                                        if hasOrigSlots then
                                                            fIsFloat = nIsFloat
                                                            && fOrig =
                                                                rawOrigSlots[orderedToRaw[skipTo]]
                                                        else
                                                            not fIsFloat && not nIsFloat

                                                    if
                                                        (not skipConsumedIn2
                                                         || not inConsumed[skipTo])
                                                        && not (isNull canGoFooter)
                                                        && canGoFooter[skipTo]
                                                        && sameOrigin
                                                        && nc.Frame = fc.Frame
                                                        && nc.Ctx = fc.Ctx
                                                        && nc.RegionDepth = fc.RegionDepth
                                                        && nc.RegionSeq = fc.RegionSeq
                                                        && nc.DirSeq = fc.DirSeq
                                                        && na.Kind = fa.Kind
                                                        && lSpan
                                                            .Slice(fa.Start, fa.Length)
                                                            .SequenceEqual(
                                                                lSpan.Slice(na.Start, na.Length)
                                                            )
                                                    then
                                                        skipTo <- skipTo + 1
                                                    else
                                                        contRun <- false

                                        i2 <- skipTo
                                        resumed <- true

                                if not resumed then
                                    stepping <- false

                        if succeeded then
                            struct (true, false, preI1, i2)
                        else
                            if not (isNull sharedDocFailed) && outOi >= 0 then
                                sharedDocFailed.Add(
                                    struct (outOi, preBPos, preI2, min 2 preMatched)
                                )
                                |> ignore

                            if consumedIndices.Count > savedCount then
                                consumedIndices.RemoveRange(
                                    savedCount,
                                    consumedIndices.Count - savedCount
                                )

                            struct (false, useStream1, cur1, cur2)

    let private tryMatchUsingOneItem
        (allowDirectiveSpanning: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outC: UsingRunComment)
        (requireDirSeq: bool)
        (in1E: int)
        (canCrossToStream2: bool)
        (in2E: int)
        (skipConsumedIn2: bool)
        (inConsumed: bool array)
        (canGoFooter: bool array)
        (allowFooterSkipIn2: bool)
        (preferSkipIn2: bool)
        (minRemainingOut: int)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (rawOrigSlots: int array)
        (orderedToRaw: int array)
        (outOi: int)
        (useStream1: bool)
        (cur1: int)
        (cur2: int)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        (pendingRawSpans: ResizeArray<struct (int * int * int * int)>)
        (consumedIndices: ResizeArray<int>)
        (sharedDocFailed: HashSet<struct (int * int * int * int)>)
        (docLinesScratch: ResizeArray<int>)
        (docSuffixScratch: ResizeArray<int>)
        =
        let idx = if useStream1 then cur1 else cur2
        let inC = inComments[idx]
        let isFloating = not (isNull inIsFloating) && inIsFloating[idx]

        if
            tryMatchSingleUsingComment
                allowDirectiveSpanning
                lSpan
                lTriv
                inC
                rSpan
                rTriv
                outC
                requireDirSeq
                (useRelativeRegion && not useStream1)
                inClauseFrame
                inClauseRegionDepth
                inClauseRegionSeq
                outClauseFrame
                outClauseRegionDepth
                outClauseRegionSeq
                isFloating
                outerSpans
                pendingRawSpans
        then
            consumedIndices.Add idx

            if useStream1 then
                struct (true, true, cur1 + 1, cur2)
            else
                struct (true, false, cur1, cur2 + 1)
        else
            tryConsumeUsingMergedDoc
                inComments
                lSpan
                lTriv
                rSpan
                rTriv
                outC
                requireDirSeq
                in1E
                canCrossToStream2
                in2E
                skipConsumedIn2
                inConsumed
                canGoFooter
                allowFooterSkipIn2
                preferSkipIn2
                minRemainingOut
                useRelativeRegion
                inClauseFrame
                inClauseRegionDepth
                inClauseRegionSeq
                outClauseFrame
                outClauseRegionDepth
                outClauseRegionSeq
                inIsFloating
                rawOrigSlots
                orderedToRaw
                outOi
                useStream1
                cur1
                cur2
                consumedIndices
                sharedDocFailed
                docLinesScratch
                docSuffixScratch

    let private tryMatchUsingHeaderPrefix
        (allowDirectiveSpanning: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (outComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outS: int)
        (outE: int)
        (in1S: int)
        (in1E: int)
        (in2S: int)
        (in2E: int)
        (inConsumed: bool array)
        (canGoFooter: bool array)
        (allowFooterSkipIn2: bool)
        (preferSkipIn2: bool)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (rawOrigSlots: int array)
        (orderedToRaw: int array)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        (pendingRawSpans: ResizeArray<struct (int * int * int * int)>)
        (consumedIndices: ResizeArray<int>)
        (sharedDocFailed: HashSet<struct (int * int * int * int)>)
        (docLinesScratch: ResizeArray<int>)
        (docSuffixScratch: ResizeArray<int>)
        =
        let mutable oi = outS
        let mutable cur1 = in1S
        let mutable cur2 = in2S
        let mutable ok = true

        while ok && oi <= outE && cur1 <= in1E do
            let struct (matched, nextS1, next1, next2) =
                tryMatchUsingOneItem
                    allowDirectiveSpanning
                    inComments
                    lSpan
                    lTriv
                    rSpan
                    rTriv
                    outComments[oi]
                    false
                    in1E
                    true
                    in2E
                    false
                    inConsumed
                    canGoFooter
                    allowFooterSkipIn2
                    preferSkipIn2
                    (outE - oi)
                    useRelativeRegion
                    inClauseFrame
                    inClauseRegionDepth
                    inClauseRegionSeq
                    outClauseFrame
                    outClauseRegionDepth
                    outClauseRegionSeq
                    inIsFloating
                    rawOrigSlots
                    orderedToRaw
                    oi
                    true
                    cur1
                    cur2
                    outerSpans
                    pendingRawSpans
                    consumedIndices
                    sharedDocFailed
                    docLinesScratch
                    docSuffixScratch

            if not matched then
                ok <- false
            else
                oi <- oi + 1
                cur1 <- next1
                cur2 <- next2

                if not nextS1 && cur1 <= in1E then
                    ok <- false

        if ok && cur1 > in1E then
            struct (true, oi, cur2)
        else
            struct (false, outS, in2S)

    let private maxUsingHeaderSplitPrefix
        (allowDirectiveSpanning: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (outComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (in0S: int)
        (in0E: int)
        (out0S: int)
        (out0E: int)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        let mutable oi = out0S
        let mutable cur1 = in0S
        let mutable advancing = true

        while advancing && oi <= out0E && cur1 <= in0E do
            let inC = inComments[cur1]
            let outC = outComments[oi]

            if
                tryMatchSingleUsingComment
                    allowDirectiveSpanning
                    lSpan
                    lTriv
                    inC
                    rSpan
                    rTriv
                    outC
                    false
                    false
                    0
                    0
                    0
                    0
                    0
                    0
                    false
                    outerSpans
                    null
            then
                cur1 <- cur1 + 1
                oi <- oi + 1
            else
                let b = rTriv[outC.TriviaIndex]

                if b.Kind <> TriviaKind.SingleLineDocumentationCommentTrivia then
                    advancing <- false
                else
                    let bFinish = b.Start + b.Length
                    let mutable bPos = b.Start
                    let mutable matchedItems = 0
                    let mutable same = true

                    while same && bPos < bFinish && cur1 <= in0E do
                        let cand = inComments[cur1]
                        let a = lTriv[cand.TriviaIndex]

                        if
                            cand.Frame <> outC.Frame
                            || cand.Ctx <> outC.Ctx
                            || cand.RegionDepth <> outC.RegionDepth
                            || a.Kind <> TriviaKind.SingleLineDocumentationCommentTrivia
                        then
                            same <- false
                        elif docTriviaMatchesPrefix lSpan a rSpan &bPos bFinish then
                            cur1 <- cur1 + 1
                            matchedItems <- matchedItems + 1
                        else
                            same <- false

                    if same && bPos >= bFinish && matchedItems >= 2 then
                        oi <- oi + 1
                    else
                        advancing <- false

        cur1 - in0S

    let private tryMatchUsingStream2NoSkip
        (allowDirectiveSpanning: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (outComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outS: int)
        (outE: int)
        (in2S: int)
        (in2E: int)
        (inConsumed: bool array)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        (pendingRawSpans: ResizeArray<struct (int * int * int * int)>)
        (consumedIndices: ResizeArray<int>)
        (failedMemo: HashSet<struct (int * int)>)
        (visitedIn: ResizeArray<int>)
        =
        let mutable oi = outS
        let mutable cur2 = in2S
        let mutable ok = true

        if not (isNull visitedIn) then
            visitedIn.Clear()

        while ok && oi <= outE do
            if cur2 > in2E then
                ok <- false
            elif not (isNull failedMemo) && failedMemo.Contains(struct (oi, cur2)) then
                ok <- false
            else
                if not (isNull visitedIn) then
                    visitedIn.Add cur2

                let struct (matched, _, _, next2) =
                    tryMatchUsingOneItem
                        allowDirectiveSpanning
                        inComments
                        lSpan
                        lTriv
                        rSpan
                        rTriv
                        outComments[oi]
                        false
                        -1
                        false
                        in2E
                        false
                        inConsumed
                        null
                        false
                        false
                        0
                        useRelativeRegion
                        inClauseFrame
                        inClauseRegionDepth
                        inClauseRegionSeq
                        outClauseFrame
                        outClauseRegionDepth
                        outClauseRegionSeq
                        inIsFloating
                        null
                        null
                        oi
                        false
                        0
                        cur2
                        outerSpans
                        pendingRawSpans
                        consumedIndices
                        null
                        null
                        null

                if not matched then
                    ok <- false
                else
                    oi <- oi + 1
                    cur2 <- next2

        if ok && cur2 > in2E then
            true
        else
            if not (isNull failedMemo) && not (isNull visitedIn) then
                for k = 0 to visitedIn.Count - 1 do
                    failedMemo.Add(struct (outS + k, visitedIn[k])) |> ignore

            false

    let private canMatchUsingSubsequence
        (allowDirectiveSpanning: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (outComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outS: int)
        (outE: int)
        (in2S: int)
        (in2E: int)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        let mutable oi = outS
        let mutable ii = in2S
        let mutable ok = true

        while ok && oi <= outE do
            let outC = outComments[oi]
            let b = rTriv[outC.TriviaIndex]
            let mutable found = false

            let isMultiLineDoc =
                if b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                    let bFinish = b.Start + b.Length
                    let struct (_, _, bNext) = CommentContent.lineSpan rSpan bFinish b.Start
                    bNext < bFinish
                else
                    false

            if isMultiLineDoc then
                let bFinish = b.Start + b.Length

                let struct (bLineStart, bLineLen, _) = CommentContent.lineSpan rSpan bFinish b.Start

                while not found && ii <= in2E do
                    let inC = inComments[ii]
                    let isFloating = not (isNull inIsFloating) && inIsFloating[ii]

                    if
                        tryMatchSingleUsingComment
                            allowDirectiveSpanning
                            lSpan
                            lTriv
                            inC
                            rSpan
                            rTriv
                            outC
                            false
                            useRelativeRegion
                            inClauseFrame
                            inClauseRegionDepth
                            inClauseRegionSeq
                            outClauseFrame
                            outClauseRegionDepth
                            outClauseRegionSeq
                            isFloating
                            outerSpans
                            null
                    then
                        found <- true
                    elif
                        usingCommentFrameMatches inC outC useRelativeRegion isFloating
                        && inC.Ctx = outC.Ctx
                        && usingCommentRegionMatches
                            inC
                            outC
                            useRelativeRegion
                            inClauseFrame
                            inClauseRegionDepth
                            inClauseRegionSeq
                            outClauseFrame
                            outClauseRegionDepth
                            outClauseRegionSeq
                            isFloating
                    then
                        let a = lTriv[inC.TriviaIndex]

                        if a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                            let aFinish = a.Start + a.Length

                            let struct (aLineStart, aLineLen, _) =
                                CommentContent.lineSpan lSpan aFinish a.Start

                            if
                                aLineLen = bLineLen
                                && lSpan
                                    .Slice(aLineStart, aLineLen)
                                    .SequenceEqual(rSpan.Slice(bLineStart, bLineLen))
                            then
                                found <- true

                    ii <- ii + 1
            else
                while not found && ii <= in2E do
                    let isFloating = not (isNull inIsFloating) && inIsFloating[ii]

                    if
                        tryMatchSingleUsingComment
                            allowDirectiveSpanning
                            lSpan
                            lTriv
                            inComments[ii]
                            rSpan
                            rTriv
                            outC
                            false
                            useRelativeRegion
                            inClauseFrame
                            inClauseRegionDepth
                            inClauseRegionSeq
                            outClauseFrame
                            outClauseRegionDepth
                            outClauseRegionSeq
                            isFloating
                            outerSpans
                            null
                    then
                        found <- true

                    ii <- ii + 1

            if not found then ok <- false else oi <- oi + 1

        ok

    let private matchesUsingMandatoryDocSlice
        (lSpan: ReadOnlySpan<char>)
        (rSpan: ReadOnlySpan<char>)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inC: UsingRunComment)
        (a: Trivia)
        (outC: UsingRunComment)
        (b: Trivia)
        (isFloating: bool)
        =
        if
            a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
            && b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
            && usingCommentFrameMatches inC outC useRelativeRegion isFloating
            && inC.Ctx = outC.Ctx
            && usingCommentRegionMatches
                inC
                outC
                useRelativeRegion
                inClauseFrame
                inClauseRegionDepth
                inClauseRegionSeq
                outClauseFrame
                outClauseRegionDepth
                outClauseRegionSeq
                isFloating
        then
            let bFinish = b.Start + b.Length
            let struct (_, _, bNext) = CommentContent.lineSpan rSpan bFinish b.Start
            bNext < bFinish && docTriviaContainsFirstLine lSpan a rSpan b
        else
            false

    let private canMatchMandatoryInOut
        (allowDirectiveSpanning: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (outComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outS: int)
        (outE: int)
        (in2S: int)
        (in2E: int)
        (canGoFooter: bool array)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        let mutable ok = true
        let mutable pf = outS
        let mutable k = in2S

        while ok && k <= in2E do
            if not canGoFooter[k] then
                let inC = inComments[k]
                let a = lTriv[inC.TriviaIndex]
                let isFloating = not (isNull inIsFloating) && inIsFloating[k]
                let maxP = min outE (outS + (k - in2S))
                let mutable found = false

                while not found && pf <= maxP do
                    let outC = outComments[pf]

                    if
                        tryMatchSingleUsingComment
                            allowDirectiveSpanning
                            lSpan
                            lTriv
                            inC
                            rSpan
                            rTriv
                            outC
                            false
                            useRelativeRegion
                            inClauseFrame
                            inClauseRegionDepth
                            inClauseRegionSeq
                            outClauseFrame
                            outClauseRegionDepth
                            outClauseRegionSeq
                            isFloating
                            outerSpans
                            null
                    then
                        found <- true
                        pf <- pf + 1
                    elif
                        matchesUsingMandatoryDocSlice
                            lSpan
                            rSpan
                            useRelativeRegion
                            inClauseFrame
                            inClauseRegionDepth
                            inClauseRegionSeq
                            outClauseFrame
                            outClauseRegionDepth
                            outClauseRegionSeq
                            inC
                            a
                            outC
                            rTriv[outC.TriviaIndex]
                            isFloating
                    then
                        found <- true
                    else
                        pf <- pf + 1

                if not found then
                    ok <- false

            k <- k + 1

        if ok then
            let mutable pb = outE
            let mutable kb = in2E

            while ok && kb >= in2S do
                if not canGoFooter[kb] then
                    let inC = inComments[kb]
                    let a = lTriv[inC.TriviaIndex]
                    let isFloating = not (isNull inIsFloating) && inIsFloating[kb]
                    let minP = max outS (outE - (in2E - kb))
                    let mutable found = false

                    while not found && pb >= minP do
                        let outC = outComments[pb]

                        if
                            tryMatchSingleUsingComment
                                allowDirectiveSpanning
                                lSpan
                                lTriv
                                inC
                                rSpan
                                rTriv
                                outC
                                false
                                useRelativeRegion
                                inClauseFrame
                                inClauseRegionDepth
                                inClauseRegionSeq
                                outClauseFrame
                                outClauseRegionDepth
                                outClauseRegionSeq
                                isFloating
                                outerSpans
                                null
                        then
                            found <- true
                            pb <- pb - 1
                        elif
                            matchesUsingMandatoryDocSlice
                                lSpan
                                rSpan
                                useRelativeRegion
                                inClauseFrame
                                inClauseRegionDepth
                                inClauseRegionSeq
                                outClauseFrame
                                outClauseRegionDepth
                                outClauseRegionSeq
                                inC
                                a
                                outC
                                rTriv[outC.TriviaIndex]
                                isFloating
                        then
                            found <- true
                        else
                            pb <- pb - 1

                    if not found then
                        ok <- false

                kb <- kb - 1

        ok

    let private maxSplitForSuffixMin (pref: int array) (baseIdx: int) (len: int) (minSuffix: int) =
        if minSuffix <= 0 then
            len
        elif pref[baseIdx + len] - pref[baseIdx] < minSuffix then
            -1
        else
            let mutable lo = 0
            let mutable hi = len

            while lo < hi do
                let mid = (lo + hi + 1) >>> 1

                if pref[baseIdx + len] - pref[baseIdx + mid] >= minSuffix then
                    lo <- mid
                else
                    hi <- mid - 1

            lo

    let private minSplitForSuffixMax (pref: int array) (baseIdx: int) (len: int) (maxSuffix: int) =
        if maxSuffix < 0 then
            len + 1
        else
            let target = pref[baseIdx + len] - maxSuffix

            if target <= pref[baseIdx] then
                0
            else
                let mutable lo = 0
                let mutable hi = len

                while lo < hi do
                    let mid = (lo + hi) >>> 1

                    if pref[baseIdx + mid] >= target then
                        hi <- mid
                    else
                        lo <- mid + 1

                lo

    let private maxSplitForPrefixMax (pref: int array) (baseIdx: int) (len: int) (maxPrefix: int) =
        if maxPrefix < 0 then
            -1
        elif pref[baseIdx + len] - pref[baseIdx] <= maxPrefix then
            len
        else
            let target = pref[baseIdx] + maxPrefix
            let mutable lo = 0
            let mutable hi = len

            while lo < hi do
                let mid = (lo + hi + 1) >>> 1

                if pref[baseIdx + mid] <= target then
                    lo <- mid
                else
                    hi <- mid - 1

            lo

    let private minSplitForPrefixMin (pref: int array) (baseIdx: int) (len: int) (minPrefix: int) =
        if minPrefix <= 0 then
            0
        elif pref[baseIdx + len] - pref[baseIdx] < minPrefix then
            len + 1
        else
            let target = pref[baseIdx] + minPrefix
            let mutable lo = 0
            let mutable hi = len

            while lo < hi do
                let mid = (lo + hi) >>> 1

                if pref[baseIdx + mid] >= target then
                    hi <- mid
                else
                    lo <- mid + 1

            lo

    let inline private usingFooterPreCondMatches
        (requiresPreCond: bool)
        (inC: UsingRunComment)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        =
        not requiresPreCond
        || (not (isNull inClauseDirSeqs)
            && origSlot < clauseCount
            && inC.DirSeq < inClauseDirSeqs[origSlot])

    let inline private packUsingBfKey (bfIdx: int) (bfPos: int) =
        (uint64 (uint32 bfIdx) <<< 32) ||| uint64 (uint32 bfPos)

    let private scanDocLineBucket
        (lSpan: ReadOnlySpan<char>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (a: Trivia)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (curIdx: int)
        (minSameIdxStart: int)
        (bestCandIdx: byref<int>)
        (bestNextIdx: byref<int>)
        (bestNextPos: byref<int>)
        (lineHash: uint64)
        (hashes: uint64 array)
        (bfIdxs: ResizeArray<int>)
        (docStarts: ResizeArray<int>)
        (bucketMask: int)
        (bucketOffsets: int array)
        (bucketItems: int array)
        =
        if not (isNull bfIdxs) && bfIdxs.Count > 0 then
            let bucket = usingFooterBucketIndex lineHash bucketMask
            let bStart = bucketOffsets[bucket]
            let bEnd = bucketOffsets[bucket + 1]

            let mutable pos =
                lowerBoundIndexedBf bucketItems bfIdxs docStarts bStart bEnd curIdx minSameIdxStart

            while pos < bEnd do
                let entryIdx = bucketItems[pos]
                let candIdx = bfIdxs[entryIdx]

                if candIdx >= bestCandIdx then
                    pos <- bEnd
                elif hashes[entryIdx] = lineHash then
                    let outC = bfComments[candIdx]

                    if
                        inC.Frame = outC.Frame
                        && inC.Ctx = outC.Ctx
                        && inC.RegionDepth = outC.RegionDepth
                        && inC.DirSeq = outC.DirSeq
                        && usingFooterPreCondMatches
                            bfRequiresPreCond[candIdx]
                            inC
                            origSlot
                            clauseCount
                            inClauseDirSeqs
                    then
                        let b = rTriv[outC.TriviaIndex]
                        let bFinish = b.Start + b.Length

                        let mutable nextPos =
                            if isNull docStarts then b.Start else docStarts[entryIdx]

                        if docTriviaMatchesPrefix lSpan a rSpan &nextPos bFinish then
                            bestCandIdx <- candIdx

                            if nextPos >= bFinish then
                                bestNextIdx <- candIdx + 1
                                bestNextPos <- 0
                            else
                                bestNextIdx <- candIdx
                                bestNextPos <- nextPos

                            pos <- bEnd
                        else
                            pos <- pos + 1
                    else
                        pos <- pos + 1
                else
                    pos <- pos + 1

    let private scanDocLineBucketPair
        (lSpan: ReadOnlySpan<char>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (a: Trivia)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (curIdx: int)
        (minSameIdxStart: int)
        (canUsePreCond: bool)
        (polyHash: uint64)
        (lineCount: int)
        (bestCandIdx: byref<int>)
        (bestNextIdx: byref<int>)
        (bestNextPos: byref<int>)
        (hashes: uint64 array)
        (bfIdxs: ResizeArray<int>)
        (docStarts: ResizeArray<int>)
        (bucketMask: int)
        (bucketOffsets: int array)
        (bucketItems: int array)
        =
        if not (isNull bfIdxs) && bfIdxs.Count > 0 then
            let hFalse = mixUsingDocSliceKey inC polyHash lineCount false

            scanDocLineBucket
                lSpan
                rSpan
                rTriv
                inC
                a
                origSlot
                clauseCount
                inClauseDirSeqs
                bfComments
                bfRequiresPreCond
                curIdx
                minSameIdxStart
                &bestCandIdx
                &bestNextIdx
                &bestNextPos
                hFalse
                hashes
                bfIdxs
                docStarts
                bucketMask
                bucketOffsets
                bucketItems

            if canUsePreCond then
                let hTrue = mixUsingDocSliceKey inC polyHash lineCount true

                scanDocLineBucket
                    lSpan
                    rSpan
                    rTriv
                    inC
                    a
                    origSlot
                    clauseCount
                    inClauseDirSeqs
                    bfComments
                    bfRequiresPreCond
                    curIdx
                    minSameIdxStart
                    &bestCandIdx
                    &bestNextIdx
                    &bestNextPos
                    hTrue
                    hashes
                    bfIdxs
                    docStarts
                    bucketMask
                    bucketOffsets
                    bucketItems

    let private indexedBucketBounds
        (bfIdxs: ResizeArray<int>)
        (docStarts: ResizeArray<int>)
        (bucketMask: int)
        (bucketOffsets: int array)
        (bucketItems: int array)
        (curIdx: int)
        (minSameIdxStart: int)
        (lineHash: uint64)
        =
        let bucket = usingFooterBucketIndex lineHash bucketMask
        let bStart = bucketOffsets[bucket]
        let bEnd = bucketOffsets[bucket + 1]

        let pos =
            lowerBoundIndexedBf bucketItems bfIdxs docStarts bStart bEnd curIdx minSameIdxStart

        struct (pos, bEnd)

    let private scanEvictedMidBucket
        (lSpan: ReadOnlySpan<char>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (a: Trivia)
        (docLineCount: int)
        (fullPoly: uint64)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (footerIndex: UsingFooterIndex)
        (curIdx: int)
        (minSameIdxStart: int)
        (bestJ: int)
        (bestCandIdx: byref<int>)
        (bestNextIdx: byref<int>)
        (bestNextPos: byref<int>)
        (targetHash: uint64)
        (hashes: uint64 array)
        (bfIdxs: ResizeArray<int>)
        (lineIdxs: ResizeArray<int>)
        (bucketItems: int array)
        (pos0: int)
        (bEnd: int)
        =
        let mutable pos = pos0
        let powM = footerIndex.PowBase[docLineCount]

        while pos < bEnd do
            let entryIdx = bucketItems[pos]
            let candIdx = bfIdxs[entryIdx]

            if candIdx >= bestCandIdx then
                pos <- bEnd
            elif hashes[entryIdx] = targetHash then
                let s = lineIdxs[entryIdx] - bestJ

                if s >= 1 then
                    let kLines = footerIndex.BfDocLineCounts[candIdx]

                    if s + docLineCount <= kLines then
                        let startOff = footerIndex.BfDocStartOff[candIdx]
                        let polyOff = footerIndex.BfDocPolyOff[candIdx]
                        let candStartPos = footerIndex.DocAllStarts[startOff + s]

                        if candIdx > curIdx || candStartPos >= minSameIdxStart then
                            let slicePoly =
                                footerIndex.DocAllPolys[polyOff + s + docLineCount]
                                - footerIndex.DocAllPolys[polyOff + s] * powM

                            if slicePoly = fullPoly then
                                let outC = bfComments[candIdx]

                                if
                                    inC.Frame = outC.Frame
                                    && inC.Ctx = outC.Ctx
                                    && inC.RegionDepth = outC.RegionDepth
                                    && inC.DirSeq = outC.DirSeq
                                    && usingFooterPreCondMatches
                                        bfRequiresPreCond[candIdx]
                                        inC
                                        origSlot
                                        clauseCount
                                        inClauseDirSeqs
                                then
                                    let b = rTriv[outC.TriviaIndex]
                                    let bFinish = b.Start + b.Length
                                    let mutable nextPos = candStartPos

                                    if docTriviaMatchesPrefix lSpan a rSpan &nextPos bFinish then
                                        bestCandIdx <- candIdx

                                        if nextPos >= bFinish then
                                            bestNextIdx <- candIdx + 1
                                            bestNextPos <- 0
                                        else
                                            bestNextIdx <- candIdx
                                            bestNextPos <- nextPos

                                        pos <- bEnd
                                    else
                                        pos <- pos + 1
                                else
                                    pos <- pos + 1
                            else
                                pos <- pos + 1
                        else
                            pos <- pos + 1
                    else
                        pos <- pos + 1
                else
                    pos <- pos + 1
            else
                pos <- pos + 1

    let private scanEvictedMidDocFallback
        (lSpan: ReadOnlySpan<char>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (a: Trivia)
        (docLineCount: int)
        (fullPoly: uint64)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (footerIndex: UsingFooterIndex)
        (curIdx: int)
        (minSameIdxStart: int)
        (canUsePreCond: bool)
        (bestCandIdx: byref<int>)
        (bestNextIdx: byref<int>)
        (bestNextPos: byref<int>)
        =
        if footerIndex.DocMidBfIdxs.Count > 0 then
            let aFinish = a.Start + a.Length
            let mutable pos = a.Start
            let mutable j = 0
            let mutable prevFp = 0UL
            let mutable bestCount = Int32.MaxValue
            let mutable bestIsPair = false
            let mutable bestJ = 0
            let mutable bestHFalse = 0UL
            let mutable bestHTrue = 0UL
            let mutable bestPosF = 0
            let mutable bestEndF = 0
            let mutable bestPosT = 0
            let mutable bestEndT = 0
            let hasPairIndex = footerIndex.DocMidMultiBfIdxs.Count > 0

            while bestCount > 0 && pos < aFinish do
                let struct (ls, len, next) = CommentContent.lineSpan lSpan aFinish pos
                let fp = hashUsingDocLineFp lSpan ls len
                let hF = mixUsingDocSliceKey inC fp 1 false

                let struct (pF, eF) =
                    indexedBucketBounds
                        footerIndex.DocMidBfIdxs
                        footerIndex.DocMidStarts
                        footerIndex.DocMidBucketMask
                        footerIndex.DocMidBucketOffsets
                        footerIndex.DocMidBucketItems
                        curIdx
                        minSameIdxStart
                        hF

                let mutable total = eF - pF
                let mutable hT = 0UL
                let mutable pT = 0
                let mutable eT = 0

                if canUsePreCond then
                    hT <- mixUsingDocSliceKey inC fp 1 true

                    let struct (tpT, teT) =
                        indexedBucketBounds
                            footerIndex.DocMidBfIdxs
                            footerIndex.DocMidStarts
                            footerIndex.DocMidBucketMask
                            footerIndex.DocMidBucketOffsets
                            footerIndex.DocMidBucketItems
                            curIdx
                            minSameIdxStart
                            hT

                    pT <- tpT
                    eT <- teT
                    total <- total + (eT - pT)

                if total < bestCount then
                    bestCount <- total
                    bestIsPair <- false
                    bestJ <- j
                    bestHFalse <- hF
                    bestHTrue <- hT
                    bestPosF <- pF
                    bestEndF <- eF
                    bestPosT <- pT
                    bestEndT <- eT

                if bestCount > 0 && hasPairIndex && j >= 1 then
                    let pairPoly = prevFp * docPolyBase + fp
                    let phF = mixUsingDocSliceKey inC pairPoly 2 false

                    let struct (ppF, peF) =
                        indexedBucketBounds
                            footerIndex.DocMidMultiBfIdxs
                            footerIndex.DocMidMultiStarts
                            footerIndex.DocMidMultiBucketMask
                            footerIndex.DocMidMultiBucketOffsets
                            footerIndex.DocMidMultiBucketItems
                            curIdx
                            minSameIdxStart
                            phF

                    let mutable pairTotal = peF - ppF
                    let mutable phT = 0UL
                    let mutable ppT = 0
                    let mutable peT = 0

                    if canUsePreCond then
                        phT <- mixUsingDocSliceKey inC pairPoly 2 true

                        let struct (tppT, tpeT) =
                            indexedBucketBounds
                                footerIndex.DocMidMultiBfIdxs
                                footerIndex.DocMidMultiStarts
                                footerIndex.DocMidMultiBucketMask
                                footerIndex.DocMidMultiBucketOffsets
                                footerIndex.DocMidMultiBucketItems
                                curIdx
                                minSameIdxStart
                                phT

                        ppT <- tppT
                        peT <- tpeT
                        pairTotal <- pairTotal + (peT - ppT)

                    if pairTotal < bestCount then
                        bestCount <- pairTotal
                        bestIsPair <- true
                        bestJ <- j - 1
                        bestHFalse <- phF
                        bestHTrue <- phT
                        bestPosF <- ppF
                        bestEndF <- peF
                        bestPosT <- ppT
                        bestEndT <- peT

                prevFp <- fp
                j <- j + 1
                pos <- next

            if bestCount > 0 && bestCount < Int32.MaxValue then
                let hashes =
                    if bestIsPair then
                        footerIndex.DocMidMultiHashes
                    else
                        footerIndex.DocMidHashes

                let bfIdxs =
                    if bestIsPair then
                        footerIndex.DocMidMultiBfIdxs
                    else
                        footerIndex.DocMidBfIdxs

                let lineIdxs =
                    if bestIsPair then
                        footerIndex.DocMidMultiLineIdxs
                    else
                        footerIndex.DocMidLineIdxs

                let bucketItems =
                    if bestIsPair then
                        footerIndex.DocMidMultiBucketItems
                    else
                        footerIndex.DocMidBucketItems

                if bestEndF > bestPosF then
                    scanEvictedMidBucket
                        lSpan
                        rSpan
                        rTriv
                        inC
                        a
                        docLineCount
                        fullPoly
                        origSlot
                        clauseCount
                        inClauseDirSeqs
                        bfComments
                        bfRequiresPreCond
                        footerIndex
                        curIdx
                        minSameIdxStart
                        bestJ
                        &bestCandIdx
                        &bestNextIdx
                        &bestNextPos
                        bestHFalse
                        hashes
                        bfIdxs
                        lineIdxs
                        bucketItems
                        bestPosF
                        bestEndF

                if canUsePreCond && bestEndT > bestPosT then
                    scanEvictedMidBucket
                        lSpan
                        rSpan
                        rTriv
                        inC
                        a
                        docLineCount
                        fullPoly
                        origSlot
                        clauseCount
                        inClauseDirSeqs
                        bfComments
                        bfRequiresPreCond
                        footerIndex
                        curIdx
                        minSameIdxStart
                        bestJ
                        &bestCandIdx
                        &bestNextIdx
                        &bestNextPos
                        bestHTrue
                        hashes
                        bfIdxs
                        lineIdxs
                        bucketItems
                        bestPosT
                        bestEndT

    let inline private usingFooterCandidateMatches
        (allowDirectiveSpanning: bool)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (candIdx: int)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        usingFooterPreCondMatches
            bfRequiresPreCond[candIdx]
            inC
            origSlot
            clauseCount
            inClauseDirSeqs
        && tryMatchSingleUsingComment
            allowDirectiveSpanning
            lSpan
            lTriv
            inC
            rSpan
            rTriv
            bfComments[candIdx]
            true
            false
            0
            0
            0
            0
            0
            0
            false
            outerSpans
            null

    let private findExactFooterBucketMatch
        (allowDirectiveSpanning: bool)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (footerIndex: UsingFooterIndex)
        (curIdx: int)
        (maxCandIdx: int)
        (targetHash: uint64)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        let bucket = usingFooterBucketIndex targetHash footerIndex.BucketMask
        let bStart = footerIndex.BucketOffsets[bucket]
        let bEnd = footerIndex.BucketOffsets[bucket + 1]
        let mutable bPos = lowerBoundSlice footerIndex.BucketItems bStart bEnd curIdx
        let mutable found = -1

        while found < 0 && bPos < bEnd do
            let candIdx = footerIndex.BucketItems[bPos]

            if candIdx >= maxCandIdx then
                bPos <- bEnd
            elif
                footerIndex.Hashes[candIdx] = targetHash
                && usingFooterCandidateMatches
                    allowDirectiveSpanning
                    lSpan
                    lTriv
                    rSpan
                    rTriv
                    inC
                    origSlot
                    clauseCount
                    inClauseDirSeqs
                    bfComments
                    bfRequiresPreCond
                    candIdx
                    outerSpans
            then
                found <- candIdx
            else
                bPos <- bPos + 1

        found

    let private findInertFooterBucketMatch
        (allowDirectiveSpanning: bool)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (footerIndex: UsingFooterIndex)
        (curIdx: int)
        (maxCandIdx: int)
        (targetHash: uint64)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        let bucket = usingFooterBucketIndex targetHash footerIndex.InertBucketMask
        let bStart = footerIndex.InertBucketOffsets[bucket]
        let bEnd = footerIndex.InertBucketOffsets[bucket + 1]

        let mutable bPos =
            lowerBoundIndexedBf
                footerIndex.InertBucketItems
                footerIndex.InertBfIdxs
                null
                bStart
                bEnd
                curIdx
                0

        let mutable found = -1

        while found < 0 && bPos < bEnd do
            let entryIdx = footerIndex.InertBucketItems[bPos]
            let candIdx = footerIndex.InertBfIdxs[entryIdx]

            if candIdx >= maxCandIdx then
                bPos <- bEnd
            elif
                footerIndex.InertHashes[entryIdx] = targetHash
                && usingFooterCandidateMatches
                    allowDirectiveSpanning
                    lSpan
                    lTriv
                    rSpan
                    rTriv
                    inC
                    origSlot
                    clauseCount
                    inClauseDirSeqs
                    bfComments
                    bfRequiresPreCond
                    candIdx
                    outerSpans
            then
                found <- candIdx
            else
                bPos <- bPos + 1

        found

    let private findBestExactFooterMatch
        (allowDirectiveSpanning: bool)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (a: Trivia)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (footerIndex: UsingFooterIndex)
        (curIdx: int)
        (limitIdx: int)
        (canUsePreCond: bool)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        let mutable bestIdx = limitIdx
        let hBase = hashUsingCommentKey lSpan a inC inC.DirSeq

        let candFalse =
            findExactFooterBucketMatch
                allowDirectiveSpanning
                lSpan
                lTriv
                rSpan
                rTriv
                inC
                origSlot
                clauseCount
                inClauseDirSeqs
                bfComments
                bfRequiresPreCond
                footerIndex
                curIdx
                bestIdx
                (mixUsingPreCondHash hBase false)
                outerSpans

        if candFalse >= 0 then
            bestIdx <- candFalse

        if canUsePreCond then
            let candTrue =
                findExactFooterBucketMatch
                    allowDirectiveSpanning
                    lSpan
                    lTriv
                    rSpan
                    rTriv
                    inC
                    origSlot
                    clauseCount
                    inClauseDirSeqs
                    bfComments
                    bfRequiresPreCond
                    footerIndex
                    curIdx
                    bestIdx
                    (mixUsingPreCondHash hBase true)
                    outerSpans

            if candTrue >= 0 then
                bestIdx <- candTrue

        if inC.IsInertIgnoreEnd && footerIndex.InertBfIdxs.Count > 0 then
            let hEffBase = hashUsingCommentKey lSpan a inC inC.EffDirSeq

            let inertFalse =
                findInertFooterBucketMatch
                    allowDirectiveSpanning
                    lSpan
                    lTriv
                    rSpan
                    rTriv
                    inC
                    origSlot
                    clauseCount
                    inClauseDirSeqs
                    bfComments
                    bfRequiresPreCond
                    footerIndex
                    curIdx
                    bestIdx
                    (mixUsingPreCondHash hEffBase false)
                    outerSpans

            if inertFalse >= 0 then
                bestIdx <- inertFalse

            if canUsePreCond then
                let inertTrue =
                    findInertFooterBucketMatch
                        allowDirectiveSpanning
                        lSpan
                        lTriv
                        rSpan
                        rTriv
                        inC
                        origSlot
                        clauseCount
                        inClauseDirSeqs
                        bfComments
                        bfRequiresPreCond
                        footerIndex
                        curIdx
                        bestIdx
                        (mixUsingPreCondHash hEffBase true)
                        outerSpans

                if inertTrue >= 0 then
                    bestIdx <- inertTrue

        if bestIdx < limitIdx then bestIdx else -1

    let private advanceUsingFooterCursor
        (allowDirectiveSpanning: bool)
        (allowMidDocBfStart: bool)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (inC: UsingRunComment)
        (origSlot: int)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (bfCount: int)
        (footerIndex: UsingFooterIndex)
        (bfIdx: int)
        (bfPos: int)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        =
        let mutable curIdx = bfIdx
        let mutable curPos = bfPos
        let a = lTriv[inC.TriviaIndex]
        let isDoc = a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
        let mutable resultIdx = -1
        let mutable resultPos = 0

        let mutable midStartIdx = curIdx
        let mutable minMidStart = 0

        if curPos > 0 && curIdx < bfCount then
            let outC = bfComments[curIdx]
            let b = rTriv[outC.TriviaIndex]
            let bFinish = b.Start + b.Length

            if
                isDoc
                && b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                && inC.Frame = outC.Frame
                && inC.Ctx = outC.Ctx
                && inC.RegionDepth = outC.RegionDepth
                && inC.DirSeq = outC.DirSeq
                && usingFooterPreCondMatches
                    bfRequiresPreCond[curIdx]
                    inC
                    origSlot
                    clauseCount
                    inClauseDirSeqs
            then
                let mutable nextPos = curPos

                if docTriviaMatchesPrefix lSpan a rSpan &nextPos bFinish then
                    if nextPos >= bFinish then
                        resultIdx <- curIdx + 1
                        resultPos <- 0
                    else
                        resultIdx <- curIdx
                        resultPos <- nextPos

            if resultIdx < 0 then
                let mutable stayInBlock = false

                if
                    allowMidDocBfStart
                    && isDoc
                    && b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                then
                    let struct (_, _, nextAfterCur) = CommentContent.lineSpan rSpan bFinish curPos

                    if nextAfterCur < bFinish then
                        stayInBlock <- true
                        midStartIdx <- curIdx
                        minMidStart <- nextAfterCur

                curIdx <- curIdx + 1
                curPos <- 0

                if not stayInBlock then
                    midStartIdx <- curIdx
                    minMidStart <- 0

        if resultIdx < 0 && midStartIdx < bfCount then
            if isNull footerIndex then
                let mutable scanIdx = midStartIdx

                while resultIdx < 0 && scanIdx < bfCount do
                    let outC = bfComments[scanIdx]

                    if
                        usingFooterPreCondMatches
                            bfRequiresPreCond[scanIdx]
                            inC
                            origSlot
                            clauseCount
                            inClauseDirSeqs
                    then
                        if
                            scanIdx >= curIdx
                            && tryMatchSingleUsingComment
                                allowDirectiveSpanning
                                lSpan
                                lTriv
                                inC
                                rSpan
                                rTriv
                                outC
                                true
                                false
                                0
                                0
                                0
                                0
                                0
                                0
                                false
                                outerSpans
                                null
                        then
                            resultIdx <- scanIdx + 1
                            resultPos <- 0
                        elif
                            isDoc
                            && rTriv[outC.TriviaIndex].Kind =
                                TriviaKind.SingleLineDocumentationCommentTrivia
                            && inC.Frame = outC.Frame
                            && inC.Ctx = outC.Ctx
                            && inC.RegionDepth = outC.RegionDepth
                            && inC.DirSeq = outC.DirSeq
                        then
                            let b = rTriv[outC.TriviaIndex]
                            let bFinish = b.Start + b.Length

                            if scanIdx < curIdx then
                                let mutable scanPos = minMidStart

                                while resultIdx < 0 && scanPos < bFinish do
                                    let mutable nextPos = scanPos

                                    if docTriviaMatchesPrefix lSpan a rSpan &nextPos bFinish then
                                        if nextPos >= bFinish then
                                            resultIdx <- scanIdx + 1
                                            resultPos <- 0
                                        else
                                            resultIdx <- scanIdx
                                            resultPos <- nextPos
                                    else
                                        let struct (_, _, pNext) =
                                            CommentContent.lineSpan rSpan bFinish scanPos

                                        scanPos <- pNext
                            else
                                let mutable nextPos = b.Start

                                if docTriviaMatchesPrefix lSpan a rSpan &nextPos bFinish then
                                    if nextPos >= bFinish then
                                        resultIdx <- scanIdx + 1
                                        resultPos <- 0
                                    else
                                        resultIdx <- scanIdx
                                        resultPos <- nextPos

                    if resultIdx < 0 then
                        scanIdx <- scanIdx + 1
            else
                let mutable bestCandIdx = bfCount
                let mutable bestNextIdx = -1
                let mutable bestNextPos = 0

                let canUsePreCond = origSlot < clauseCount && inC.DirSeq < inClauseDirSeqs[origSlot]

                if curIdx < bfCount then
                    let candExact =
                        findBestExactFooterMatch
                            allowDirectiveSpanning
                            lSpan
                            lTriv
                            rSpan
                            rTriv
                            inC
                            a
                            origSlot
                            clauseCount
                            inClauseDirSeqs
                            bfComments
                            bfRequiresPreCond
                            footerIndex
                            curIdx
                            bestCandIdx
                            canUsePreCond
                            outerSpans

                    if candExact >= 0 then
                        bestCandIdx <- candExact
                        bestNextIdx <- candExact + 1
                        bestNextPos <- 0

                if isDoc && bfCount > 0 then
                    let struct (docLineCount, fullPoly) = evalUsingDocPoly lSpan a

                    if curIdx < bestCandIdx then
                        scanDocLineBucketPair
                            lSpan
                            rSpan
                            rTriv
                            inC
                            a
                            origSlot
                            clauseCount
                            inClauseDirSeqs
                            bfComments
                            bfRequiresPreCond
                            curIdx
                            0
                            canUsePreCond
                            fullPoly
                            docLineCount
                            &bestCandIdx
                            &bestNextIdx
                            &bestNextPos
                            footerIndex.DocPrefixHashes
                            footerIndex.DocPrefixBfIdxs
                            null
                            footerIndex.DocPrefixBucketMask
                            footerIndex.DocPrefixBucketOffsets
                            footerIndex.DocPrefixBucketItems

                    if allowMidDocBfStart && midStartIdx < bfCount then
                        if docLineCount = 1 then
                            scanDocLineBucketPair
                                lSpan
                                rSpan
                                rTriv
                                inC
                                a
                                origSlot
                                clauseCount
                                inClauseDirSeqs
                                bfComments
                                bfRequiresPreCond
                                midStartIdx
                                minMidStart
                                canUsePreCond
                                fullPoly
                                1
                                &bestCandIdx
                                &bestNextIdx
                                &bestNextPos
                                footerIndex.DocMidHashes
                                footerIndex.DocMidBfIdxs
                                footerIndex.DocMidStarts
                                footerIndex.DocMidBucketMask
                                footerIndex.DocMidBucketOffsets
                                footerIndex.DocMidBucketItems
                        elif docLineCount < footerIndex.MaxBfDocLines then
                            if footerIndex.IndexedMidLens.Contains docLineCount then
                                scanDocLineBucketPair
                                    lSpan
                                    rSpan
                                    rTriv
                                    inC
                                    a
                                    origSlot
                                    clauseCount
                                    inClauseDirSeqs
                                    bfComments
                                    bfRequiresPreCond
                                    midStartIdx
                                    minMidStart
                                    canUsePreCond
                                    fullPoly
                                    docLineCount
                                    &bestCandIdx
                                    &bestNextIdx
                                    &bestNextPos
                                    footerIndex.DocMidMultiHashes
                                    footerIndex.DocMidMultiBfIdxs
                                    footerIndex.DocMidMultiStarts
                                    footerIndex.DocMidMultiBucketMask
                                    footerIndex.DocMidMultiBucketOffsets
                                    footerIndex.DocMidMultiBucketItems
                            else
                                scanEvictedMidDocFallback
                                    lSpan
                                    rSpan
                                    rTriv
                                    inC
                                    a
                                    docLineCount
                                    fullPoly
                                    origSlot
                                    clauseCount
                                    inClauseDirSeqs
                                    bfComments
                                    bfRequiresPreCond
                                    footerIndex
                                    midStartIdx
                                    minMidStart
                                    canUsePreCond
                                    &bestCandIdx
                                    &bestNextIdx
                                    &bestNextPos

                if
                    curIdx < bfCount
                    && allowDirectiveSpanning
                    && (a.Kind = TriviaKind.MultiLineCommentTrivia
                        || a.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                    && footerIndex.SpanningBfIndices.Count > 0
                    && hasConditionalDirectiveSpanningLine (lSpan.Slice(a.Start, a.Length))
                then
                    let mutable si = lowerBoundResize footerIndex.SpanningBfIndices curIdx

                    while si < footerIndex.SpanningBfIndices.Count do
                        let candIdx = footerIndex.SpanningBfIndices[si]

                        if candIdx >= bestCandIdx then
                            si <- footerIndex.SpanningBfIndices.Count
                        elif
                            usingFooterPreCondMatches
                                bfRequiresPreCond[candIdx]
                                inC
                                origSlot
                                clauseCount
                                inClauseDirSeqs
                            && tryMatchSingleUsingComment
                                allowDirectiveSpanning
                                lSpan
                                lTriv
                                inC
                                rSpan
                                rTriv
                                bfComments[candIdx]
                                true
                                false
                                0
                                0
                                0
                                0
                                0
                                0
                                false
                                outerSpans
                                null
                        then
                            bestCandIdx <- candIdx
                            bestNextIdx <- candIdx + 1
                            bestNextPos <- 0
                            si <- footerIndex.SpanningBfIndices.Count
                        else
                            si <- si + 1

                resultIdx <- bestNextIdx
                resultPos <- bestNextPos

        struct (resultIdx, resultPos)

    let private advanceFooterOverMergedGaps
        (allowDirectiveSpanning: bool)
        (allowMidDocBfStart: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (gapStart: int)
        (gapEndExclusive: int)
        (mergedScratch: ResizeArray<int>)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (bfCount: int)
        (footerIndex: UsingFooterIndex)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (rawOrigSlots: int array)
        (orderedToRaw: int array)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        (bfIdx: int)
        (bfPos: int)
        =
        let mutable ok = true
        let mutable curIdx = bfIdx
        let mutable curPos = bfPos
        let mutable mi = 0
        let mutable g = gapStart

        while ok && g < gapEndExclusive do
            while mi < mergedScratch.Count && mergedScratch[mi] < g do
                mi <- mi + 1

            if mi < mergedScratch.Count && mergedScratch[mi] = g then
                mi <- mi + 1
            elif not (isNull bfComments) then
                let origS = rawOrigSlots[orderedToRaw[g]]

                let struct (nIdx, nPos) =
                    advanceUsingFooterCursor
                        allowDirectiveSpanning
                        allowMidDocBfStart
                        lSpan
                        lTriv
                        rSpan
                        rTriv
                        inComments[g]
                        origS
                        clauseCount
                        inClauseDirSeqs
                        bfComments
                        bfRequiresPreCond
                        bfCount
                        footerIndex
                        curIdx
                        curPos
                        outerSpans

                if nIdx < 0 then
                    ok <- false
                else
                    curIdx <- nIdx
                    curPos <- nPos

            g <- g + 1

        struct (ok, curIdx, curPos)

    let private tryMatchUsingStream2WithSkips
        (allowDirectiveSpanning: bool)
        (allowMidDocBfStart: bool)
        (isResume: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (outComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outE: int)
        (in2E: int)
        (canGoFooter: bool array)
        (inConsumed: bool array)
        (useRelativeRegion: bool)
        (inClauseFrame: int)
        (inClauseRegionDepth: int)
        (inClauseRegionSeq: int)
        (outClauseFrame: int)
        (outClauseRegionDepth: int)
        (outClauseRegionSeq: int)
        (inIsFloating: bool array)
        (inSameRunEnd: int array)
        (outSameRunEnd: int array)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        (pendingRawSpans: ResizeArray<struct (int * int * int * int)>)
        (consumedIndices: ResizeArray<int>)
        (matchedRanges: ResizeArray<struct (int * int)>)
        (mergedScratch: ResizeArray<int>)
        (failedNoSkipMemo: HashSet<struct (int * int)>)
        (failedMemo3: HashSet<struct (int * int * uint64)>)
        (frameStack: ResizeArray<struct (int * int * int * int * int)>)
        (bfStack: ResizeArray<struct (int * int)>)
        (noSkipVisited: ResizeArray<int>)
        (sharedDocFailed: HashSet<struct (int * int * int * int)>)
        (docLinesScratch: ResizeArray<int>)
        (docSuffixScratch: ResizeArray<int>)
        (bfComments: ResizeArray<UsingRunComment>)
        (bfRequiresPreCond: ResizeArray<bool>)
        (bfCount: int)
        (footerIndex: UsingFooterIndex)
        (bfRemainingMaxIn: int array)
        (outMaxInPrefix: int array)
        (clauseCount: int)
        (inClauseDirSeqs: int array)
        (rawOrigSlots: int array)
        (orderedToRaw: int array)
        (oi: int)
        (cur2: int)
        (bfStartIdx: int)
        (bfStartPos: int)
        (bfEndIdxOut: outref<int>)
        (bfEndPosOut: outref<int>)
        : bool =
        let mutable curOi = oi
        let mutable curIn = cur2
        let mutable curBfIdx = bfStartIdx
        let mutable curBfPos = bfStartPos
        let mutable resumingStart = isResume

        if not isResume then
            frameStack.Clear()
            bfStack.Clear()
            matchedRanges.Clear()

        let mutable stepping = true
        let mutable result = false

        while stepping do
            let mutable needBacktrack = false

            if resumingStart then
                resumingStart <- false
                needBacktrack <- true
            else
                let remOut = outE - curOi + 1

                if remOut <= 0 then
                    let mutable restOk = true
                    let mutable k = curIn
                    let mutable remBfIdx = curBfIdx
                    let mutable remBfPos = curBfPos

                    while restOk && k <= in2E do
                        if not canGoFooter[k] then
                            restOk <- false
                        elif not (isNull bfComments) then
                            let origS = rawOrigSlots[orderedToRaw[k]]

                            let struct (nIdx, nPos) =
                                advanceUsingFooterCursor
                                    allowDirectiveSpanning
                                    allowMidDocBfStart
                                    lSpan
                                    lTriv
                                    rSpan
                                    rTriv
                                    inComments[k]
                                    origS
                                    clauseCount
                                    inClauseDirSeqs
                                    bfComments
                                    bfRequiresPreCond
                                    bfCount
                                    footerIndex
                                    remBfIdx
                                    remBfPos
                                    outerSpans

                            if nIdx < 0 then
                                restOk <- false
                            else
                                remBfIdx <- nIdx
                                remBfPos <- nPos

                        k <- k + 1

                    if restOk then
                        bfEndIdxOut <- remBfIdx
                        bfEndPosOut <- remBfPos
                        result <- true
                        stepping <- false
                    else
                        needBacktrack <- true
                else
                    let remIn = in2E - curIn + 1

                    if remIn < remOut then
                        needBacktrack <- true
                    else
                        let key = struct (curOi, curIn, packUsingBfKey curBfIdx curBfPos)

                        if failedMemo3.Contains key then
                            needBacktrack <- true
                        elif remIn = remOut then
                            let savedConsumed = consumedIndices.Count

                            let savedRaw =
                                if isNull pendingRawSpans then 0 else pendingRawSpans.Count

                            if
                                tryMatchUsingStream2NoSkip
                                    allowDirectiveSpanning
                                    inComments
                                    outComments
                                    lSpan
                                    lTriv
                                    rSpan
                                    rTriv
                                    curOi
                                    outE
                                    curIn
                                    in2E
                                    inConsumed
                                    useRelativeRegion
                                    inClauseFrame
                                    inClauseRegionDepth
                                    inClauseRegionSeq
                                    outClauseFrame
                                    outClauseRegionDepth
                                    outClauseRegionSeq
                                    inIsFloating
                                    outerSpans
                                    pendingRawSpans
                                    consumedIndices
                                    failedNoSkipMemo
                                    noSkipVisited
                            then
                                bfEndIdxOut <- curBfIdx
                                bfEndPosOut <- curBfPos
                                result <- true
                                stepping <- false
                            else
                                if consumedIndices.Count > savedConsumed then
                                    consumedIndices.RemoveRange(
                                        savedConsumed,
                                        consumedIndices.Count - savedConsumed
                                    )

                                if
                                    not (isNull pendingRawSpans) && pendingRawSpans.Count > savedRaw
                                then
                                    pendingRawSpans.RemoveRange(
                                        savedRaw,
                                        pendingRawSpans.Count - savedRaw
                                    )

                                failedMemo3.Add key |> ignore
                                needBacktrack <- true
                        else
                            let mutable tryConsume = true
                            let mutable skipNextBfIdx = -1
                            let mutable skipNextBfPos = 0

                            if canGoFooter[curIn] then
                                if isNull bfComments then
                                    tryConsume <- false
                                else
                                    let origS = rawOrigSlots[orderedToRaw[curIn]]

                                    let struct (nIdx, nPos) =
                                        advanceUsingFooterCursor
                                            allowDirectiveSpanning
                                            allowMidDocBfStart
                                            lSpan
                                            lTriv
                                            rSpan
                                            rTriv
                                            inComments[curIn]
                                            origS
                                            clauseCount
                                            inClauseDirSeqs
                                            bfComments
                                            bfRequiresPreCond
                                            bfCount
                                            footerIndex
                                            curBfIdx
                                            curBfPos
                                            outerSpans

                                    let remCap = if nIdx >= 0 then bfRemainingMaxIn[nIdx] else -1

                                    let remOutMax = outMaxInPrefix[outE + 1] - outMaxInPrefix[curOi]

                                    let minSkipsNeeded = (in2E - curIn) - remOutMax

                                    if nIdx >= 0 && remCap >= minSkipsNeeded then
                                        skipNextBfIdx <- nIdx
                                        skipNextBfPos <- nPos
                                        tryConsume <- false

                            if not tryConsume then
                                let savedMatched = matchedRanges.Count

                                let savedRaw =
                                    if isNull pendingRawSpans then 0 else pendingRawSpans.Count

                                frameStack.Add(struct (curOi, curIn, savedMatched, savedRaw, 0))
                                bfStack.Add(struct (curBfIdx, curBfPos))
                                curIn <- curIn + 1

                                if not (isNull bfComments) then
                                    curBfIdx <- skipNextBfIdx
                                    curBfPos <- skipNextBfPos
                            else
                                let savedMatched = matchedRanges.Count

                                let savedRaw =
                                    if isNull pendingRawSpans then 0 else pendingRawSpans.Count

                                mergedScratch.Clear()

                                let struct (rawItemOk, _, _, next2) =
                                    tryMatchUsingOneItem
                                        allowDirectiveSpanning
                                        inComments
                                        lSpan
                                        lTriv
                                        rSpan
                                        rTriv
                                        outComments[curOi]
                                        false
                                        -1
                                        false
                                        in2E
                                        false
                                        inConsumed
                                        canGoFooter
                                        true
                                        true
                                        (outE - curOi)
                                        useRelativeRegion
                                        inClauseFrame
                                        inClauseRegionDepth
                                        inClauseRegionSeq
                                        outClauseFrame
                                        outClauseRegionDepth
                                        outClauseRegionSeq
                                        inIsFloating
                                        rawOrigSlots
                                        orderedToRaw
                                        curOi
                                        false
                                        0
                                        curIn
                                        outerSpans
                                        pendingRawSpans
                                        mergedScratch
                                        sharedDocFailed
                                        docLinesScratch
                                        docSuffixScratch

                                let mutable itemOk = rawItemOk
                                let mutable newBfIdx = curBfIdx
                                let mutable newBfPos = curBfPos

                                if itemOk && next2 - curIn > mergedScratch.Count then
                                    let struct (gapsOk, gapBfIdx, gapBfPos) =
                                        advanceFooterOverMergedGaps
                                            allowDirectiveSpanning
                                            allowMidDocBfStart
                                            inComments
                                            lSpan
                                            lTriv
                                            rSpan
                                            rTriv
                                            curIn
                                            next2
                                            mergedScratch
                                            bfComments
                                            bfRequiresPreCond
                                            bfCount
                                            footerIndex
                                            clauseCount
                                            inClauseDirSeqs
                                            rawOrigSlots
                                            orderedToRaw
                                            outerSpans
                                            curBfIdx
                                            curBfPos

                                    itemOk <- gapsOk
                                    newBfIdx <- gapBfIdx
                                    newBfPos <- gapBfPos

                                if itemOk then
                                    for mi = 0 to mergedScratch.Count - 1 do
                                        matchedRanges.Add(struct (mergedScratch[mi], 1))

                                    if frameStack.Count > 0 then
                                        frameStack.Add(
                                            struct (curOi, curIn, savedMatched, savedRaw, 1)
                                        )

                                        bfStack.Add(struct (curBfIdx, curBfPos))

                                    curOi <- curOi + 1
                                    curIn <- next2
                                    curBfIdx <- newBfIdx
                                    curBfPos <- newBfPos
                                else
                                    if matchedRanges.Count > savedMatched then
                                        matchedRanges.RemoveRange(
                                            savedMatched,
                                            matchedRanges.Count - savedMatched
                                        )

                                    if
                                        not (isNull pendingRawSpans)
                                        && pendingRawSpans.Count > savedRaw
                                    then
                                        pendingRawSpans.RemoveRange(
                                            savedRaw,
                                            pendingRawSpans.Count - savedRaw
                                        )

                                    failedMemo3.Add key |> ignore
                                    needBacktrack <- true

            if needBacktrack then
                let mutable resumed = false

                while not resumed && frameStack.Count > 0 do
                    let topIdx = frameStack.Count - 1
                    let struct (fOi, fCur2, fSavedMatched, fSavedRaw, fMode) = frameStack[topIdx]
                    let struct (fBfIdx, fBfPos) = bfStack[topIdx]
                    frameStack.RemoveAt topIdx
                    bfStack.RemoveAt topIdx

                    if matchedRanges.Count > fSavedMatched then
                        matchedRanges.RemoveRange(
                            fSavedMatched,
                            matchedRanges.Count - fSavedMatched
                        )

                    if not (isNull pendingRawSpans) && pendingRawSpans.Count > fSavedRaw then
                        pendingRawSpans.RemoveRange(fSavedRaw, pendingRawSpans.Count - fSavedRaw)

                    let fKey = struct (fOi, fCur2, packUsingBfKey fBfIdx fBfPos)

                    if fMode = 0 then
                        let runEnd =
                            if not (isNull inSameRunEnd) then
                                min in2E inSameRunEnd[fCur2]
                            else
                                fCur2

                        if runEnd > fCur2 then
                            let runLen = runEnd - fCur2 + 1
                            let isFloating = not (isNull inIsFloating) && inIsFloating[fCur2]

                            if
                                fOi + runLen - 1 <= outE
                                && not (isNull outSameRunEnd)
                                && outSameRunEnd[fOi] >= fOi + runLen - 1
                                && tryMatchSingleUsingComment
                                    allowDirectiveSpanning
                                    lSpan
                                    lTriv
                                    inComments[fCur2]
                                    rSpan
                                    rTriv
                                    outComments[fOi]
                                    false
                                    useRelativeRegion
                                    inClauseFrame
                                    inClauseRegionDepth
                                    inClauseRegionSeq
                                    outClauseFrame
                                    outClauseRegionDepth
                                    outClauseRegionSeq
                                    isFloating
                                    outerSpans
                                    pendingRawSpans
                            then
                                matchedRanges.Add(struct (fCur2, runLen))
                                frameStack.Add(struct (fOi, fCur2, fSavedMatched, fSavedRaw, 1))
                                bfStack.Add(struct (fBfIdx, fBfPos))
                                curOi <- fOi + runLen
                                curIn <- runEnd + 1
                                curBfIdx <- fBfIdx
                                curBfPos <- fBfPos
                                resumed <- true
                            else
                                failedMemo3.Add fKey |> ignore
                        else
                            mergedScratch.Clear()

                            let struct (rawItemOk, _, _, next2) =
                                tryMatchUsingOneItem
                                    allowDirectiveSpanning
                                    inComments
                                    lSpan
                                    lTriv
                                    rSpan
                                    rTriv
                                    outComments[fOi]
                                    false
                                    -1
                                    false
                                    in2E
                                    false
                                    inConsumed
                                    canGoFooter
                                    true
                                    true
                                    (outE - fOi)
                                    useRelativeRegion
                                    inClauseFrame
                                    inClauseRegionDepth
                                    inClauseRegionSeq
                                    outClauseFrame
                                    outClauseRegionDepth
                                    outClauseRegionSeq
                                    inIsFloating
                                    rawOrigSlots
                                    orderedToRaw
                                    fOi
                                    false
                                    0
                                    fCur2
                                    outerSpans
                                    pendingRawSpans
                                    mergedScratch
                                    sharedDocFailed
                                    docLinesScratch
                                    docSuffixScratch

                            let mutable itemOk = rawItemOk
                            let mutable newBfIdx = fBfIdx
                            let mutable newBfPos = fBfPos

                            if itemOk && next2 - fCur2 > mergedScratch.Count then
                                let struct (gapsOk, gapBfIdx, gapBfPos) =
                                    advanceFooterOverMergedGaps
                                        allowDirectiveSpanning
                                        allowMidDocBfStart
                                        inComments
                                        lSpan
                                        lTriv
                                        rSpan
                                        rTriv
                                        fCur2
                                        next2
                                        mergedScratch
                                        bfComments
                                        bfRequiresPreCond
                                        bfCount
                                        footerIndex
                                        clauseCount
                                        inClauseDirSeqs
                                        rawOrigSlots
                                        orderedToRaw
                                        outerSpans
                                        fBfIdx
                                        fBfPos

                                itemOk <- gapsOk
                                newBfIdx <- gapBfIdx
                                newBfPos <- gapBfPos

                            if itemOk then
                                for mi = 0 to mergedScratch.Count - 1 do
                                    matchedRanges.Add(struct (mergedScratch[mi], 1))

                                frameStack.Add(struct (fOi, fCur2, fSavedMatched, fSavedRaw, 1))
                                bfStack.Add(struct (fBfIdx, fBfPos))
                                curOi <- fOi + 1
                                curIn <- next2
                                curBfIdx <- newBfIdx
                                curBfPos <- newBfPos
                                resumed <- true
                            else
                                if matchedRanges.Count > fSavedMatched then
                                    matchedRanges.RemoveRange(
                                        fSavedMatched,
                                        matchedRanges.Count - fSavedMatched
                                    )

                                if
                                    not (isNull pendingRawSpans)
                                    && pendingRawSpans.Count > fSavedRaw
                                then
                                    pendingRawSpans.RemoveRange(
                                        fSavedRaw,
                                        pendingRawSpans.Count - fSavedRaw
                                    )

                                failedMemo3.Add fKey |> ignore
                    else
                        failedMemo3.Add fKey |> ignore

                if not resumed then
                    stepping <- false

        if result then
            for mi = 0 to matchedRanges.Count - 1 do
                let struct (startIn, len) = matchedRanges[mi]

                for d = 0 to len - 1 do
                    consumedIndices.Add(startIn + d)

        result

    let private tryMatchUsingFooterComments
        (allowDirectiveSpanning: bool)
        (inComments: ResizeArray<UsingRunComment>)
        (outComments: ResizeArray<UsingRunComment>)
        (lSpan: ReadOnlySpan<char>)
        (lTriv: ReadOnlySpan<Trivia>)
        (rSpan: ReadOnlySpan<char>)
        (rTriv: ReadOnlySpan<Trivia>)
        (outS: int)
        (outE: int)
        (inConsumed: bool array)
        (bfRequiresPreCond: ResizeArray<bool>)
        (clauseCount: int)
        (boundaryCount: int)
        (inClauseDirSeqs: int array)
        (rawOrigSlots: int array)
        (outerSpans: ResizeArray<struct (int * int * int * int)>)
        (pendingRawSpans: ResizeArray<struct (int * int * int * int)>)
        (scratchConsumed: ResizeArray<int>)
        =
        scratchConsumed.Clear()
        let mutable oi = outS
        let mutable ii = 0
        let inEnd = inComments.Count - 1
        let mutable ok = true

        while ok && oi <= outE do
            while ii <= inEnd && inConsumed[ii] do
                ii <- ii + 1

            if ii > inEnd then
                ok <- false
            else
                let savedScratch = scratchConsumed.Count
                let outC = outComments[oi]

                let disallowUsingDocMerge =
                    oi >= boundaryCount
                    && rTriv[outC.TriviaIndex].Kind =
                        TriviaKind.SingleLineDocumentationCommentTrivia

                let mutable singleMatched = false

                if
                    disallowUsingDocMerge
                    && tryMatchSingleUsingComment
                        allowDirectiveSpanning
                        lSpan
                        lTriv
                        inComments[ii]
                        rSpan
                        rTriv
                        outC
                        true
                        false
                        0
                        0
                        0
                        0
                        0
                        0
                        false
                        outerSpans
                        pendingRawSpans
                then
                    scratchConsumed.Add ii
                    singleMatched <- true

                let struct (matched, _, _, next2) =
                    if singleMatched then
                        struct (true, false, 0, ii + 1)
                    else
                        tryMatchUsingOneItem
                            allowDirectiveSpanning
                            inComments
                            lSpan
                            lTriv
                            rSpan
                            rTriv
                            outC
                            true
                            -1
                            false
                            inEnd
                            true
                            inConsumed
                            null
                            false
                            false
                            0
                            false
                            0
                            0
                            0
                            0
                            0
                            0
                            null
                            rawOrigSlots
                            null
                            -1
                            false
                            0
                            ii
                            outerSpans
                            pendingRawSpans
                            scratchConsumed
                            null
                            null
                            null

                if not matched then
                    ok <- false
                else
                    if disallowUsingDocMerge && not singleMatched then
                        let mutable hasUsingOrig = false
                        let mutable hasFooterOrig = false
                        let mutable di = savedScratch

                        while di < scratchConsumed.Count do
                            if rawOrigSlots[scratchConsumed[di]] < clauseCount then
                                hasUsingOrig <- true
                            else
                                hasFooterOrig <- true

                            di <- di + 1

                        if hasUsingOrig && hasFooterOrig then
                            ok <- false

                    if ok && not (isNull bfRequiresPreCond) && bfRequiresPreCond[oi] then
                        let mutable si = savedScratch

                        while ok && si < scratchConsumed.Count do
                            let rawIdx = scratchConsumed[si]

                            if
                                not (
                                    usingFooterPreCondMatches
                                        true
                                        inComments[rawIdx]
                                        rawOrigSlots[rawIdx]
                                        clauseCount
                                        inClauseDirSeqs
                                )
                            then
                                ok <- false

                            si <- si + 1

                    oi <- oi + 1
                    ii <- next2

        if ok then
            while ii <= inEnd && inConsumed[ii] do
                ii <- ii + 1

            ii > inEnd
        else
            false

    [<Sealed>]
    type private UsingPlacementCursor() =
        let stack = ResizeArray<struct (int * int)>()
        let mutable buffer = Unchecked.defaultof<TokenBuffer>
        let mutable version = -1
        let mutable tokenCount = -1
        let mutable triviaCount = -1
        let mutable lastFirstIdx = -1
        let mutable tokPos = 0
        let mutable suspendedOnTok = false
        let mutable ti = 0
        let mutable curFrame = -1
        let mutable curCtx = 0
        let mutable nextFrame = 0
        let mutable braceDepth = 0
        let mutable inIgnoreBlock = false
        let mutable ignoreScopeDepth = -1
        let mutable ignoreOpenedOnUsing = false
        let mutable inUsingClause = false
        let mutable clauseSingleIgnore = false
        let mutable clauseSuppressedStart = false

        member _.Reset() =
            buffer <- Unchecked.defaultof<TokenBuffer>
            version <- -1
            tokenCount <- -1
            triviaCount <- -1
            lastFirstIdx <- -1
            tokPos <- 0
            suspendedOnTok <- false
            ti <- 0
            curFrame <- -1
            curCtx <- 0
            nextFrame <- 0
            braceDepth <- 0
            inIgnoreBlock <- false
            ignoreScopeDepth <- -1
            ignoreOpenedOnUsing <- false
            inUsingClause <- false
            clauseSingleIgnore <- false
            clauseSuppressedStart <- false
            stack.Clear()

        member private _.ProcessTriviaRange
            (
                triv: ReadOnlySpan<Trivia>,
                span: ReadOnlySpan<char>,
                contentLim: int,
                lo: int,
                hi: int,
                isTokLeading: bool,
                tokenIdx: int,
                isNamespaceKw: bool,
                canUsingHead: bool,
                isClauseToken: bool
            ) =
            let stop = min contentLim hi
            let mutable j = max ti lo
            let mutable sawMarker = false

            while j < stop do
                let item = triv[j]
                let kind = item.Kind

                if kind > TriviaKind.WhitespaceTrivia then
                    if kind <= TriviaKind.MultiLineDocumentationCommentTrivia then
                        let ignKind = ignoreCommentKind span item

                        if ignKind > 0 then
                            let suppressed =
                                isTokLeading
                                && sawMarker
                                && ((ignKind = 2 && (braceDepth = 0 || isNamespaceKw))
                                    || (ignKind = 3
                                        && tokenIdx > 0
                                        && braceDepth > 0
                                        && not isNamespaceKw))

                            if isTokLeading then
                                sawMarker <- true

                            if not suppressed then
                                if ignKind = 2 then
                                    if not inIgnoreBlock then
                                        inIgnoreBlock <- true
                                        ignoreScopeDepth <- braceDepth
                                        ignoreOpenedOnUsing <- canUsingHead
                                elif ignKind = 3 then
                                    if inIgnoreBlock && braceDepth <= ignoreScopeDepth then
                                        inIgnoreBlock <- false
                                        ignoreScopeDepth <- -1
                                        ignoreOpenedOnUsing <- false
                                elif ignKind = 1 && isTokLeading && isClauseToken then
                                    clauseSingleIgnore <- true
                            elif ignKind = 2 && isClauseToken && not inIgnoreBlock then
                                clauseSuppressedStart <- true
                    elif kind = TriviaKind.IfDirectiveTrivia then
                        stack.Add(struct (curFrame, curCtx))
                        curFrame <- nextFrame
                        nextFrame <- nextFrame + 1
                        curCtx <- 0
                    elif
                        kind = TriviaKind.ElifDirectiveTrivia
                        || kind = TriviaKind.ElseDirectiveTrivia
                    then
                        curFrame <- nextFrame
                        nextFrame <- nextFrame + 1
                        curCtx <- 0
                    elif kind = TriviaKind.EndIfDirectiveTrivia then
                        if stack.Count > 0 then
                            let last = stack.Count - 1
                            let struct (pf, pc) = stack[last]
                            stack.RemoveAt last
                            curFrame <- pf
                            curCtx <- pc
                        else
                            curFrame <- -1
                            curCtx <- 0
                    elif contextDirective kind then
                        curCtx <- curCtx + 1

                j <- j + 1

            if hi > ti then
                ti <- hi

        member private this.AdvanceLeading
            (
                tokens: ReadOnlySpan<Token>,
                triv: ReadOnlySpan<Trivia>,
                span: ReadOnlySpan<char>,
                contentLim: int,
                k: int,
                isClauseToken: bool
            ) =
            let t = tokens[k]
            let isNs = t.Kind = TokenKind.NamespaceKeyword
            let canUsing = isUsingDirectiveHeadToken tokens span k

            if
                inIgnoreBlock
                && ignoreOpenedOnUsing
                && not inUsingClause
                && not canUsing
                && t.Kind <> TokenKind.ExternKeyword
                && braceDepth = ignoreScopeDepth
            then
                if
                    not (
                        hasClosingIgnoreEndInScope
                            tokens
                            triv
                            span
                            contentLim
                            k
                            braceDepth
                            ignoreScopeDepth
                    )
                then
                    inIgnoreBlock <- false
                    ignoreScopeDepth <- -1

                ignoreOpenedOnUsing <- false

            this.ProcessTriviaRange(
                triv,
                span,
                contentLim,
                t.TriviaStart,
                t.TriviaStart + t.LeadingCount,
                true,
                k,
                isNs,
                canUsing,
                isClauseToken
            )

            if canUsing then
                inUsingClause <- true

        member private this.FinishToken
            (
                tokens: ReadOnlySpan<Token>,
                triv: ReadOnlySpan<Trivia>,
                span: ReadOnlySpan<char>,
                contentLim: int,
                k: int
            ) =
            let t = tokens[k]

            if t.Kind = TokenKind.OpenBraceToken then
                braceDepth <- braceDepth + 1
            elif t.Kind = TokenKind.CloseBraceToken then
                braceDepth <- max 0 (braceDepth - 1)

                if inIgnoreBlock && braceDepth < ignoreScopeDepth then
                    inIgnoreBlock <- false
                    ignoreScopeDepth <- -1
                    ignoreOpenedOnUsing <- false
            elif t.Kind = TokenKind.SemicolonToken then
                inUsingClause <- false

            let trailStart = t.TriviaStart + t.LeadingCount

            this.ProcessTriviaRange(
                triv,
                span,
                contentLim,
                trailStart,
                trailStart + t.TrailingCount,
                false,
                k,
                false,
                false,
                false
            )

        member this.Fill
            (
                buf: TokenBuffer,
                span: ReadOnlySpan<char>,
                useInLengths: bool,
                i0: int,
                inUsingLengths: int array,
                childSlots: int array,
                count: int,
                framesOut: int array,
                ctxOut: int array,
                ignsOut: int array
            ) =
            let first0 = if useInLengths then i0 else childSlots[0]

            if
                not (Object.ReferenceEquals(buffer, buf))
                || version <> buf.Version
                || tokenCount <> buf.TokenCount
                || triviaCount <> buf.TriviaCount
                || first0 <= lastFirstIdx
            then
                this.Reset()
                buffer <- buf
                version <- buf.Version
                tokenCount <- buf.TokenCount
                triviaCount <- buf.TriviaCount

            let tokens = buf.TokenSpan()
            let triv = buf.TriviaSpan()

            let contentLim =
                min triv.Length ((max buf.LastNonCommentTrivia buf.LastCommentTrivia) + 1)

            let mutable tokCursor = i0

            for s = 0 to count - 1 do
                let firstIdx = if useInLengths then tokCursor else childSlots[s]
                clauseSingleIgnore <- false
                clauseSuppressedStart <- false

                if suspendedOnTok then
                    this.FinishToken(tokens, triv, span, contentLim, tokPos)
                    tokPos <- tokPos + 1
                    suspendedOnTok <- false

                while tokPos < firstIdx do
                    this.AdvanceLeading(tokens, triv, span, contentLim, tokPos, false)
                    this.FinishToken(tokens, triv, span, contentLim, tokPos)
                    tokPos <- tokPos + 1

                this.AdvanceLeading(tokens, triv, span, contentLim, firstIdx, true)
                tokPos <- firstIdx
                suspendedOnTok <- true

                framesOut[s] <- curFrame
                ctxOut[s] <- curCtx

                ignsOut[s] <-
                    if clauseSingleIgnore then
                        1
                    elif inIgnoreBlock then
                        2
                    elif clauseSuppressedStart && (s > 0 || braceDepth > 0) then
                        3
                    else
                        0

                lastFirstIdx <- firstIdx

                if useInLengths then
                    tokCursor <- tokCursor + inUsingLengths[s]

    let private directiveOrder =
        Comparer<Trivia>.Create(fun left right -> compare left.Start right.Start)

    type Checker(?sharedAfter: SyntaxTree, ?sharedOwnedBefore: SyntaxTree) =
        let ownsBefore = sharedOwnedBefore.IsNone

        let ownedBefore =
            match sharedOwnedBefore with
            | Some tree -> tree
            | None -> SyntaxTree()

        let mutable separatorClosings = Dictionary<int, struct (int * bool * bool)>()
        let mutable before = ownedBefore
        let mutable beforeBuilt = true
        let mutable tokScopeLexId = -1
        let mutable tokScopePos = 0
        let mutable tokScopeCanUse = true
        let mutable tokScopeCurIsNs = true
        let mutable tokScopeValid = true
        let tokScopeStack = ResizeArray<bool>()
        let ownsAfter = sharedAfter.IsNone

        let after =
            match sharedAfter with
            | Some tree -> tree
            | None -> SyntaxTree()

        let mutable afterLexedFor: string = null
        let mutable beforeLexedFor: string = null
        let mutable beforeLexedSymbols: string array = Array.empty
        let mutable afterLexedSymbols: string array = Array.empty
        let mutable lexedTexts = 0
        let mutable builtTrees = 0

        let parseText (text: string) (tree: SyntaxTree) =
            lexedTexts <- lexedTexts + 1
            builtTrees <- builtTrees + 1
            Parser.parse text tree

        let parseTextWith (symbols: string array) (text: string) (tree: SyntaxTree) =
            lexedTexts <- lexedTexts + 1
            builtTrees <- builtTrees + 1
            Parser.parseWith symbols text tree

        let parseTextWithHinted
            (symbols: string array)
            (tokenHint: int)
            (triviaHint: int)
            (text: string)
            (tree: SyntaxTree)
            =
            lexedTexts <- lexedTexts + 1
            builtTrees <- builtTrees + 1
            Parser.parseWithHinted symbols tokenHint triviaHint text tree

        let lexText (text: string) (tree: SyntaxTree) =
            lexedTexts <- lexedTexts + 1
            Parser.lexOnly text tree

        let lexTextHinted (tokenHint: int) (triviaHint: int) (text: string) (tree: SyntaxTree) =
            lexedTexts <- lexedTexts + 1
            Parser.lexOnlyHinted tokenHint triviaHint text tree

        let lexTextWith (symbols: string array) (text: string) (tree: SyntaxTree) =
            lexedTexts <- lexedTexts + 1
            Parser.lexOnlyWith symbols text tree

        let lexTextWithHinted
            (symbols: string array)
            (tokenHint: int)
            (triviaHint: int)
            (text: string)
            (tree: SyntaxTree)
            =
            lexedTexts <- lexedTexts + 1
            Parser.lexOnlyWithHinted symbols tokenHint triviaHint text tree

        let buildFromLexed (text: string) (tree: SyntaxTree) =
            if tree.LexerBuffer.IsVerifyOnly then
                let tokHint = tree.LexerBuffer.TokenCount + 32
                let trivHint = (tree.LexerBuffer.TokenCount <<< 1) + 64
                Parser.lexOnlyHinted tokHint trivHint text tree

            builtTrees <- builtTrees + 1
            Parser.parseFromLexed text tree

        let mutable allowDisabledDeferral = false
        let mutable disabledDeferralPrefix = 0

        let deferredDisabledSpanComparer =
            { new IEqualityComparer<struct (string * int * int * int * int * int)> with
                member _.Equals(struct (s1, p1, a1, b1, c1, d1), struct (s2, p2, a2, b2, c2, d2)) =
                    obj.ReferenceEquals(s1, s2)
                    && p1 = p2
                    && a1 = a2
                    && b1 = b2
                    && c1 = c2
                    && d1 = d2

                member _.GetHashCode(struct (s, p, a, b, c, d)) =
                    HashCode.Combine(
                        System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode s,
                        p,
                        a,
                        b,
                        c,
                        d
                    )
            }

        let deferredDisabledSpans =
            ResizeArray<struct (string * int * int * int * int * int)>()

        let deferredDisabledSpanSet =
            HashSet<struct (string * int * int * int * int * int)>(deferredDisabledSpanComparer)

        let mutable deferredCanonicalBase: string = null

        let mutable lastSafeText0: string = null
        let mutable lastSafePrefix0 = -1
        let mutable lastSafeOk0 = false
        let mutable lastSafeText1: string = null
        let mutable lastSafePrefix1 = -1
        let mutable lastSafeOk1 = false

        let recordSafeChecked (text: string) (prefixLen: int) (ok: bool) =
            if not (Object.ReferenceEquals(text, lastSafeText0) && prefixLen = lastSafePrefix0) then
                lastSafeText1 <- lastSafeText0
                lastSafePrefix1 <- lastSafePrefix0
                lastSafeOk1 <- lastSafeOk0

            lastSafeText0 <- text
            lastSafePrefix0 <- prefixLen
            lastSafeOk0 <- ok

        let deferredSafeSpanByFmt = Dictionary<int64, ResizeArray<int>>()

        let packFmtKey (fmtS: int) (fmtE: int) =
            (int64 fmtS <<< 32) ||| int64 (uint32 fmtE)

        let hasUnsafeContextChars (span: ReadOnlySpan<char>) =
            let mutable i = 0
            let mutable found = false

            while not found && i < span.Length do
                match span[i] with
                | '#'
                | '/'
                | '*'
                | '"'
                | '\''
                | '\\' -> found <- true
                | '\r' ->
                    if i + 1 >= span.Length || span[i + 1] <> '\n' then
                        found <- true
                | _ -> ()

                i <- i + 1

            found

        let countNewlines (span: ReadOnlySpan<char>) =
            let mutable count = 0

            for i = 0 to span.Length - 1 do
                if span[i] = '\n' then
                    count <- count + 1

            count

        let canPreserveDisabledContext
            (src: string)
            (edits: ResizeArray<int * int * string>)
            (prefixLen: int)
            =
            let mutable ok = true
            let mutable i = 0

            while ok && i < edits.Count do
                let (o, len, repl) = edits[i]

                if o < prefixLen || len < 0 || o + len > src.Length then
                    ok <- false
                else
                    let oldSpan = src.AsSpan(o, len)
                    let newSpan = repl.AsSpan()

                    if
                        hasUnsafeContextChars oldSpan
                        || hasUnsafeContextChars newSpan
                        || countNewlines oldSpan <> countNewlines newSpan
                    then
                        ok <- false

                i <- i + 1

            ok

        let ensureSafeBaselineSuffix (text: string) (prefixLen: int) =
            if isNull text || prefixLen < 0 || prefixLen > text.Length then
                false
            elif Object.ReferenceEquals(text, lastSafeText0) && prefixLen = lastSafePrefix0 then
                lastSafeOk0
            elif Object.ReferenceEquals(text, lastSafeText1) && prefixLen = lastSafePrefix1 then
                lastSafeOk1
            else
                let checkText =
                    match DeclaredTransformations.tryChainOrigin text with
                    | ValueSome origin when origin.Length >= prefixLen -> origin
                    | _ -> text

                let ok =
                    if isNull deferredCanonicalBase then
                        deferredCanonicalBase <-
                            if prefixLen > 0 then
                                checkText.Substring prefixLen
                            else
                                checkText

                        true
                    else
                        checkText.AsSpan(prefixLen).SequenceEqual(deferredCanonicalBase.AsSpan())

                recordSafeChecked text prefixLen ok
                ok

        let addDeferredDisabledSpan (item: struct (string * int * int * int * int * int)) =
            let struct (srcText, srcPrefixLen, srcS, srcE, fmtS, fmtE) = item

            if srcS < srcE || fmtS < fmtE then
                let sliceLen = srcE - srcS
                let isSafe = sliceLen >= 0 && ensureSafeBaselineSuffix srcText srcPrefixLen

                let duplicateSafe =
                    isSafe
                    && (match deferredSafeSpanByFmt.TryGetValue(packFmtKey fmtS fmtE) with
                        | false, _ -> false
                        | true, indices ->
                            let incoming = srcText.AsSpan(srcS + srcPrefixLen, sliceLen)
                            let mutable found = false
                            let mutable i = 0

                            while not found && i < indices.Count do
                                let struct (eSrc, ePref, eS, eE, _, _) =
                                    deferredDisabledSpans[indices[i]]

                                if
                                    eE - eS = sliceLen
                                    && eSrc.AsSpan(eS + ePref, sliceLen).SequenceEqual(incoming)
                                then
                                    found <- true

                                i <- i + 1

                            found)

                if not duplicateSafe && deferredDisabledSpanSet.Add item then
                    let idx = deferredDisabledSpans.Count
                    deferredDisabledSpans.Add item

                    if isSafe then
                        let key = packFmtKey fmtS fmtE

                        let bucket =
                            match deferredSafeSpanByFmt.TryGetValue key with
                            | true, list -> list
                            | false, _ ->
                                let list = ResizeArray<int>(1)
                                deferredSafeSpanByFmt[key] <- list
                                list

                        bucket.Add idx

        let truncateDeferredDisabledSpans (count: int) =
            while deferredDisabledSpans.Count > count do
                let last = deferredDisabledSpans.Count - 1
                let item = deferredDisabledSpans[last]
                let struct (_, _, _, _, fmtS, fmtE) = item
                let key = packFmtKey fmtS fmtE

                match deferredSafeSpanByFmt.TryGetValue key with
                | true, bucket when bucket.Count > 0 && bucket[bucket.Count - 1] = last ->
                    bucket.RemoveAt(bucket.Count - 1)

                    if bucket.Count = 0 then
                        deferredSafeSpanByFmt.Remove key |> ignore
                | _ -> ()

                deferredDisabledSpanSet.Remove item |> ignore
                deferredDisabledSpans.RemoveAt last

        let clearDeferredDisabledSpans () =
            deferredDisabledSpans.Clear()
            deferredDisabledSpanSet.Clear()
            deferredCanonicalBase <- null
            lastSafeText0 <- null
            lastSafePrefix0 <- -1
            lastSafeOk0 <- false
            lastSafeText1 <- null
            lastSafePrefix1 <- -1
            lastSafeOk1 <- false
            deferredSafeSpanByFmt.Clear()

            if deferredDisabledSpans.Capacity > 1024 then
                deferredDisabledSpans.TrimExcess()
                deferredDisabledSpanSet.TrimExcess()

        let mutable pendingLeft = Array.zeroCreate<int> 256
        let mutable pendingRight = Array.zeroCreate<int> 256
        let mutable pendingCount = 0
        let beforeDirectives = ResizeArray<Trivia>()
        let afterDirectives = ResizeArray<Trivia>()

        let mutable probe: SyntaxTree voption = ValueNone

        let droppedCommas = HashSet<int>()
        let addedCommas = HashSet<int>()
        let commaClosings = HashSet<int>()
        let provenEdits = ResizeArray<int * int * string>()
        let mutable provenSource: string = null
        let mutable provenFormatted: string = null
        let mutable provenRewrite: string = null
        let mutable fullyProvenSource: string = null
        let mutable fullyProvenFormatted: string = null

        let mutable agreedSource: string = null
        let mutable agreedFormatted: string = null
        let mutable sepDeclinedSource: string = null
        let mutable sepDeclinedFormatted: string = null
        let mutable sepDeclinedSpanId: int = -1
        let mutable afterLexedSpanId: int = -1
        let mutable lastLexicalSource: string = null
        let mutable lastLexicalFormatted: string = null
        let mutable lastLexicalBefore: SyntaxTree = ownedBefore
        let mutable lastLexicalId: int = -1
        let mutable lastLexicalPrefix: int = 0
        let savedDefaultBeforeBuf = TokenBuffer()
        let savedDefaultAfterBuf = TokenBuffer()
        let mutable pinnedCondSource: string = null
        let mutable pinnedCondFormatted: string = null
        let mutable pinnedSourceBuf: TokenBuffer = savedDefaultBeforeBuf
        let mutable pinnedFormattedBuf: TokenBuffer = savedDefaultAfterBuf
        let mutable pinnedSourceWin: ConditionalLexWindow = Unchecked.defaultof<_>
        let mutable pinnedFormattedWin: ConditionalLexWindow = Unchecked.defaultof<_>
        let mutable pinnedDefaultLexPrefix: int = 0
        let mutable pinnedSourceCleanDirectives: bool = false
        let mutable pinnedFormattedCleanDirectives: bool = false
        let mutable pinnedSuffixLexicallyEqual: bool = false
        let mutable curSrcPrefixTok: int = 0
        let mutable curSrcPrefixTriv: int = 0
        let mutable curSrcSuffixTok: int = -1
        let mutable curSrcSuffixTriv: int = -1
        let mutable curFmtPrefixTok: int = 0
        let mutable curFmtPrefixTriv: int = 0
        let mutable curFmtSuffixTok: int = -1
        let mutable curFmtSuffixTriv: int = -1
        let mutable curWindowedPairId: int = -1

        let beforePlacement = UsingPlacement()
        let afterPlacement = UsingPlacement()
        let skippedBefore = HashSet<int>()
        let skippedAfter = HashSet<int>()
        let mutable childSlots = Array.zeroCreate<int> 256
        let mutable usingSlots = Array.zeroCreate<int> 64
        let mutable usingSegmentsBefore = Array.zeroCreate<int> 64
        let mutable usingSegmentsAfter = Array.zeroCreate<int> 64
        let mutable usingFramesBefore = Array.zeroCreate<int> 64
        let mutable usingFramesAfter = Array.zeroCreate<int> 64
        let mutable usingIgnoresBefore = Array.zeroCreate<int> 64
        let mutable usingIgnoresAfter = Array.zeroCreate<int> 64
        let inUsingPlacementCursor = UsingPlacementCursor()
        let outUsingPlacementCursor = UsingPlacementCursor()
        let inRunIgnoreCursor = UsingIgnoreStateCursor()
        let outRunIgnoreCursor = UsingIgnoreStateCursor()
        let mutable inUsingLengths = Array.zeroCreate<int> 64
        let mutable usingTaken = Array.zeroCreate<bool> 64
        let mutable usingBuckets = Array.zeroCreate<int> 128
        let mutable usingNext = Array.zeroCreate<int> 64
        let mutable usingPairs = Array.zeroCreate<int> 64
        let rawInRunComments = ResizeArray<UsingRunComment>()
        let inRunComments = ResizeArray<UsingRunComment>()
        let outRunComments = ResizeArray<UsingRunComment>()
        let outBoundaryAndFooterComments = ResizeArray<UsingRunComment>()
        let runDirStack = ResizeArray<struct (int * int)>()
        let runEffDirStack = ResizeArray<struct (int * bool)>()
        let runOuterSpanScratch = ResizeArray<struct (int * int * int * int)>()
        let runTempRawSpans = ResizeArray<struct (int * int * int * int)>()
        let runConsumedScratch = ResizeArray<int>()
        let runPrefixConsumedScratch = ResizeArray<int>()
        let runUndoRawIndices = ResizeArray<int>()
        let runClauseMemo = HashSet<struct (int * int)>()
        let runClauseMemo3 = HashSet<struct (int * int * uint64)>()
        let runClauseStack = ResizeArray<struct (int * int * int * int * int)>()
        let runClauseBfStack = ResizeArray<struct (int * int)>()
        let runClauseMatchedRanges = ResizeArray<struct (int * int)>()
        let runMergedDocScratch = ResizeArray<int>()
        let runNoSkipVisited = ResizeArray<int>()
        let runMergedDocFailedScratch = HashSet<struct (int * int * int * int)>()
        let runMergedDocLinesScratch = ResizeArray<int>()
        let runMergedDocSuffixScratch = ResizeArray<int>()
        let mutable inClauseFrames = Array.zeroCreate<int> 64
        let mutable outClauseFrames = Array.zeroCreate<int> 64
        let mutable inClauseRegionDepths = Array.zeroCreate<int> 64
        let mutable outClauseRegionDepths = Array.zeroCreate<int> 64
        let mutable inClauseRegionSeqs = Array.zeroCreate<int> 64
        let mutable outClauseRegionSeqs = Array.zeroCreate<int> 64
        let mutable inClauseDirSeqs = Array.zeroCreate<int> 64
        let mutable outClauseDirSeqs = Array.zeroCreate<int> 64
        let mutable outBoundaryEndIfDirSeqs = Array.zeroCreate<int> 64
        let outBoundaryRequiresPreCond = ResizeArray<bool>()
        let mutable inSlotStarts = Array.zeroCreate<int> 65
        let mutable inSlotEnds = Array.zeroCreate<int> 65
        let mutable inSlotHasDoc = Array.zeroCreate<bool> 65
        let mutable outSlotStarts = Array.zeroCreate<int> 65
        let mutable outSlotEnds = Array.zeroCreate<int> 65
        let mutable outSlotHasDoc = Array.zeroCreate<bool> 64
        let mutable outSlotNonDocCounts = Array.zeroCreate<int> 64
        let mutable outSlotDocCounts = Array.zeroCreate<int> 64
        let mutable outSlotDocLines = Array.zeroCreate<int> 64
        let mutable outMaxInPrefix = Array.zeroCreate<int> 65
        let mutable bfRemainingMaxIn = Array.zeroCreate<int> 65
        let mutable invUsingPairs = Array.zeroCreate<int> 64
        let mutable runTargetSlots = Array.zeroCreate<int> 64
        let mutable runOrderedToRaw = Array.zeroCreate<int> 64
        let mutable runRawOrigSlots = Array.zeroCreate<int> 64
        let mutable runRawIsFloating = Array.zeroCreate<bool> 64
        let mutable runIsFloating = Array.zeroCreate<bool> 64
        let mutable inSameRunEnd = Array.zeroCreate<int> 64
        let mutable outSameRunEnd = Array.zeroCreate<int> 64
        let mutable runNextFooterEligible = Array.zeroCreate<int> 64
        let mutable runNonFooterPrefix = Array.zeroCreate<int> 65
        let mutable runNonDocPrefix = Array.zeroCreate<int> 65
        let mutable runDocCountPrefix = Array.zeroCreate<int> 65
        let mutable runDocLinePrefix = Array.zeroCreate<int> 65
        let mutable runNonFooterNonDocPrefix = Array.zeroCreate<int> 65
        let mutable runNonFooterDocPrefix = Array.zeroCreate<int> 65
        let mutable runLastEndBfIdx = 0
        let mutable runLastEndBfPos = 0
        let mutable runBoundaryCount = 0
        let mutable runSlotDisplaced = Array.zeroCreate<bool> 64
        let mutable runSlotSavedRawStart = Array.zeroCreate<int> 64
        let mutable runSlotConsumedStart = Array.zeroCreate<int> 64
        let mutable runSlotConsumedCount = Array.zeroCreate<int> 64
        let mutable runSlotPreS0EndBfIdx = Array.zeroCreate<int> 64
        let mutable runSlotPreS0EndBfPos = Array.zeroCreate<int> 64
        let runNextClauseFrames = Dictionary<int, int>()
        let runOutSlotFrames = HashSet<int>()
        let mutable runSlotCounts = Array.zeroCreate<int> 65
        let mutable runSlotOffsets = Array.zeroCreate<int> 65
        let mutable runInConsumed = Array.zeroCreate<bool> 64
        let mutable runCanGoFooter = Array.zeroCreate<bool> 64
        let runFooterIndex = UsingFooterIndex()
        let runDocTempStarts = ResizeArray<int>()
        let runDocTempPolys = ResizeArray<uint64>()
        let runDocBfSpansScratch = ResizeArray<int>()
        let runDocMidFreqScratch = Dictionary<int, int>()
        let runDocMidLensScratch = ResizeArray<struct (int * int)>()
        let runDocSelectedLensScratch = ResizeArray<int>()
        let mutable runDocKHistScratch = Array.zeroCreate<int> 64
        let mutable runDocKSumScratch = Array.zeroCreate<int> 64
        let runFooterDocStates = HashSet<struct (int * int * int * int * bool)>()
        let runFooterSpanningEntries = ResizeArray<DirectiveSpanningFooterEntry>()
        let mutable runFooterSpanningBuckets = Array.zeroCreate<int> 64
        let mutable runFooterSpanningNext = Array.zeroCreate<int> 64
        let mutable runFooterSpanningHashes = Array.zeroCreate<uint64> 64
        let mutable runSlotRetryStates = Array.zeroCreate<UsingSlotRetryState> 64
        let mutable runOtherSlotsScratch = Array.zeroCreate<int> 64
        let interpLeft = TokenBuffer()
        let interpRight = TokenBuffer()
        let interpLeftDepthBuffers = ResizeArray<TokenBuffer>()
        let interpRightDepthBuffers = ResizeArray<TokenBuffer>()
        let interpScanDepthBuffers = ResizeArray<TokenBuffer>()
        let interpHoleBuffers = ResizeArray<TokenBuffer>()
        let interpHoleTreesLeft = ResizeArray<SyntaxTree>()
        let interpHoleTreesRight = ResizeArray<SyntaxTree>()

        let getDepthBuffer (buffers: ResizeArray<TokenBuffer>) (depth: int) =
            while buffers.Count <= depth do
                buffers.Add(TokenBuffer())

            buffers[depth]

        let orderDirectives (tree: SyntaxTree) (items: ResizeArray<Trivia>) =
            items.Clear()

            for index = 0 to tree.TriviaCount - 1 do
                let item = tree.Trivia index

                if directive item.Kind then
                    items.Add item

            if tree.TriviaCount <> tree.LexerBuffer.TriviaCount then
                items.Sort directiveOrder

        let isNewLine ch =
            ch = '\r' || ch = '\n' || ch = '\u0085' || ch = '\u2028' || ch = '\u2029'

        let quotedDirectiveTerminated (span: ReadOnlySpan<char>) =
            let mutable inString = false
            let mutable ok = true
            let mutable index = 0

            while ok && index < span.Length do
                let ch = span[index]

                if inString then
                    if ch = '"' then
                        inString <- false
                elif ch = '"' then
                    inString <- true
                elif ch = '\'' then
                    ok <- false
                elif ch = '/' && index + 1 < span.Length && span[index + 1] = '/' then
                    index <- span.Length

                index <- index + 1

            ok && not inString

        let directiveComparand (text: string) (item: Trivia) : ReadOnlySpan<char> =
            let span = text.AsSpan(item.Start, item.Length)

            let trimmable =
                if
                    item.Kind = TriviaKind.LineDirectiveTrivia
                    || item.Kind = TriviaKind.LineSpanDirectiveTrivia
                    || item.Kind = TriviaKind.PragmaChecksumDirectiveTrivia
                then
                    quotedDirectiveTerminated span
                elif
                    item.Kind = TriviaKind.RegionDirectiveTrivia
                    || item.Kind = TriviaKind.EndRegionDirectiveTrivia
                then
                    true
                else
                    let code =
                        match span.IndexOf("//".AsSpan(), StringComparison.Ordinal) with
                        | commentIndex when commentIndex >= 0 -> span.Slice(0, commentIndex)
                        | _ -> span

                    code.IndexOfAny('"', '\'') < 0

            if trimmable then
                span.Trim()
            else
                let body = span.TrimStart()

                if body.EndsWith("\r\n".AsSpan(), StringComparison.Ordinal) then
                    body.Slice(0, body.Length - 2)
                elif body.Length > 0 && isNewLine body[body.Length - 1] then
                    body.Slice(0, body.Length - 1)
                else
                    body

        let collectDirectives
            (quoted: bool)
            (text: string)
            (tree: SyntaxTree)
            (items: ResizeArray<Trivia>)
            =
            items.Clear()
            let outerTriviaCount = tree.LexerBuffer.TriviaCount

            let outerLastContent =
                max tree.LexerBuffer.LastCommentTrivia tree.LexerBuffer.LastNonCommentTrivia

            if outerTriviaCount = tree.TriviaCount && outerLastContent < 0 then
                true
            else
                let limit =
                    if outerTriviaCount = tree.TriviaCount then
                        outerLastContent + 1
                    else
                        tree.TriviaCount

                let mutable openConditionals = 0
                let mutable openRegions = 0
                let mutable clean = true
                let mutable index = 0

                while clean && index < limit do
                    let item = tree.Trivia index

                    match item.Kind with
                    | TriviaKind.WhitespaceTrivia
                    | TriviaKind.EndOfLineTrivia
                    | TriviaKind.DisabledTextTrivia -> ()
                    | TriviaKind.SingleLineCommentTrivia ->
                        let finish = item.Start + item.Length
                        clean <- finish = text.Length || isNewLine text[finish]
                    | TriviaKind.SingleLineDocumentationCommentTrivia ->
                        let finish = item.Start + item.Length

                        clean <-
                            item.Length > 0 && (finish = text.Length || isNewLine text[finish - 1])
                    | TriviaKind.MultiLineCommentTrivia ->
                        clean <-
                            item.Length >= 4
                            && text.AsSpan(item.Start, item.Length).EndsWith("*/".AsSpan())
                    | TriviaKind.MultiLineDocumentationCommentTrivia ->
                        let finish = item.Start + item.Length
                        let mutable next = finish

                        while next < text.Length && (text[next] = ' ' || text[next] = '\t') do
                            next <- next + 1

                        clean <-
                            item.Length >= 5
                            && text.AsSpan(item.Start, item.Length).EndsWith("*/".AsSpan())
                            && (next = text.Length || text[next] <> '#')
                    | TriviaKind.LineSpanDirectiveTrivia
                    | TriviaKind.PragmaChecksumDirectiveTrivia when not quoted -> clean <- false
                    | TriviaKind.BadDirectiveTrivia
                    | TriviaKind.ReferenceDirectiveTrivia
                    | TriviaKind.LoadDirectiveTrivia
                    | TriviaKind.IgnoredDirectiveTrivia
                    | TriviaKind.SkippedTokensTrivia
                    | TriviaKind.ConflictMarkerTrivia -> clean <- false
                    | TriviaKind.ShebangDirectiveTrivia ->
                        clean <-
                            index < outerTriviaCount
                            && openConditionals = 0
                            && openRegions = 0
                            && isValidShebang text &item

                        items.Add item
                    | kind when directive kind ->
                        let finish = item.Start + item.Length
                        let span = text.AsSpan(item.Start, item.Length)

                        let codeSpan =
                            if
                                kind = TriviaKind.RegionDirectiveTrivia
                                || kind = TriviaKind.EndRegionDirectiveTrivia
                            then
                                ReadOnlySpan<char>.Empty
                            else
                                match span.IndexOf("//".AsSpan(), StringComparison.Ordinal) with
                                | commentIndex when commentIndex >= 0 -> span.Slice(0, commentIndex)
                                | _ -> span

                        let validInHole =
                            index < outerTriviaCount
                            || (kind <> TriviaKind.IfDirectiveTrivia
                                && kind <> TriviaKind.ElifDirectiveTrivia
                                && kind <> TriviaKind.ElseDirectiveTrivia
                                && kind <> TriviaKind.EndIfDirectiveTrivia
                                && kind <> TriviaKind.RegionDirectiveTrivia
                                && kind <> TriviaKind.EndRegionDirectiveTrivia
                                && kind <> TriviaKind.DefineDirectiveTrivia
                                && kind <> TriviaKind.UndefDirectiveTrivia)

                        if kind = TriviaKind.IfDirectiveTrivia then
                            openConditionals <- openConditionals + 1
                        elif kind = TriviaKind.EndIfDirectiveTrivia then
                            openConditionals <- openConditionals - 1
                        elif kind = TriviaKind.RegionDirectiveTrivia then
                            openRegions <- openRegions + 1
                        elif kind = TriviaKind.EndRegionDirectiveTrivia then
                            openRegions <- openRegions - 1

                        clean <-
                            validInHole
                            && item.Length > 0
                            && (finish = text.Length || isNewLine text[finish - 1])
                            && (codeSpan.IndexOfAny('"', '\'') < 0
                                || (quoted
                                    && (kind = TriviaKind.LineDirectiveTrivia
                                        || kind = TriviaKind.LineSpanDirectiveTrivia
                                        || kind = TriviaKind.PragmaChecksumDirectiveTrivia
                                        || kind = TriviaKind.ErrorDirectiveTrivia
                                        || kind = TriviaKind.WarningDirectiveTrivia)))
                            && not (span.Contains("/*".AsSpan(), StringComparison.Ordinal))

                        items.Add item
                    | _ -> clean <- false

                    index <- index + 1

                clean <- clean && openConditionals = 0 && openRegions = 0

                if clean && tree.TriviaCount <> outerTriviaCount then
                    items.Sort directiveOrder

                clean

        let cleanBufferDirectivesRange
            (text: string)
            (buf: TokenBuffer)
            (startIdx: int)
            (endIdx: int)
            =
            let lastContent = min endIdx (max buf.LastCommentTrivia buf.LastNonCommentTrivia)

            if lastContent < startIdx then
                true
            else
                let trivia = buf.TriviaSpan()
                let mutable openConditionals = 0
                let mutable openRegions = 0
                let mutable clean = true
                let mutable index = max 0 startIdx

                while clean && index <= lastContent do
                    let item = trivia[index]

                    match item.Kind with
                    | TriviaKind.WhitespaceTrivia
                    | TriviaKind.EndOfLineTrivia -> ()
                    | TriviaKind.DisabledTextTrivia ->
                        clean <- not (disabledRunMayOpen (text.AsSpan()) item)
                    | TriviaKind.SingleLineCommentTrivia ->
                        let finish = item.Start + item.Length
                        clean <- finish = text.Length || isNewLine text[finish]
                    | TriviaKind.SingleLineDocumentationCommentTrivia ->
                        let finish = item.Start + item.Length

                        clean <-
                            item.Length > 0 && (finish = text.Length || isNewLine text[finish - 1])
                    | TriviaKind.MultiLineCommentTrivia ->
                        clean <-
                            item.Length >= 4
                            && text.AsSpan(item.Start, item.Length).EndsWith("*/".AsSpan())
                    | TriviaKind.MultiLineDocumentationCommentTrivia ->
                        let finish = item.Start + item.Length
                        let mutable next = finish

                        while next < text.Length && (text[next] = ' ' || text[next] = '\t') do
                            next <- next + 1

                        clean <-
                            item.Length >= 5
                            && text.AsSpan(item.Start, item.Length).EndsWith("*/".AsSpan())
                            && (next = text.Length || text[next] <> '#')
                    | TriviaKind.BadDirectiveTrivia
                    | TriviaKind.LineSpanDirectiveTrivia
                    | TriviaKind.PragmaChecksumDirectiveTrivia
                    | TriviaKind.ReferenceDirectiveTrivia
                    | TriviaKind.LoadDirectiveTrivia
                    | TriviaKind.IgnoredDirectiveTrivia
                    | TriviaKind.SkippedTokensTrivia
                    | TriviaKind.ConflictMarkerTrivia -> clean <- false
                    | TriviaKind.ShebangDirectiveTrivia ->
                        clean <-
                            openConditionals = 0 && openRegions = 0 && isValidShebang text &item
                    | kind when directive kind ->
                        let finish = item.Start + item.Length
                        let span = text.AsSpan(item.Start, item.Length)

                        let codeSpan =
                            if
                                kind = TriviaKind.RegionDirectiveTrivia
                                || kind = TriviaKind.EndRegionDirectiveTrivia
                            then
                                ReadOnlySpan<char>.Empty
                            else
                                match span.IndexOf("//".AsSpan(), StringComparison.Ordinal) with
                                | commentIndex when commentIndex >= 0 -> span.Slice(0, commentIndex)
                                | _ -> span

                        if kind = TriviaKind.IfDirectiveTrivia then
                            openConditionals <- openConditionals + 1
                        elif kind = TriviaKind.EndIfDirectiveTrivia then
                            openConditionals <- openConditionals - 1
                        elif kind = TriviaKind.RegionDirectiveTrivia then
                            openRegions <- openRegions + 1
                        elif kind = TriviaKind.EndRegionDirectiveTrivia then
                            openRegions <- openRegions - 1

                        clean <-
                            item.Length > 0
                            && (finish = text.Length || isNewLine text[finish - 1])
                            && codeSpan.IndexOfAny('"', '\'') < 0
                            && not (span.Contains("/*".AsSpan(), StringComparison.Ordinal))
                    | _ -> clean <- false

                    index <- index + 1

                clean && openConditionals = 0 && openRegions = 0

        let cleanBufferDirectives (text: string) (buf: TokenBuffer) =
            cleanBufferDirectivesRange
                text
                buf
                0
                (max buf.LastCommentTrivia buf.LastNonCommentTrivia)

        let agree (left: string) (right: string) =
            let beforeTokens = before.TokenSpan()
            let afterTokens = after.TokenSpan()
            let limit = min beforeTokens.Length afterTokens.Length
            let mutable index = 0
            let mutable same = true

            while same && index < limit do
                let leftToken = &beforeTokens[index]
                let rightToken = &afterTokens[index]

                same <-
                    leftToken.Kind = rightToken.Kind
                    && leftToken.Length = rightToken.Length
                    && sameTokenText left &leftToken right &rightToken

                if same then
                    index <- index + 1

            struct (same && beforeTokens.Length = afterTokens.Length, index)

        let trimmedRun (whole: string) (item: Trivia) =
            let mutable length = item.Length

            while length > 0 && isNewLine whole[item.Start + length - 1] do
                length <- length - 1

            length

        let runBeginsLine (whole: string) (start: int) =
            let mutable index = start

            while index > 0 && CommentContent.indent whole[index - 1] do
                index <- index - 1

            index = 0 || isNewLine whole[index - 1]

        let triviaRunsAgree
            (source: string)
            (formatted: string)
            (input: TokenBuffer)
            (output: TokenBuffer)
            leftStart
            leftCount
            rightStart
            rightCount
            =
            let inputTrivia = input.TriviaSpan()
            let outputTrivia = output.TriviaSpan()
            let leftEnd = leftStart + leftCount
            let rightEnd = rightStart + rightCount
            let mutable left = leftStart
            let mutable right = rightStart
            let mutable same = true

            while same && (left < leftEnd || right < rightEnd) do
                while left < leftEnd && not (contentTrivia inputTrivia[left].Kind) do
                    left <- left + 1

                while right < rightEnd && not (contentTrivia outputTrivia[right].Kind) do
                    right <- right + 1

                if left < leftEnd && right < rightEnd then
                    let a = inputTrivia[left]
                    let b = outputTrivia[right]
                    let aLength = trimmedRun source a
                    let bLength = trimmedRun formatted b

                    same <-
                        a.Kind = b.Kind
                        && (if
                                aLength = bLength
                                && source
                                    .AsSpan(a.Start, aLength)
                                    .SequenceEqual(formatted.AsSpan(b.Start, bLength))
                            then
                                true
                            else
                                commentTrivia a.Kind
                                && CommentContent.equivalent source a formatted b)
                        && runBeginsLine source a.Start = runBeginsLine formatted b.Start
                        && (a.Kind <> TriviaKind.ShebangDirectiveTrivia
                            || (a.Start = 0 && b.Start = 0))

                    left <- left + 1
                    right <- right + 1
                else
                    same <- left = leftEnd && right = rightEnd

            same

        let singleConfiguration (buffer: TokenBuffer) = not buffer.HasSingleConfigBlocker

        let nonCommentTriviaRunsAgreeSpan
            (allowConditional: bool)
            (source: ReadOnlySpan<char>)
            (formatted: ReadOnlySpan<char>)
            (input: TokenBuffer)
            (output: TokenBuffer)
            leftStart
            leftCount
            rightStart
            rightCount
            =
            let inputTrivia = input.TriviaSpan()
            let outputTrivia = output.TriviaSpan()
            let leftEnd = leftStart + leftCount
            let rightEnd = rightStart + rightCount
            let mutable left = leftStart
            let mutable right = rightStart
            let mutable same = true

            while same && (left < leftEnd || right < rightEnd) do
                while left < leftEnd
                      && not (
                          nonCommentContentTriviaForProof allowConditional inputTrivia[left].Kind
                      ) do
                    left <- left + 1

                while right < rightEnd
                      && not (
                          nonCommentContentTriviaForProof allowConditional outputTrivia[right].Kind
                      ) do
                    right <- right + 1

                if left < leftEnd && right < rightEnd then
                    let a = inputTrivia[left]
                    let b = outputTrivia[right]
                    let aLength = trimmedRunSpan source a
                    let bLength = trimmedRunSpan formatted b

                    same <-
                        a.Kind = b.Kind
                        && aLength = bLength
                        && source
                            .Slice(a.Start, aLength)
                            .SequenceEqual(formatted.Slice(b.Start, bLength))
                        && runBeginsLineSpan source a.Start = runBeginsLineSpan formatted b.Start
                        && (a.Kind <> TriviaKind.ShebangDirectiveTrivia
                            || (a.Start = 0 && b.Start = 0))

                    left <- left + 1
                    right <- right + 1
                else
                    same <- left = leftEnd && right = rightEnd

            same

        let nonCommentRunIsLayoutOnly (buffer: TokenBuffer) start count =
            let trivia = buffer.TriviaSpan()
            let finish = start + count
            let mutable index = start
            let mutable only = true

            while only && index < finish do
                if nonCommentContentTrivia trivia[index].Kind then
                    only <- false

                index <- index + 1

            only

        let cleanHoleTrivia (text: string) (buf: TokenBuffer) =
            if DeclaredTransformations.hasMalformedTrivia buf then
                false
            else
                let trivia = buf.TriviaSpan()
                let mutable clean = true
                let mutable idx = 0

                while clean && idx < trivia.Length do
                    let item = &trivia[idx]

                    match item.Kind with
                    | TriviaKind.WhitespaceTrivia
                    | TriviaKind.EndOfLineTrivia -> ()
                    | TriviaKind.SingleLineCommentTrivia ->
                        let finish = item.Start + item.Length
                        clean <- finish = text.Length || isNewLine text[finish]
                    | TriviaKind.SingleLineDocumentationCommentTrivia ->
                        let finish = item.Start + item.Length

                        clean <-
                            item.Length > 0 && (finish = text.Length || isNewLine text[finish - 1])
                    | TriviaKind.MultiLineCommentTrivia ->
                        clean <-
                            item.Length >= 4
                            && text.AsSpan(item.Start, item.Length).EndsWith("*/".AsSpan())
                    | TriviaKind.MultiLineDocumentationCommentTrivia ->
                        let finish = item.Start + item.Length
                        let mutable next = finish

                        while next < text.Length && (text[next] = ' ' || text[next] = '\t') do
                            next <- next + 1

                        clean <-
                            item.Length >= 5
                            && text.AsSpan(item.Start, item.Length).EndsWith("*/".AsSpan())
                            && (next = text.Length || text[next] <> '#')
                    | _ -> clean <- false

                    idx <- idx + 1

                clean

        let parseInterpHeader (allowMultilineRaw: bool) (text: string) (tok: Token) =
            let mutable quote = tok.Start
            let mutable dollars = 0
            let mutable verbatim = false
            let mutable ats = 0

            while quote < tok.End && text[quote] <> '"' do
                if text[quote] = '$' then
                    dollars <- dollars + 1
                elif text[quote] = '@' then
                    verbatim <- true
                    ats <- ats + 1

                quote <- quote + 1

            let mutable quoteCount = 0

            while quote + quoteCount < tok.End && text[quote + quoteCount] = '"' do
                quoteCount <- quoteCount + 1

            let raw = not verbatim && quoteCount >= 3
            let invalid = ats > 1 || dollars < 1 || (dollars > 1 && (ats > 0 || quoteCount < 3))
            let width = if raw then max 1 dollars else 1
            let contentStart = quote + (if raw then quoteCount else 1)
            let mutable contentEnd = tok.End
            let mutable closed = false

            if not invalid then
                if raw then
                    let mutable ending = tok.End

                    while ending > contentStart && text[ending - 1] = '"' do
                        ending <- ending - 1

                    if tok.End - ending >= quoteCount then
                        closed <- true
                        contentEnd <- ending
                elif tok.End > contentStart && text[tok.End - 1] = '"' then
                    let mutable preceding = tok.End - 1

                    if verbatim then
                        while preceding > contentStart && text[preceding - 1] = '"' do
                            preceding <- preceding - 1

                        closed <- (tok.End - preceding) % 2 = 1
                    else
                        while preceding > contentStart && text[preceding - 1] = '\\' do
                            preceding <- preceding - 1

                        closed <- (tok.End - 1 - preceding) % 2 = 0

                    if closed then
                        contentEnd <- tok.End - 1

            let validNonMultiline =
                not invalid
                && closed
                && (allowMultilineRaw
                    || not raw
                    || text.AsSpan(tok.Start, tok.Length).IndexOfAny(lineTerminatorChars) < 0)

            struct (validNonMultiline, raw, verbatim, width, contentStart, contentEnd)

        let nextInterpHole
            (text: string)
            (raw: bool)
            (verbatim: bool)
            (width: int)
            (startCursor: int)
            (contentEnd: int)
            =
            let mutable cursor = startCursor
            let mutable holeOpen = -1
            let mutable degraded = false

            while cursor < contentEnd && holeOpen < 0 && not degraded do
                if not raw && not verbatim && text[cursor] = '\\' then
                    cursor <- min contentEnd (cursor + 2)
                elif
                    not raw
                    && text[cursor] = '{'
                    && cursor + 1 < contentEnd
                    && text[cursor + 1] = '{'
                then
                    cursor <- cursor + 2
                elif text[cursor] = '{' then
                    let mutable run = cursor

                    while run < contentEnd && text[run] = '{' do
                        run <- run + 1

                    if run - cursor < width then cursor <- run
                    elif raw && run - cursor >= width * 2 then degraded <- true
                    else holeOpen <- if raw then run - width else cursor
                elif raw && text[cursor] = '}' then
                    let mutable finish = cursor

                    while finish < contentEnd && text[finish] = '}' do
                        finish <- finish + 1

                    if finish - cursor >= width then
                        degraded <- true

                    cursor <- finish
                else
                    cursor <- cursor + 1

            struct (not degraded, holeOpen)

        let scanFormatEnd (text: string) (raw: bool) (verbatim: bool) (startPos: int) (cEnd: int) =
            let mutable closing = min cEnd startPos

            while closing < cEnd && text[closing] <> '}' && not (raw && text[closing] = '"') do
                if not raw && not verbatim && text[closing] = '\\' then
                    closing <- min cEnd (closing + 2)
                else
                    closing <- closing + 1

            closing

        let hasClosingWidth (text: string) (pos: int) (cEnd: int) (w: int) =
            if pos + w > cEnd then
                false
            else
                let mutable ok = true

                for k = 0 to w - 1 do
                    if text[pos + k] <> '}' then
                        ok <- false

                ok

        let interpolatedStringsLexicallyEqual
            (allowMultilineRaw: bool)
            (source: string)
            (left: Token)
            (formatted: string)
            (right: Token)
            =
            let struct (lValid, lRaw, lVerbatim, lWidth, lContentStart, lContentEnd) =
                parseInterpHeader allowMultilineRaw source left

            let struct (rValid, rRaw, rVerbatim, rWidth, rContentStart, rContentEnd) =
                parseInterpHeader allowMultilineRaw formatted right

            if
                not lValid
                || not rValid
                || lRaw <> rRaw
                || lVerbatim <> rVerbatim
                || lWidth <> rWidth
                || lContentStart - left.Start <> rContentStart - right.Start
                || left.End - lContentEnd <> right.End - rContentEnd
                || not (
                    source
                        .AsSpan(left.Start, lContentStart - left.Start)
                        .SequenceEqual(formatted.AsSpan(right.Start, rContentStart - right.Start))
                )
                || not (
                    source
                        .AsSpan(lContentEnd, left.End - lContentEnd)
                        .SequenceEqual(formatted.AsSpan(rContentEnd, right.End - rContentEnd))
                )
            then
                false
            else
                let mutable ok = true
                let mutable lCursor = lContentStart
                let mutable rCursor = rContentStart

                while ok && (lCursor < lContentEnd || rCursor < rContentEnd) do
                    let struct (lOk, lOpen) =
                        nextInterpHole source lRaw lVerbatim lWidth lCursor lContentEnd

                    let struct (rOk, rOpen) =
                        nextInterpHole formatted rRaw rVerbatim rWidth rCursor rContentEnd

                    if not lOk || not rOk || (lOpen >= 0) <> (rOpen >= 0) then
                        ok <- false
                    else
                        let lSegEnd = if lOpen >= 0 then lOpen else lContentEnd
                        let rSegEnd = if rOpen >= 0 then rOpen else rContentEnd

                        if
                            lSegEnd - lCursor <> rSegEnd - rCursor
                            || not (
                                source
                                    .AsSpan(lCursor, lSegEnd - lCursor)
                                    .SequenceEqual(formatted.AsSpan(rCursor, rSegEnd - rCursor))
                            )
                        then
                            ok <- false
                        elif lOpen < 0 then
                            lCursor <- lContentEnd
                            rCursor <- rContentEnd
                        else
                            let lExprStart = lOpen + lWidth
                            let rExprStart = rOpen + rWidth

                            let struct (lBoundary, lFormat) =
                                Lexer.lexInterpolationWithRecovery
                                    false
                                    source
                                    (lExprStart - 1)
                                    lContentEnd
                                    interpLeft

                            let struct (rBoundary, rFormat) =
                                Lexer.lexInterpolationWithRecovery
                                    false
                                    formatted
                                    (rExprStart - 1)
                                    rContentEnd
                                    interpRight

                            if
                                lFormat <> rFormat
                                || interpLeft.TokenCount <> interpRight.TokenCount
                                || interpLeft.TokenCount < 2
                                || not (cleanHoleTrivia source interpLeft)
                                || not (cleanHoleTrivia formatted interpRight)
                            then
                                ok <- false
                            else
                                let mutable t = 0

                                while ok && t < interpLeft.TokenCount do
                                    let a = interpLeft.Token t
                                    let b = interpRight.Token t

                                    ok <-
                                        a.Kind = b.Kind
                                        && a.Kind <> TokenKind.BadToken
                                        && a.Length = b.Length
                                        && sameTokenText source &a formatted &b
                                        && (a.Kind
                                            <> TokenKind.GreaterThanGreaterThanGreaterThanToken
                                            || let leftAdj =
                                                t + 1 < interpLeft.TokenCount
                                                && (interpLeft.Token(t + 1)).Start = a.End
                                                && (interpLeft.Token(t + 1)).LeadingCount = 0 in

                                               let rightAdj =
                                                   t + 1 < interpRight.TokenCount
                                                   && (interpRight.Token(t + 1)).Start = b.End
                                                   && (interpRight.Token(t + 1)).LeadingCount = 0 in

                                               leftAdj = rightAdj)
                                        && (a.LeadingCount = 0 && b.LeadingCount = 0
                                            || triviaRunsAgree
                                                source
                                                formatted
                                                interpLeft
                                                interpRight
                                                a.TriviaStart
                                                a.LeadingCount
                                                b.TriviaStart
                                                b.LeadingCount)
                                        && (a.TrailingCount = 0 && b.TrailingCount = 0
                                            || triviaRunsAgree
                                                source
                                                formatted
                                                interpLeft
                                                interpRight
                                                (a.TriviaStart + a.LeadingCount)
                                                a.TrailingCount
                                                (b.TriviaStart + b.LeadingCount)
                                                b.TrailingCount)

                                    t <- t + 1

                                if ok then
                                    if lFormat then
                                        let lFormatStart = min lContentEnd (lBoundary + 1)
                                        let rFormatStart = min rContentEnd (rBoundary + 1)

                                        let lClosing =
                                            scanFormatEnd
                                                source
                                                lRaw
                                                lVerbatim
                                                lFormatStart
                                                lContentEnd

                                        let rClosing =
                                            scanFormatEnd
                                                formatted
                                                rRaw
                                                rVerbatim
                                                rFormatStart
                                                rContentEnd

                                        ok <-
                                            lClosing - lFormatStart = rClosing - rFormatStart
                                            && source
                                                .AsSpan(lFormatStart, lClosing - lFormatStart)
                                                .SequenceEqual(
                                                    formatted.AsSpan(
                                                        rFormatStart,
                                                        rClosing - rFormatStart
                                                    )
                                                )
                                            && hasClosingWidth source lClosing lContentEnd lWidth
                                            && hasClosingWidth formatted rClosing rContentEnd rWidth

                                        lCursor <- lClosing + lWidth
                                        rCursor <- rClosing + rWidth
                                    else
                                        ok <-
                                            (interpLeft.Token(interpLeft.TokenCount - 2)).Kind =
                                                TokenKind.CloseBraceToken
                                            && hasClosingWidth source lBoundary lContentEnd lWidth
                                            && hasClosingWidth
                                                formatted
                                                rBoundary
                                                rContentEnd
                                                rWidth

                                        lCursor <- lBoundary + lWidth
                                        rCursor <- rBoundary + rWidth

                ok

        let usableSourceTree (sourceTree: SyntaxTree) =
            not (isNull (box sourceTree))
            && sourceTree.NodeCount > 0
            && not sourceTree.LexerBuffer.IsVerifyOnly

        let ensureBeforeParsed (source: string) =
            if not beforeBuilt then
                buildFromLexed source before
                beforeBuilt <- true

            before.IsComplete

        let findBeforeTokenAt (targetStart: int) =
            let mutable lo = 0
            let mutable hi = before.TokenCount - 1
            let mutable pIdx = -1

            while lo <= hi && pIdx < 0 do
                let mid = (lo + hi) >>> 1
                let midStart = (before.Token mid).Start

                if midStart = targetStart then pIdx <- mid
                elif midStart < targetStart then lo <- mid + 1
                else hi <- mid - 1

            while pIdx > 0 && (before.Token(pIdx - 1)).Start = targetStart do
                pIdx <- pIdx - 1

            while pIdx >= 0
                  && pIdx < before.TokenCount
                  && (before.Token pIdx).Start = targetStart
                  && (before.Token pIdx).Length <= 0 do
                pIdx <- pIdx + 1

            if pIdx >= 0 && pIdx < before.TokenCount && (before.Token pIdx).Start = targetStart then
                pIdx
            else
                -1

        let reindentedInterpolatedStringsEqual
            options
            (source: string)
            (left: Token)
            (formatted: string)
            (right: Token)
            =
            match
                DeclaredTransformations.tryReindentRawInterpolation
                    options
                    source
                    left
                    formatted
                    right
            with
            | Some reindented ->
                let reindentedTok: Token =
                    {
                        Kind = left.Kind
                        Start = 0
                        Length = reindented.Length
                        TriviaStart = 0
                        LeadingCount = 0
                        TrailingCount = 0
                    }

                interpolatedStringsLexicallyEqual true reindented reindentedTok formatted right
            | None -> false

        let findChildSlotContainingToken (currNode: Node) (tokIdx: int) =
            let mutable lo = 0
            let mutable hi = currNode.ChildCount - 1
            let mutable foundSlot = -1

            while lo <= hi && foundSlot < 0 do
                let mid = (lo + hi) >>> 1
                let c = before.Child(currNode.ChildStart + mid)

                let struct (tStart, tEnd) =
                    if c < 0 then
                        let ti = ~~~c
                        struct (ti, ti + 1)
                    else
                        let cn = before.Node c
                        struct (cn.TokenStart, cn.TokenStart + cn.TokenCount)

                if tokIdx < tStart then hi <- mid - 1
                elif tokIdx >= tEnd then lo <- mid + 1
                else foundSlot <- mid

            foundSlot

        let hashUsingClauseSpan
            (text: ReadOnlySpan<char>)
            (buf: TokenBuffer)
            (startTok: int)
            (len: int)
            =
            let mutable h = 2166136261u

            for t = 0 to len - 1 do
                let tok = buf.Token(startTok + t)
                let w = greaterWidth tok.Kind

                if w > 0 then
                    for _ = 1 to w do
                        h <- (h ^^^ uint32 TokenKind.GreaterThanToken) * 16777619u
                else
                    let span = text.Slice(tok.Start, tok.Length)

                    h <-
                        (h ^^^ (uint32 tok.Kind * 31u + uint32 (String.GetHashCode span)))
                        * 16777619u

            int (h &&& 0x7FFFFFFFu)

        let tryScanExternAliasTokens
            (srcSpan: ReadOnlySpan<char>)
            (tokens: ReadOnlySpan<Token>)
            (pos: int)
            =
            let count = tokens.Length

            if
                pos + 3 < count
                && tokens[pos].Kind = TokenKind.ExternKeyword
                && (tokens[pos + 1].Kind = TokenKind.AliasKeyword
                    || (tokens[pos + 1].Kind = TokenKind.IdentifierToken
                        && tokens[pos + 1].Length = 5
                        && srcSpan.Slice(tokens[pos + 1].Start, 5).SequenceEqual("alias".AsSpan())))
                && tokens[pos + 2].Kind = TokenKind.IdentifierToken
                && tokens[pos + 3].Kind = TokenKind.SemicolonToken
            then
                4
            else
                -1

        let tryScanNamespaceHeader (tokens: ReadOnlySpan<Token>) (pos: int) =
            let count = tokens.Length

            if pos >= count || tokens[pos].Kind <> TokenKind.NamespaceKeyword then
                struct (-1, false)
            else
                let mutable k = pos + 1
                let mutable nameToks = 0
                let mutable ok = true

                while ok
                      && k < count
                      && tokens[k].Kind <> TokenKind.OpenBraceToken
                      && tokens[k].Kind <> TokenKind.SemicolonToken do
                    match tokens[k].Kind with
                    | TokenKind.IdentifierToken
                    | TokenKind.DotToken
                    | TokenKind.ColonColonToken
                    | TokenKind.GlobalKeyword ->
                        nameToks <- nameToks + 1
                        k <- k + 1
                    | _ -> ok <- false

                if not ok || nameToks = 0 || k >= count then
                    struct (-1, false)
                elif tokens[k].Kind = TokenKind.OpenBraceToken then
                    struct (k + 1 - pos, true)
                else
                    struct (k + 1 - pos, false)

        let tryScanUsingClauseTokens
            (srcSpan: ReadOnlySpan<char>)
            (tokens: ReadOnlySpan<Token>)
            (pos: int)
            =
            let count = tokens.Length

            let k0 =
                if
                    pos + 1 < count
                    && tokens[pos + 1].Kind = TokenKind.UsingKeyword
                    && (tokens[pos].Kind = TokenKind.GlobalKeyword
                        || (tokens[pos].Kind = TokenKind.IdentifierToken
                            && tokens[pos].Length = 6
                            && srcSpan.Slice(tokens[pos].Start, 6).SequenceEqual("global".AsSpan())))
                then
                    pos + 1
                else
                    pos

            if k0 >= count || tokens[k0].Kind <> TokenKind.UsingKeyword then
                -1
            else
                let mutable k = k0 + 1
                let mutable hasStatic = false
                let mutable hasUnsafe = false

                while k < count
                      && (tokens[k].Kind = TokenKind.StaticKeyword
                          || tokens[k].Kind = TokenKind.UnsafeKeyword) do
                    if tokens[k].Kind = TokenKind.StaticKeyword then
                        hasStatic <- true
                    else
                        hasUnsafe <- true

                    k <- k + 1

                let mutable hasAlias = false

                if
                    k + 1 < count
                    && tokens[k + 1].Kind = TokenKind.EqualsToken
                    && (tokens[k].Kind = TokenKind.IdentifierToken
                        || (tokens[k].Kind >= TokenKind.YieldKeyword
                            && tokens[k].Kind <= TokenKind.SafeKeyword
                            && tokens[k].Kind <> TokenKind.GlobalKeyword))
                then
                    hasAlias <- true
                    k <- k + 2

                if (hasAlias && hasStatic) || (hasUnsafe && not hasAlias && not hasStatic) then
                    -1
                else
                    let mutable valid = true
                    let mutable ltDepth = 0
                    let mutable parenDepth = 0
                    let mutable bracketDepth = 0
                    let mutable targetToks = 0
                    let mutable prevNameTok = false

                    while valid && k < count && tokens[k].Kind <> TokenKind.SemicolonToken do
                        let tok = tokens[k]
                        let tk = tok.Kind

                        if tok.Length <= 0 && tk <> TokenKind.OmittedArraySizeExpressionToken then
                            valid <- false
                        else
                            match tk with
                            | TokenKind.IdentifierToken
                            | TokenKind.GlobalKeyword ->
                                if
                                    not hasAlias
                                    && ltDepth = 0
                                    && parenDepth = 0
                                    && bracketDepth = 0
                                    && prevNameTok
                                then
                                    valid <- false
                                else
                                    prevNameTok <- true
                            | TokenKind.ManagedKeyword
                            | TokenKind.UnmanagedKeyword
                            | TokenKind.UnderscoreToken
                            | TokenKind.BoolKeyword
                            | TokenKind.ByteKeyword
                            | TokenKind.SByteKeyword
                            | TokenKind.ShortKeyword
                            | TokenKind.UShortKeyword
                            | TokenKind.IntKeyword
                            | TokenKind.UIntKeyword
                            | TokenKind.LongKeyword
                            | TokenKind.ULongKeyword
                            | TokenKind.DoubleKeyword
                            | TokenKind.FloatKeyword
                            | TokenKind.DecimalKeyword
                            | TokenKind.StringKeyword
                            | TokenKind.CharKeyword
                            | TokenKind.VoidKeyword
                            | TokenKind.ObjectKeyword ->
                                if not hasAlias && ltDepth = 0 then
                                    valid <- false
                                else
                                    prevNameTok <- true
                            | TokenKind.DotToken
                            | TokenKind.ColonColonToken -> prevNameTok <- false
                            | TokenKind.CommaToken ->
                                if ltDepth > 0 || parenDepth > 0 || bracketDepth > 0 then
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | TokenKind.LessThanToken ->
                                ltDepth <- ltDepth + 1
                                prevNameTok <- false
                            | TokenKind.GreaterThanToken
                            | TokenKind.GreaterThanGreaterThanToken
                            | TokenKind.GreaterThanGreaterThanGreaterThanToken ->
                                let w = greaterWidth tk

                                if ltDepth >= w then
                                    ltDepth <- ltDepth - w
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | TokenKind.OpenParenToken ->
                                if hasAlias || ltDepth > 0 then
                                    parenDepth <- parenDepth + 1
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | TokenKind.CloseParenToken ->
                                if parenDepth > 0 then
                                    parenDepth <- parenDepth - 1
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | TokenKind.OpenBracketToken ->
                                if hasAlias || ltDepth > 0 then
                                    bracketDepth <- bracketDepth + 1
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | TokenKind.CloseBracketToken ->
                                if bracketDepth > 0 then
                                    bracketDepth <- bracketDepth - 1
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | TokenKind.OmittedArraySizeExpressionToken ->
                                if bracketDepth > 0 then
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | TokenKind.QuestionToken
                            | TokenKind.AsteriskToken
                            | TokenKind.DelegateKeyword
                            | TokenKind.InKeyword
                            | TokenKind.OutKeyword ->
                                if hasAlias || ltDepth > 0 then
                                    prevNameTok <- false
                                else
                                    valid <- false
                            | _ -> valid <- false

                        targetToks <- targetToks + 1
                        k <- k + 1

                    if
                        valid
                        && targetToks > 0
                        && ltDepth = 0
                        && parenDepth = 0
                        && bracketDepth = 0
                        && k < count
                        && tokens[k].Kind = TokenKind.SemicolonToken
                    then
                        k + 1 - pos
                    else
                        -1

        let findUsingRunScopeFromTokens
            (stopAtComment: bool)
            (minCount: int)
            (source: string)
            (i0: int)
            =
            let input = before.LexerBuffer
            let inTokens = input.TokenSpan()
            let countTokens = inTokens.Length
            let srcSpan = source.AsSpan()

            if tokScopeLexId <> lexedTexts || i0 < tokScopePos then
                tokScopeLexId <- lexedTexts
                tokScopePos <- 0
                tokScopeCanUse <- true
                tokScopeCurIsNs <- true
                tokScopeValid <- true
                tokScopeStack.Clear()

            while tokScopeValid && tokScopePos < i0 && tokScopePos < countTokens do
                let tk = inTokens[tokScopePos].Kind

                if tokScopeCanUse then
                    let uLen = tryScanUsingClauseTokens srcSpan inTokens tokScopePos

                    if uLen > 0 then
                        tokScopePos <- tokScopePos + uLen
                    else
                        let eLen = tryScanExternAliasTokens srcSpan inTokens tokScopePos

                        if eLen > 0 then
                            tokScopePos <- tokScopePos + eLen
                        elif tk = TokenKind.NamespaceKeyword then
                            let struct (nsLen, isBrace) =
                                tryScanNamespaceHeader inTokens tokScopePos

                            if nsLen > 0 then
                                if isBrace then
                                    tokScopeStack.Add tokScopeCurIsNs
                                    tokScopeCurIsNs <- true
                                    tokScopeCanUse <- true

                                tokScopePos <- tokScopePos + nsLen
                            else
                                tokScopeCanUse <- false
                                tokScopeValid <- false
                        elif tk = TokenKind.CloseBraceToken then
                            if tokScopeStack.Count > 0 then
                                let last = tokScopeStack.Count - 1
                                tokScopeCurIsNs <- tokScopeStack[last]
                                tokScopeStack.RemoveAt last
                                tokScopeCanUse <- false
                                tokScopePos <- tokScopePos + 1
                            else
                                tokScopeValid <- false
                        else
                            tokScopeCanUse <- false

                            if tk = TokenKind.OpenBraceToken then
                                tokScopeStack.Add tokScopeCurIsNs
                                tokScopeCurIsNs <- false

                            tokScopePos <- tokScopePos + 1
                else if tokScopeCurIsNs && tk = TokenKind.NamespaceKeyword then
                    let struct (nsLen, isBrace) = tryScanNamespaceHeader inTokens tokScopePos

                    if nsLen > 0 && isBrace then
                        tokScopeStack.Add tokScopeCurIsNs
                        tokScopeCurIsNs <- true
                        tokScopeCanUse <- true
                        tokScopePos <- tokScopePos + nsLen
                    else
                        tokScopePos <- tokScopePos + 1
                elif tk = TokenKind.OpenBraceToken then
                    tokScopeStack.Add tokScopeCurIsNs
                    tokScopeCurIsNs <- false
                    tokScopePos <- tokScopePos + 1
                elif tk = TokenKind.CloseBraceToken then
                    if tokScopeStack.Count > 0 then
                        let last = tokScopeStack.Count - 1
                        tokScopeCurIsNs <- tokScopeStack[last]
                        tokScopeStack.RemoveAt last
                        tokScopeCanUse <- false
                        tokScopePos <- tokScopePos + 1
                    else
                        tokScopeValid <- false
                else
                    tokScopePos <- tokScopePos + 1

            if not tokScopeValid || not tokScopeCanUse || tokScopePos <> i0 then
                struct (false, 0, 0)
            else
                let mutable count = 0
                let mutable totalTokens = 0
                let mutable q = i0
                let mutable keepGoing = true

                while keepGoing && q < countTokens do
                    let cLen = tryScanUsingClauseTokens srcSpan inTokens q

                    if cLen <= 0 then
                        keepGoing <- false
                    elif
                        stopAtComment
                        && count > 0
                        && not (
                            nonCommentRunIsLayoutOnly
                                input
                                inTokens[q].TriviaStart
                                inTokens[q].LeadingCount
                        )
                    then
                        keepGoing <- false
                    else
                        if count >= inUsingLengths.Length then
                            inUsingLengths <- grownIndices inUsingLengths (count + 1)

                        inUsingLengths[count] <- cLen
                        count <- count + 1
                        totalTokens <- totalTokens + cLen
                        q <- q + cLen

                if count < minCount then
                    struct (false, 0, 0)
                else
                    struct (true, count, totalTokens)

        let findUsingRunScope (stopAtComment: bool) (minCount: int) (source: string) (i0: int) =
            let input = before.LexerBuffer

            if not beforeBuilt || before.NodeCount = 0 then
                findUsingRunScopeFromTokens stopAtComment minCount source i0
            elif not before.IsComplete then
                struct (false, 0, 0)
            else
                let targetStart = (input.Token i0).Start
                let pIdx = findBeforeTokenAt targetStart
                let mutable scopeIdx = if pIdx >= 0 then before.RootIndex else -1
                let mutable foundScope = -1
                let mutable startSlot = -1
                let mutable searching = scopeIdx >= 0

                while searching do
                    let scopeNode = before.Node scopeIdx

                    if not (holdsUsings scopeNode.Kind) then
                        searching <- false
                    else
                        let slot = findChildSlotContainingToken scopeNode pIdx

                        if slot < 0 then
                            searching <- false
                        else
                            let c = before.Child(scopeNode.ChildStart + slot)

                            if c < 0 then
                                searching <- false
                            else
                                let cn = before.Node c

                                if cn.Kind = NodeKind.UsingDirective && cn.TokenStart = pIdx then
                                    foundScope <- scopeIdx
                                    startSlot <- slot
                                    searching <- false
                                elif holdsUsings cn.Kind then
                                    scopeIdx <- c
                                else
                                    searching <- false

                if foundScope < 0 then
                    struct (false, 0, 0)
                else
                    let scopeNode = before.Node foundScope

                    let declStart = if scopeNode.Kind = NodeKind.CompilationUnit then 0 else 3

                    let mutable validScope = startSlot >= declStart
                    let mutable seenMemberOrAttr = false

                    for s = declStart to scopeNode.ChildCount - 1 do
                        if validScope then
                            let c = before.Child(scopeNode.ChildStart + s)

                            if c < 0 then
                                if s < startSlot then
                                    validScope <- false
                            else
                                let k = (before.Node c).Kind

                                if k = NodeKind.UsingDirective then
                                    if seenMemberOrAttr then
                                        validScope <- false
                                elif k <> NodeKind.ExternAliasDirective then
                                    seenMemberOrAttr <- true

                                    if s < startSlot then
                                        validScope <- false

                    let mutable endSlot = startSlot
                    let mutable inRun = true

                    while validScope && inRun && endSlot < scopeNode.ChildCount do
                        let c = before.Child(scopeNode.ChildStart + endSlot)

                        if c >= 0 && (before.Node c).Kind = NodeKind.UsingDirective then
                            let uNode = before.Node c
                            let firstTok = before.Token uNode.TokenStart

                            if
                                stopAtComment
                                && endSlot > startSlot
                                && not (
                                    nonCommentRunIsLayoutOnly
                                        input
                                        firstTok.TriviaStart
                                        firstTok.LeadingCount
                                )
                            then
                                inRun <- false
                            else
                                endSlot <- endSlot + 1
                        else
                            inRun <- false

                    let count = endSlot - startSlot

                    if not validScope || count < minCount then
                        struct (false, 0, 0)
                    else
                        inUsingLengths <- grownIndices inUsingLengths count
                        let mutable totalTokens = 0
                        let mutable s = startSlot

                        while validScope && s < endSlot do
                            let uNode = before.Node(before.Child(scopeNode.ChildStart + s))

                            if not (DeclaredTransformations.isValidUsingDirective before uNode) then
                                validScope <- false
                            else
                                let firstExpectedTok = before.Token uNode.TokenStart

                                let lastExpectedTok =
                                    before.Token(uNode.TokenStart + uNode.TokenCount - 1)

                                let clauseStart = i0 + totalTokens

                                if
                                    clauseStart >= input.TokenCount
                                    || (input.Token clauseStart).Start <> firstExpectedTok.Start
                                then
                                    validScope <- false
                                else
                                    let mutable inLen = 0
                                    let mutable foundSemi = false

                                    while validScope
                                          && not foundSemi
                                          && clauseStart + inLen < input.TokenCount do
                                        let inTok = input.Token(clauseStart + inLen)

                                        inLen <- inLen + 1

                                        if inTok.Kind = TokenKind.SemicolonToken then
                                            foundSemi <- true

                                            validScope <- inTok.End = lastExpectedTok.End
                                        elif inTok.End >= lastExpectedTok.End then
                                            validScope <- false

                                    if not foundSemi then
                                        validScope <- false
                                    else
                                        inUsingLengths[s - startSlot] <- inLen
                                        totalTokens <- totalTokens + inLen

                            s <- s + 1

                        struct (validScope, count, totalTokens)

        let pairUsingClauses
            (srcSpan: ReadOnlySpan<char>)
            (formatted: ReadOnlySpan<char>)
            (i0: int)
            (j0: int)
            (count: int)
            (totalTokens: int)
            (allowSplitClosers: bool)
            (requireGlobalPartition: bool)
            (pairedOut: int array)
            (outTotalTokens: outref<int>)
            =
            let input = before.LexerBuffer
            let output = after.LexerBuffer
            childSlots <- grownIndices childSlots count
            usingSlots <- grownIndices usingSlots count

            let mutable outClauses = 0
            let mutable clauseStart = j0
            let mutable pos = 0
            let mutable sawOrdinary = false

            let outLimit =
                if allowSplitClosers then
                    output.TokenCount - 1 - j0
                else
                    min totalTokens (output.TokenCount - j0)

            let mutable scanningOut = true

            while scanningOut && pos < outLimit && outClauses <= count do
                let tk = (output.Token(j0 + pos)).Kind

                if tk = TokenKind.OpenBraceToken || tk = TokenKind.CloseBraceToken then
                    scanningOut <- false
                elif tk = TokenKind.SemicolonToken then
                    if outClauses < count then
                        let firstOut = output.Token clauseStart

                        if requireGlobalPartition then
                            let isOutGlobal =
                                firstOut.Kind = TokenKind.GlobalKeyword
                                || (firstOut.Kind = TokenKind.IdentifierToken
                                    && firstOut.Length = 6
                                    && formatted
                                        .Slice(firstOut.Start, 6)
                                        .SequenceEqual("global".AsSpan()))

                            if not isOutGlobal then
                                sawOrdinary <- true
                            elif sawOrdinary then
                                outClauses <- count

                    if outClauses < count then
                        childSlots[outClauses] <- clauseStart
                        usingSlots[outClauses] <- j0 + pos + 1 - clauseStart

                    outClauses <- outClauses + 1
                    clauseStart <- j0 + pos + 1

                    if allowSplitClosers && outClauses = count then
                        scanningOut <- false

                pos <- pos + 1

            let outSpanTokens = clauseStart - j0
            outTotalTokens <- outSpanTokens

            if outClauses <> count || (not allowSplitClosers && outSpanTokens <> totalTokens) then
                false
            else
                let hasPlacementInfo =
                    input.HasNonCommentContent
                    || output.HasNonCommentContent
                    || input.HasComments
                    || output.HasComments

                if hasPlacementInfo then
                    usingFramesBefore <- grownIndices usingFramesBefore count
                    usingSegmentsBefore <- grownIndices usingSegmentsBefore count
                    usingIgnoresBefore <- grownIndices usingIgnoresBefore count
                    usingFramesAfter <- grownIndices usingFramesAfter count
                    usingSegmentsAfter <- grownIndices usingSegmentsAfter count
                    usingIgnoresAfter <- grownIndices usingIgnoresAfter count

                    inUsingPlacementCursor.Fill(
                        input,
                        srcSpan,
                        true,
                        i0,
                        inUsingLengths,
                        childSlots,
                        count,
                        usingFramesBefore,
                        usingSegmentsBefore,
                        usingIgnoresBefore
                    )

                    outUsingPlacementCursor.Fill(
                        output,
                        formatted,
                        false,
                        i0,
                        inUsingLengths,
                        childSlots,
                        count,
                        usingFramesAfter,
                        usingSegmentsAfter,
                        usingIgnoresAfter
                    )

                let inline hashPlacement (tokHash: int) (frame: int) (ctx: int) =
                    let mutable h = uint32 tokHash
                    h <- (h ^^^ (uint32 frame + 0x9e3779b9u)) * 16777619u
                    h <- (h ^^^ uint32 ctx) * 16777619u
                    int (h &&& 0x7FFFFFFFu)

                let mutable bucketCount = 64

                while bucketCount < count * 2 do
                    bucketCount <- bucketCount <<< 1

                usingBuckets <- grownIndices usingBuckets bucketCount
                usingNext <- grownIndices usingNext count
                Array.fill usingBuckets 0 bucketCount -1
                let bucketMask = bucketCount - 1

                for c = count - 1 downto 0 do
                    let h = hashUsingClauseSpan formatted output childSlots[c] usingSlots[c]

                    let b =
                        (if hasPlacementInfo then
                             hashPlacement h usingFramesAfter[c] usingSegmentsAfter[c]
                         else
                             h)
                        &&& bucketMask

                    usingNext[c] <- usingBuckets[b]
                    usingBuckets[b] <- c

                usingTaken <- grownFlags usingTaken count
                Array.fill usingTaken 0 count false
                let mutable matchedAll = true
                let mutable remaining = count

                for phase = 0 to 4 do
                    if matchedAll && remaining > 0 then
                        let mutable inCursor = i0
                        let mutable slot = 0

                        while matchedAll && slot < count do
                            let inLen = inUsingLengths[slot]

                            if not usingTaken[slot] then
                                let inIgn = if hasPlacementInfo then usingIgnoresBefore[slot] else 0

                                let inPhase =
                                    match phase with
                                    | 0 -> inIgn = 0 || inIgn = 1
                                    | 1
                                    | 2 -> inIgn = 3
                                    | 3 -> inIgn = 2
                                    | _ -> true

                                if inPhase then
                                    let inFrame =
                                        if hasPlacementInfo then usingFramesBefore[slot] else -1

                                    let inCtx =
                                        if hasPlacementInfo then usingSegmentsBefore[slot] else 0

                                    let h = hashUsingClauseSpan srcSpan input inCursor inLen

                                    let b =
                                        (if hasPlacementInfo then
                                             hashPlacement h inFrame inCtx
                                         else
                                             h)
                                        &&& bucketMask

                                    let mutable prev = -1
                                    let mutable c = usingBuckets[b]
                                    let mutable found = -1
                                    let mutable deferredByIgnore = false

                                    while found < 0 && c >= 0 do
                                        let next = usingNext[c]
                                        let outLen = usingSlots[c]

                                        let placementOk =
                                            not hasPlacementInfo
                                            || (inFrame = usingFramesAfter[c]
                                                && inCtx = usingSegmentsAfter[c])

                                        if placementOk && (allowSplitClosers || outLen = inLen) then
                                            let outStart = childSlots[c]
                                            let mutable eq = true
                                            let mutable ti = 0
                                            let mutable tj = 0

                                            while eq && ti < inLen && tj < outLen do
                                                let a = input.Token(inCursor + ti)
                                                let bTok = output.Token(outStart + tj)

                                                if
                                                    allowSplitClosers
                                                    && greaterWidth a.Kind > 0
                                                    && greaterWidth bTok.Kind > 0
                                                then
                                                    let mutable inGt = greaterWidth a.Kind
                                                    let mutable outGt = greaterWidth bTok.Kind

                                                    while eq && inGt <> outGt do
                                                        if inGt < outGt then
                                                            ti <- ti + 1

                                                            if ti >= inLen then
                                                                eq <- false
                                                            else
                                                                let w =
                                                                    greaterWidth
                                                                        (input.Token(inCursor + ti))
                                                                            .Kind

                                                                if w = 0 then
                                                                    eq <- false
                                                                else
                                                                    inGt <- inGt + w
                                                        else
                                                            tj <- tj + 1

                                                            if tj >= outLen then
                                                                eq <- false
                                                            else
                                                                let w =
                                                                    greaterWidth
                                                                        (output.Token(outStart + tj))
                                                                            .Kind

                                                                if w = 0 then
                                                                    eq <- false
                                                                else
                                                                    outGt <- outGt + w

                                                    ti <- ti + 1
                                                    tj <- tj + 1
                                                else
                                                    eq <-
                                                        a.Kind = bTok.Kind
                                                        && a.Length = bTok.Length
                                                        && sameTokenTextSpan
                                                            srcSpan
                                                            &a
                                                            formatted
                                                            &bTok

                                                    ti <- ti + 1
                                                    tj <- tj + 1

                                            if eq && ti = inLen && tj = outLen then
                                                let ignOk =
                                                    if not hasPlacementInfo then
                                                        true
                                                    else
                                                        let outIgn = usingIgnoresAfter[c]

                                                        match phase with
                                                        | 0
                                                        | 1
                                                        | 3 -> inIgn = outIgn
                                                        | 2 -> outIgn = 2 || outIgn = 0
                                                        | _ -> true

                                                if ignOk then
                                                    found <- c

                                                    if not (isNull pairedOut) then
                                                        pairedOut[slot] <- c

                                                    if prev < 0 then
                                                        usingBuckets[b] <- next
                                                    else
                                                        usingNext[prev] <- next
                                                else
                                                    deferredByIgnore <- true

                                        if found < 0 then
                                            prev <- c
                                            c <- next

                                    if found >= 0 then
                                        usingTaken[slot] <- true
                                        remaining <- remaining - 1
                                    elif phase < 4 && deferredByIgnore then
                                        ()
                                    else
                                        matchedAll <- false

                            inCursor <- inCursor + inLen
                            slot <- slot + 1

                matchedAll

        let tryStepUsingRun
            (allowConditional: bool)
            (source: string)
            (formatted: ReadOnlySpan<char>)
            (curI: int)
            (curJ: int)
            =
            let input = before.LexerBuffer
            let output = after.LexerBuffer
            let mutable offset = 0

            while offset < 64
                  && curI - offset > 0
                  && (let prev = (input.Token(curI - offset - 1)).Kind in

                      prev <> TokenKind.SemicolonToken
                      && prev <> TokenKind.OpenBraceToken
                      && prev <> TokenKind.CloseBraceToken) do
                offset <- offset + 1

            let i0 = curI - offset
            let j0 = curJ - offset

            let startsUsing =
                offset < 64
                && j0 >= 0
                && i0 < input.TokenCount
                && (let first = input.Token i0 in

                    first.Kind = TokenKind.UsingKeyword
                    || (first.Kind = TokenKind.IdentifierToken
                        && first.Length = 6
                        && i0 + 1 < input.TokenCount
                        && (input.Token(i0 + 1)).Kind = TokenKind.UsingKeyword))

            if not startsUsing then
                struct (false, curI, curJ)
            else
                let struct (validScope, count, totalTokens) = findUsingRunScope true 2 source i0

                if
                    not validScope
                    || count < 2
                    || i0 + totalTokens > input.TokenCount
                    || j0 + totalTokens > output.TokenCount
                then
                    struct (false, curI, curJ)
                else
                    let mutable layoutOk = true
                    let mutable k = 0

                    while layoutOk && k < totalTokens do
                        let inTok = input.Token(i0 + k)
                        let outTok = output.Token(j0 + k)

                        layoutOk <-
                            (if k = 0 then
                                 inTok.LeadingCount = 0 && outTok.LeadingCount = 0
                                 || nonCommentTriviaRunsAgreeSpan
                                     allowConditional
                                     (source.AsSpan())
                                     formatted
                                     input
                                     output
                                     inTok.TriviaStart
                                     inTok.LeadingCount
                                     outTok.TriviaStart
                                     outTok.LeadingCount
                             else
                                 nonCommentRunIsLayoutOnly
                                     input
                                     inTok.TriviaStart
                                     inTok.LeadingCount
                                 && nonCommentRunIsLayoutOnly
                                     output
                                     outTok.TriviaStart
                                     outTok.LeadingCount)
                            && nonCommentRunIsLayoutOnly
                                input
                                (inTok.TriviaStart + inTok.LeadingCount)
                                inTok.TrailingCount
                            && nonCommentRunIsLayoutOnly
                                output
                                (outTok.TriviaStart + outTok.LeadingCount)
                                outTok.TrailingCount

                        k <- k + 1

                    let mutable ignoredOutTokens = 0

                    if
                        not layoutOk
                        || not (
                            pairUsingClauses
                                (source.AsSpan())
                                formatted
                                i0
                                j0
                                count
                                totalTokens
                                false
                                true
                                null
                                &ignoredOutTokens
                        )
                    then
                        struct (false, curI, curJ)
                    else
                        struct (true, i0 + totalTokens, j0 + totalTokens)

        let lexerModifierKindSpan (text: ReadOnlySpan<char>) (tok: Token) =
            if DeclaredTransformations.isModifierTokenKind tok.Kind then
                tok.Kind
            elif tok.Kind = TokenKind.IdentifierToken then
                let span = text.Slice(tok.Start, tok.Length)

                if span.SequenceEqual("async".AsSpan()) then
                    TokenKind.AsyncKeyword
                elif span.SequenceEqual("partial".AsSpan()) then
                    TokenKind.PartialKeyword
                elif span.SequenceEqual("required".AsSpan()) then
                    TokenKind.RequiredKeyword
                elif span.SequenceEqual("file".AsSpan()) then
                    TokenKind.FileKeyword
                else
                    TokenKind.None
            else
                TokenKind.None

        let findSortableModifierDecl (source: string) (targetStart: int) =
            if not (ensureBeforeParsed source) then
                struct (-1, 0, 0, -1)
            else
                let pIdx = findBeforeTokenAt targetStart
                let mutable currIdx = if pIdx >= 0 then before.RootIndex else -1
                let mutable foundDecl = -1
                let mutable beforeStart = 0
                let mutable beforeCount = 0
                let mutable modOffset = -1

                while currIdx >= 0 && foundDecl < 0 do
                    let currNode = before.Node currIdx

                    if
                        DeclaredTransformations.isSortableDeclarationKind currNode.Kind
                        && currNode.Kind <> NodeKind.IncompleteMember
                        && currNode.Kind <> NodeKind.GlobalStatement
                    then
                        let struct (mStart, mCount) =
                            DeclaredTransformations.leadingModifierSlice before currNode

                        if mCount >= 2 then
                            let firstTok = before.Token ~~~(before.Child mStart)
                            let lastTok = before.Token ~~~(before.Child(mStart + mCount - 1))

                            if targetStart >= firstTok.Start && targetStart < lastTok.End then
                                for s = 0 to mCount - 1 do
                                    if
                                        (before.Token ~~~(before.Child(mStart + s))).Start =
                                            targetStart
                                    then
                                        foundDecl <- currIdx
                                        beforeStart <- mStart
                                        beforeCount <- mCount
                                        modOffset <- s

                    if foundDecl < 0 then
                        let slot = findChildSlotContainingToken currNode pIdx

                        if slot >= 0 then
                            let c = before.Child(currNode.ChildStart + slot)
                            currIdx <- if c >= 0 then c else -1
                        else
                            currIdx <- -1

                struct (foundDecl, beforeStart, beforeCount, modOffset)

        let tryStepModifierRun
            (source: string)
            (formatted: ReadOnlySpan<char>)
            (curI: int)
            (curJ: int)
            =
            let input = before.LexerBuffer
            let output = after.LexerBuffer
            let srcSpan = source.AsSpan()

            if
                lexerModifierKindSpan srcSpan (input.Token curI) = TokenKind.None
                || lexerModifierKindSpan formatted (output.Token curJ) = TokenKind.None
            then
                struct (false, curI, curJ)
            else
                let struct (foundDecl, beforeStart, beforeCount, modOffset) =
                    findSortableModifierDecl source (input.Token curI).Start

                let i0 = curI - modOffset
                let j0 = curJ - modOffset

                if
                    foundDecl < 0
                    || modOffset < 0
                    || i0 < 0
                    || j0 < 0
                    || i0 + beforeCount >= input.TokenCount
                    || j0 + beforeCount >= output.TokenCount
                    || (i0 > 0
                        && lexerModifierKindSpan srcSpan (input.Token(i0 - 1)) <> TokenKind.None)
                    || (j0 > 0
                        && lexerModifierKindSpan formatted (output.Token(j0 - 1)) <> TokenKind.None)
                    || lexerModifierKindSpan srcSpan (input.Token(i0 + beforeCount))
                       <> TokenKind.None
                    || lexerModifierKindSpan formatted (output.Token(j0 + beforeCount))
                       <> TokenKind.None
                then
                    struct (false, curI, curJ)
                else
                    let beforeNode = before.Node foundDecl
                    let isLocal = beforeNode.Kind = NodeKind.LocalFunctionStatement

                    let parentKind =
                        if beforeNode.Parent >= 0 then
                            (before.Node beforeNode.Parent).Kind
                        else
                            NodeKind.None

                    let mutable valid =
                        not isLocal
                        || ((parentKind = NodeKind.Block || parentKind = NodeKind.GlobalStatement)
                            && beforeStart + beforeCount <
                                beforeNode.ChildStart + beforeNode.ChildCount
                            && before.Child(beforeStart + beforeCount) >= 0)

                    let isTypeDecl = DeclaredTransformations.isTypeDeclarationKind beforeNode.Kind

                    let plain (kind: TokenKind) =
                        DeclaredTransformations.isPositionIndependentModifier kind
                        || kind = TokenKind.AsyncKeyword

                    let mutable runCarriesStationaryWord = false
                    let mutable runCarriesPartial = false

                    for s = 0 to beforeCount - 1 do
                        if valid then
                            let expectedTok = before.Token ~~~(before.Child(beforeStart + s))

                            let bTok = input.Token(i0 + s)
                            let aTok = output.Token(j0 + s)
                            let bModKind = lexerModifierKindSpan srcSpan bTok
                            let aModKind = lexerModifierKindSpan formatted aTok

                            if
                                bTok.Start <> expectedTok.Start
                                || bTok.End <> expectedTok.End
                                || bModKind <> expectedTok.Kind
                                || aModKind = TokenKind.None
                            then
                                valid <- false
                            else
                                if not (plain bModKind) || not (plain aModKind) then
                                    runCarriesStationaryWord <- true

                                if
                                    bModKind = TokenKind.PartialKeyword
                                    || aModKind = TokenKind.PartialKeyword
                                then
                                    runCarriesPartial <- true

                    for s = 0 to beforeCount - 1 do
                        if valid then
                            let bModKind = lexerModifierKindSpan srcSpan (input.Token(i0 + s))

                            let aModKind = lexerModifierKindSpan formatted (output.Token(j0 + s))

                            if
                                isTypeDecl
                                && (bModKind = TokenKind.ExternKeyword
                                    || aModKind = TokenKind.ExternKeyword)
                            then
                                valid <- false
                            elif isLocal then
                                let permitted (kind: TokenKind) =
                                    kind = TokenKind.AsyncKeyword
                                    || kind = TokenKind.StaticKeyword
                                    || kind = TokenKind.UnsafeKeyword
                                    || kind = TokenKind.ExternKeyword

                                if not (permitted bModKind && permitted aModKind) then
                                    valid <- false
                            elif bModKind = aModKind && s = beforeCount - 1 then
                                ()
                            else
                                let asyncMovable =
                                    beforeNode.Kind = NodeKind.MethodDeclaration
                                    && not runCarriesStationaryWord

                                let fileMovable = isTypeDecl && not runCarriesPartial

                                let movable (kind: TokenKind) =
                                    DeclaredTransformations.isPositionIndependentModifier kind
                                    || (kind = TokenKind.AsyncKeyword && asyncMovable)
                                    || (kind = TokenKind.FileKeyword && fileMovable)

                                if not (movable bModKind && movable aModKind) then
                                    valid <- false

                    if valid then
                        let firstBefore = input.Token i0
                        let firstAfter = output.Token j0
                        let mutable ti = firstBefore.TriviaStart
                        let tiEnd = firstBefore.TriviaStart + firstBefore.LeadingCount
                        let mutable tj = firstAfter.TriviaStart
                        let tjEnd = firstAfter.TriviaStart + firstAfter.LeadingCount

                        while valid && (ti < tiEnd || tj < tjEnd) do
                            while ti < tiEnd && not (contentTrivia (input.Trivia ti).Kind) do
                                ti <- ti + 1

                            while tj < tjEnd && not (contentTrivia (output.Trivia tj).Kind) do
                                tj <- tj + 1

                            if ti < tiEnd && tj < tjEnd then
                                let lt = input.Trivia ti
                                let rt = output.Trivia tj

                                valid <-
                                    lt.Kind = rt.Kind
                                    && commentTrivia lt.Kind
                                    && CommentContent.equivalentSpan srcSpan lt formatted rt

                                ti <- ti + 1
                                tj <- tj + 1
                            elif ti < tiEnd || tj < tjEnd then
                                valid <- false

                        for s = 0 to beforeCount - 1 do
                            if valid then
                                let bTok = input.Token(i0 + s)
                                let aTok = output.Token(j0 + s)

                                if s > 0 then
                                    for t = bTok.TriviaStart to bTok.TriviaStart + bTok.LeadingCount
                                                                - 1 do
                                        if contentTrivia (input.Trivia t).Kind then
                                            valid <- false

                                    for t = aTok.TriviaStart to aTok.TriviaStart + aTok.LeadingCount
                                                                - 1 do
                                        if contentTrivia (output.Trivia t).Kind then
                                            valid <- false

                                let bTrail = bTok.TriviaStart + bTok.LeadingCount

                                for t = bTrail to bTrail + bTok.TrailingCount - 1 do
                                    if contentTrivia (input.Trivia t).Kind then
                                        valid <- false

                                let aTrail = aTok.TriviaStart + aTok.LeadingCount

                                for t = aTrail to aTrail + aTok.TrailingCount - 1 do
                                    if contentTrivia (output.Trivia t).Kind then
                                        valid <- false

                    if not valid then
                        struct (false, curI, curJ)
                    else
                        usingTaken <- grownFlags usingTaken beforeCount
                        Array.fill usingTaken 0 beforeCount false
                        let mutable matchedAll = true
                        let mutable s = 0

                        while matchedAll && s < beforeCount do
                            let bTok = input.Token(i0 + s)
                            let mutable found = -1
                            let mutable c = 0

                            while found < 0 && c < beforeCount do
                                if not usingTaken[c] then
                                    let aTok = output.Token(j0 + c)

                                    if
                                        bTok.Kind = aTok.Kind
                                        && bTok.Length = aTok.Length
                                        && sameTokenTextSpan srcSpan &bTok formatted &aTok
                                    then
                                        found <- c

                                c <- c + 1

                            if found < 0 then
                                matchedAll <- false
                            else
                                usingTaken[found] <- true
                                s <- s + 1

                        if matchedAll then
                            struct (true, i0 + beforeCount, j0 + beforeCount)
                        else
                            struct (false, curI, curJ)

        let isGreaterRun (kind: TokenKind) =
            kind = TokenKind.GreaterThanToken
            || kind = TokenKind.GreaterThanGreaterThanToken
            || kind = TokenKind.GreaterThanGreaterThanGreaterThanToken

        let isTypeCloserInBefore (tokIdx: int) =
            let mutable currIdx = before.RootIndex
            let mutable found = false

            while currIdx >= 0 && not found do
                let currNode = before.Node currIdx

                if
                    (currNode.Kind = NodeKind.TypeArgumentList
                     || currNode.Kind = NodeKind.TypeParameterList
                     || currNode.Kind = NodeKind.FunctionPointerParameterList)
                    && currNode.ChildCount >= 2
                    && before.Child(currNode.ChildStart + currNode.ChildCount - 1) = ~~~tokIdx
                then
                    found <- true
                else
                    let slot = findChildSlotContainingToken currNode tokIdx

                    if slot >= 0 then
                        let c = before.Child(currNode.ChildStart + slot)
                        currIdx <- if c >= 0 then c else -1
                    else
                        currIdx <- -1

            found

        let tryStepSplitTypeClosers
            (allowConditional: bool)
            (source: string)
            (formatted: ReadOnlySpan<char>)
            (curI: int)
            (curJ: int)
            =
            let input = before.LexerBuffer
            let output = after.LexerBuffer
            let firstIn = input.Token curI
            let firstOut = output.Token curJ

            if
                not (isGreaterRun firstIn.Kind)
                || not (isGreaterRun firstOut.Kind)
                || firstIn.Length = firstOut.Length
            then
                struct (false, curI, curJ)
            else
                let mutable inCount = 1
                let mutable outCount = 1
                let mutable inChars = firstIn.Length
                let mutable outChars = firstOut.Length
                let mutable canAdvance = true

                while canAdvance && inChars <> outChars && inChars <= 6 && outChars <= 6 do
                    if inChars < outChars then
                        if
                            curI + inCount < input.TokenCount
                            && isGreaterRun (input.Token(curI + inCount)).Kind
                        then
                            inChars <- inChars + (input.Token(curI + inCount)).Length
                            inCount <- inCount + 1
                        else
                            canAdvance <- false
                    else if
                        curJ + outCount < output.TokenCount
                        && isGreaterRun (output.Token(curJ + outCount)).Kind
                    then
                        outChars <- outChars + (output.Token(curJ + outCount)).Length
                        outCount <- outCount + 1
                    else
                        canAdvance <- false

                if inChars <> outChars || inChars < 2 || inChars > 6 then
                    struct (false, curI, curJ)
                else
                    let lastIn = input.Token(curI + inCount - 1)
                    let lastOut = output.Token(curJ + outCount - 1)

                    let nonAdjacent =
                        (firstIn.Start = 0
                         || (let c = source[firstIn.Start - 1] in c <> '>' && c <> '-' && c <> '='))
                        && (firstOut.Start = 0
                            || (let c = formatted[firstOut.Start - 1] in
                                c <> '>' && c <> '-' && c <> '='))
                        && (lastIn.End >= source.Length
                            || (let c = source[lastIn.End] in c <> '>' && c <> '='))
                        && (lastOut.End >= formatted.Length
                            || (let c = formatted[lastOut.End] in c <> '>' && c <> '='))

                    if not nonAdjacent then
                        struct (false, curI, curJ)
                    else
                        let srcSpan = source.AsSpan()

                        let mutable triviaOk =
                            (firstIn.LeadingCount = 0 && firstOut.LeadingCount = 0
                             || nonCommentTriviaRunsAgreeSpan
                                 allowConditional
                                 srcSpan
                                 formatted
                                 input
                                 output
                                 firstIn.TriviaStart
                                 firstIn.LeadingCount
                                 firstOut.TriviaStart
                                 firstOut.LeadingCount)
                            && (lastIn.TrailingCount = 0 && lastOut.TrailingCount = 0
                                || nonCommentTriviaRunsAgreeSpan
                                    allowConditional
                                    srcSpan
                                    formatted
                                    input
                                    output
                                    (lastIn.TriviaStart + lastIn.LeadingCount)
                                    lastIn.TrailingCount
                                    (lastOut.TriviaStart + lastOut.LeadingCount)
                                    lastOut.TrailingCount)

                        for k = 0 to inCount - 1 do
                            if triviaOk then
                                let tok = input.Token(curI + k)

                                if k > 0 then
                                    triviaOk <-
                                        nonCommentRunIsLayoutOnly
                                            input
                                            tok.TriviaStart
                                            tok.LeadingCount

                                if triviaOk && k < inCount - 1 then
                                    triviaOk <-
                                        nonCommentRunIsLayoutOnly
                                            input
                                            (tok.TriviaStart + tok.LeadingCount)
                                            tok.TrailingCount

                        for k = 0 to outCount - 1 do
                            if triviaOk then
                                let tok = output.Token(curJ + k)

                                if k > 0 then
                                    triviaOk <-
                                        nonCommentRunIsLayoutOnly
                                            output
                                            tok.TriviaStart
                                            tok.LeadingCount

                                if triviaOk && k < outCount - 1 then
                                    triviaOk <-
                                        nonCommentRunIsLayoutOnly
                                            output
                                            (tok.TriviaStart + tok.LeadingCount)
                                            tok.TrailingCount

                        if not triviaOk || not (ensureBeforeParsed source) then
                            struct (false, curI, curJ)
                        else
                            let pIdx = findBeforeTokenAt firstIn.Start

                            if pIdx < 0 || pIdx + inChars > before.TokenCount then
                                struct (false, curI, curJ)
                            else
                                let mutable allClosers = true
                                let mutable pOffset = 0

                                for t = 0 to inCount - 1 do
                                    let inTok = input.Token(curI + t)

                                    for c = 0 to inTok.Length - 1 do
                                        if allClosers then
                                            let pt = before.Token(pIdx + pOffset)

                                            allClosers <-
                                                pt.Kind = TokenKind.GreaterThanToken
                                                && pt.Length = 1
                                                && pt.Start = inTok.Start + c
                                                && isTypeCloserInBefore (pIdx + pOffset)

                                            pOffset <- pOffset + 1

                                if allClosers then
                                    struct (true, curI + inCount, curJ + outCount)
                                else
                                    struct (false, curI, curJ)

        let tryStepPermutedRun
            (allowConditional: bool)
            (source: string)
            (formatted: ReadOnlySpan<char>)
            (witness: TransformationWitness)
            (curI: int)
            (curJ: int)
            =
            let struct (steppedClosers, cI, cJ) =
                tryStepSplitTypeClosers allowConditional source formatted curI curJ

            if steppedClosers then
                struct (true, cI, cJ)
            else
                let struct (steppedUsing, uI, uJ) =
                    if witness.SortedUsings then
                        tryStepUsingRun allowConditional source formatted curI curJ
                    else
                        struct (false, curI, curJ)

                if steppedUsing then
                    struct (true, uI, uJ)
                elif witness.SortedModifiers then
                    tryStepModifierRun source formatted curI curJ
                else
                    struct (false, curI, curJ)

        let lexicallyEqual (source: string) (formatted: string) =
            lastLexicalSource <- source
            lastLexicalFormatted <- formatted
            lastLexicalBefore <- before
            lastLexicalId <- lexedTexts

            let struct (same, prefix) =
                lexicallyEqualBuffers
                    (source.AsSpan())
                    (formatted.AsSpan())
                    before.LexerBuffer
                    after.LexerBuffer

            lastLexicalPrefix <- prefix
            same

        let disabledRunsAgree (source: string) (formatted: string) =
            let input = before.LexerBuffer
            let output = after.LexerBuffer

            if not input.HasDisabledText && not output.HasDisabledText then
                true
            else
                let inline isWhiteSpace (c: char) =
                    if int c <= 32 then
                        c = ' ' || c = '\n' || c = '\r' || c = '\t' || c = '\v' || c = '\f'
                    else
                        Char.IsWhiteSpace c

                let exactNonWhitespaceEqual
                    (leftText: string)
                    aStart
                    aLen
                    (rightText: string)
                    bStart
                    bLen
                    =
                    if
                        aLen = bLen
                        && leftText
                            .AsSpan(aStart, aLen)
                            .SequenceEqual(rightText.AsSpan(bStart, bLen))
                    then
                        true
                    else
                        let aEnd = aStart + aLen
                        let bEnd = bStart + bLen
                        let mutable i = aStart
                        let mutable j = bStart
                        let mutable matched = true
                        let mutable scanning = true

                        while scanning do
                            while i < aEnd && isWhiteSpace leftText[i] do
                                i <- i + 1

                            while j < bEnd && isWhiteSpace rightText[j] do
                                j <- j + 1

                            if i < aEnd && j < bEnd then
                                if leftText[i] = rightText[j] then
                                    i <- i + 1
                                    j <- j + 1
                                else
                                    matched <- false
                                    scanning <- false
                            else
                                matched <- i >= aEnd && j >= bEnd
                                scanning <- false

                        matched

                let sortedPlainUsingLinesEqual
                    (leftText: string)
                    aStart
                    aLen
                    (rightText: string)
                    bStart
                    bLen
                    =
                    let collectPlainUsings (text: string) start len =
                        let items = ResizeArray<string>()
                        let finish = start + len
                        let mutable pos = start
                        let mutable valid = true

                        while valid && pos < finish do
                            let mutable lineEnd = pos

                            while lineEnd < finish && text[lineEnd] <> '\n' && text[lineEnd] <> '\r' do
                                lineEnd <- lineEnd + 1

                            let mutable s = pos

                            while s < lineEnd && isWhiteSpace text[s] do
                                s <- s + 1

                            let mutable e = lineEnd

                            while e > s && isWhiteSpace text[e - 1] do
                                e <- e - 1

                            if s < e then
                                let span = text.AsSpan(s, e - s)

                                if
                                    not (
                                        span.StartsWith("using".AsSpan(), StringComparison.Ordinal)
                                    )
                                then
                                    valid <- false
                                elif span.Length <= 6 || not (isWhiteSpace span[5]) then
                                    valid <- false
                                elif span[span.Length - 1] <> ';' then
                                    valid <- false
                                else
                                    let sb = StringBuilder()
                                    let mutable k = 5
                                    let mutable needIdent = false

                                    while k < span.Length - 1 do
                                        let ch = span[k]

                                        if isWhiteSpace ch then
                                            k <- k + 1
                                        elif ch = '.' then
                                            if needIdent then
                                                valid <- false
                                                k <- span.Length
                                            else
                                                sb.Append('.') |> ignore
                                                needIdent <- true
                                                k <- k + 1
                                        elif Char.IsLetterOrDigit ch || ch = '_' then
                                            sb.Append ch |> ignore
                                            needIdent <- false
                                            k <- k + 1
                                        else
                                            valid <- false
                                            k <- span.Length

                                    if valid && not needIdent && sb.Length > 0 then
                                        items.Add(sb.ToString())
                                    else
                                        valid <- false

                            if lineEnd < finish && text[lineEnd] = '\r' then
                                lineEnd <- lineEnd + 1

                            if lineEnd < finish && text[lineEnd] = '\n' then
                                lineEnd <- lineEnd + 1

                            pos <- lineEnd

                        if valid && items.Count >= 2 then
                            Some(items.ToArray())
                        else
                            None

                    match
                        collectPlainUsings leftText aStart aLen,
                        collectPlainUsings rightText bStart bLen
                    with
                    | Some leftItems, Some rightItems when leftItems.Length = rightItems.Length ->
                        Array.Sort(leftItems, StringComparer.Ordinal)
                        Array.Sort(rightItems, StringComparer.Ordinal)
                        let mutable idx = 0
                        let mutable equal = true

                        while equal && idx < leftItems.Length do
                            equal <-
                                String.Equals(
                                    leftItems[idx],
                                    rightItems[idx],
                                    StringComparison.Ordinal
                                )

                            idx <- idx + 1

                        equal
                    | _ -> false

                let nextWithContent (buf: TokenBuffer) (text: string) index =
                    let trivia = buf.TriviaSpan()
                    let limit = min trivia.Length (buf.LastNonCommentTrivia + 1)
                    let mutable i = index
                    let mutable found = false

                    while not found && i < limit do
                        while i < limit && trivia[i].Kind <> TriviaKind.DisabledTextTrivia do
                            i <- i + 1

                        if i < limit then
                            let item = trivia[i]
                            let mutable j = item.Start
                            let finish = item.Start + item.Length

                            while j < finish && isWhiteSpace text[j] do
                                j <- j + 1

                            if j < finish then found <- true else i <- i + 1

                    if found then i else trivia.Length

                let inputTrivia = input.TriviaSpan()
                let outputTrivia = output.TriviaSpan()

                let struct (startLeft, startRight) =
                    if
                        lastLexicalId = lexedTexts
                        && Object.ReferenceEquals(lastLexicalSource, source)
                        && Object.ReferenceEquals(lastLexicalFormatted, formatted)
                        && Object.ReferenceEquals(lastLexicalBefore, before)
                        && lastLexicalPrefix > 0
                        && lastLexicalPrefix < input.TokenCount
                        && lastLexicalPrefix < output.TokenCount
                    then
                        struct ((input.Token lastLexicalPrefix).TriviaStart,
                                (output.Token lastLexicalPrefix).TriviaStart)
                    else
                        struct (0, 0)

                let deferStart = deferredDisabledSpans.Count
                let mutable left = nextWithContent input source startLeft
                let mutable right = nextWithContent output formatted startRight
                let mutable same = true

                while same && (left < inputTrivia.Length || right < outputTrivia.Length) do
                    if left >= inputTrivia.Length || right >= outputTrivia.Length then
                        same <- false
                    else
                        let a = inputTrivia[left]
                        let b = outputTrivia[right]

                        if
                            not (
                                exactNonWhitespaceEqual
                                    source
                                    a.Start
                                    a.Length
                                    formatted
                                    b.Start
                                    b.Length
                            )
                        then
                            if allowDisabledDeferral then
                                addDeferredDisabledSpan (
                                    struct (source,
                                            disabledDeferralPrefix,
                                            a.Start - disabledDeferralPrefix,
                                            a.Start + a.Length - disabledDeferralPrefix,
                                            b.Start - disabledDeferralPrefix,
                                            b.Start + b.Length - disabledDeferralPrefix)
                                )
                            elif
                                not (
                                    sortedPlainUsingLinesEqual
                                        source
                                        a.Start
                                        a.Length
                                        formatted
                                        b.Start
                                        b.Length
                                )
                            then
                                same <- false

                        left <- nextWithContent input source (left + 1)
                        right <- nextWithContent output formatted (right + 1)

                if not same && deferredDisabledSpans.Count > deferStart then
                    truncateDeferredDisabledSpans deferStart

                same

        [<MethodImpl(MethodImplOptions.NoInlining)>]
        member private _.MatchExtendedToken
            (
                allowConditional: bool,
                options: PrinterOptions,
                source: string,
                formatted: string,
                witness: TransformationWitness,
                left: Token,
                right: Token
            ) =
            if
                left.Kind = TokenKind.InterpolatedStringToken
                && (not allowConditional
                    || source.AsSpan(left.Start, left.Length).IndexOfAny('#', '/') < 0)
            then
                if interpolatedStringsLexicallyEqual true source left formatted right then
                    true
                elif witness.ReindentedRawStrings then
                    reindentedInterpolatedStringsEqual options source left formatted right
                else
                    false
            elif
                witness.ReindentedRawStrings
                && (left.Kind = TokenKind.MultiLineRawStringLiteralToken
                    || left.Kind = TokenKind.Utf8MultiLineRawStringLiteralToken)
                && DeclaredTransformations.isValidRawStringReindentation
                    options
                    source
                    left
                    formatted
                    right
            then
                true
            elif
                DeclaredTransformations.isValidLiteralLineEndingChange
                    options
                    source
                    left
                    formatted
                    right
            then
                true
            else
                false

        [<MethodImpl(MethodImplOptions.NoInlining)>]
        member private _.CheckNonCommentTokenTrivia
            (
                allowConditional: bool,
                source: string,
                formatted: ReadOnlySpan<char>,
                input: TokenBuffer,
                output: TokenBuffer,
                left: inref<Token>,
                right: inref<Token>,
                lastLeftNonComment: int,
                lastRightNonComment: int,
                nextLeftContent: byref<int>,
                nextRightContent: byref<int>
            ) =
            let inputTrivia = input.TriviaSpan()
            let outputTrivia = output.TriviaSpan()
            let srcSpan = source.AsSpan()
            let leftEnd = left.TriviaStart + left.LeadingCount + left.TrailingCount
            let rightEnd = right.TriviaStart + right.LeadingCount + right.TrailingCount

            let matched =
                ((((left.LeadingCount ||| right.LeadingCount) = 0)
                  || (nonCommentLayoutOnlyRun
                          allowConditional
                          inputTrivia
                          left.TriviaStart
                          left.LeadingCount
                      && nonCommentLayoutOnlyRun
                          allowConditional
                          outputTrivia
                          right.TriviaStart
                          right.LeadingCount))
                 || nonCommentTriviaRunsAgreeSpan
                     allowConditional
                     srcSpan
                     formatted
                     input
                     output
                     left.TriviaStart
                     left.LeadingCount
                     right.TriviaStart
                     right.LeadingCount)
                && ((((left.TrailingCount ||| right.TrailingCount) = 0)
                     || (nonCommentLayoutOnlyRun
                             allowConditional
                             inputTrivia
                             (left.TriviaStart + left.LeadingCount)
                             left.TrailingCount
                         && nonCommentLayoutOnlyRun
                             allowConditional
                             outputTrivia
                             (right.TriviaStart + right.LeadingCount)
                             right.TrailingCount))
                    || nonCommentTriviaRunsAgreeSpan
                        allowConditional
                        srcSpan
                        formatted
                        input
                        output
                        (left.TriviaStart + left.LeadingCount)
                        left.TrailingCount
                        (right.TriviaStart + right.LeadingCount)
                        right.TrailingCount)

            if matched then
                if leftEnd > nextLeftContent then
                    if leftEnd > lastLeftNonComment then
                        nextLeftContent <- inputTrivia.Length
                    else
                        nextLeftContent <- leftEnd

                        while nextLeftContent <= lastLeftNonComment
                              && not (
                                  nonCommentContentTriviaForProof
                                      allowConditional
                                      inputTrivia[nextLeftContent].Kind
                              ) do
                            nextLeftContent <- nextLeftContent + 1

                        if nextLeftContent > lastLeftNonComment then
                            nextLeftContent <- inputTrivia.Length

                if rightEnd > nextRightContent then
                    if rightEnd > lastRightNonComment then
                        nextRightContent <- outputTrivia.Length
                    else
                        nextRightContent <- rightEnd

                        while nextRightContent <= lastRightNonComment
                              && not (
                                  nonCommentContentTriviaForProof
                                      allowConditional
                                      outputTrivia[nextRightContent].Kind
                              ) do
                            nextRightContent <- nextRightContent + 1

                        if nextRightContent > lastRightNonComment then
                            nextRightContent <- outputTrivia.Length

            matched

        [<MethodImpl(MethodImplOptions.NoInlining)>]
        member private _.TryStepMismatch
            (
                allowConditional: bool,
                source: string,
                formatted: ReadOnlySpan<char>,
                witness: TransformationWitness,
                noNonCommentContent: bool,
                closingsState: byref<int>,
                usedExtendedProof: byref<bool>,
                i: byref<int>,
                j: byref<int>
            ) =
            let input = before.LexerBuffer
            let output = after.LexerBuffer
            let inputTokens = input.TokenSpan()
            let outputTokens = output.TokenSpan()
            let inputTrivia = input.TriviaSpan()
            let left = &inputTokens[i]
            let right = &outputTokens[j]
            let mutable state = closingsState

            let inline ensureClosings (minStart: int) =
                if not witness.ChangedTrailingCommas then
                    false
                else
                    if state = 0 then
                        if separatorClosings.EnsureCapacity 0 > 16384 then
                            separatorClosings <- Dictionary<int, struct (int * bool * bool)>()

                        state <-
                            if
                                ensureBeforeParsed source
                                && DeclaredTransformations.tryListClosingsFromTree
                                    before
                                    separatorClosings
                                    minStart
                            then
                                1
                            else
                                -1

                    state > 0

            let matched =
                if
                    left.Kind <> right.Kind
                    && right.Kind = TokenKind.CommaToken
                    && j + 1 < outputTokens.Length
                    && i > 0
                    && j > 0
                    && ensureClosings left.Start
                then
                    let closing = &outputTokens[j + 1]
                    let previousSource = &inputTokens[i - 1]
                    let previousOutput = &outputTokens[j - 1]

                    match separatorClosings.TryGetValue left.Start with
                    | true, struct (lastEnd, true, _) when
                        closing.Kind = left.Kind
                        && (left.Kind = TokenKind.CloseBraceToken
                            || left.Kind = TokenKind.CloseBracketToken)
                        && previousSource.End = lastEnd
                        && right.Length = 1
                        && DeclaredTransformations.hasBreakSpan
                            formatted
                            previousOutput.End
                            closing.Start
                        && layoutOnlyRun inputTrivia left.TriviaStart left.LeadingCount
                        && (noNonCommentContent
                            || (nonCommentRunIsLayoutOnly
                                    output
                                    right.TriviaStart
                                    right.LeadingCount
                                && nonCommentRunIsLayoutOnly
                                    output
                                    (right.TriviaStart + right.LeadingCount)
                                    right.TrailingCount))
                        ->
                        j <- j + 1
                        true
                    | _ -> false
                elif
                    left.Kind <> right.Kind
                    && left.Kind = TokenKind.CommaToken
                    && i + 1 < inputTokens.Length
                    && i > 0
                    && j > 0
                    && ensureClosings left.Start
                then
                    let closing = &inputTokens[i + 1]
                    let previousSource = &inputTokens[i - 1]
                    let previousOutput = &outputTokens[j - 1]

                    match separatorClosings.TryGetValue closing.Start with
                    | true, struct (lastEnd, _, true) when
                        closing.Kind = right.Kind
                        && (closing.Kind = TokenKind.CloseBraceToken
                            || closing.Kind = TokenKind.CloseBracketToken
                            || closing.Kind = TokenKind.CloseParenToken)
                        && previousSource.End = lastEnd
                        && left.Length = 1
                        && not (
                            DeclaredTransformations.hasBreakSpan
                                formatted
                                previousOutput.End
                                right.Start
                        )
                        && layoutOnlyRun
                            inputTrivia
                            (left.TriviaStart + left.LeadingCount)
                            left.TrailingCount
                        && layoutOnlyRun inputTrivia closing.TriviaStart closing.LeadingCount
                        && (noNonCommentContent
                            || (nonCommentRunIsLayoutOnly input left.TriviaStart left.LeadingCount
                                && nonCommentRunIsLayoutOnly
                                    input
                                    (left.TriviaStart + left.LeadingCount)
                                    left.TrailingCount))
                        ->
                        i <- i + 1
                        true
                    | _ -> false
                else
                    let struct (stepped, nextI, nextJ) =
                        tryStepPermutedRun allowConditional source formatted witness i j

                    usedExtendedProof <- true
                    i <- nextI
                    j <- nextJ
                    stepped

            closingsState <- state
            matched

        [<MethodImpl(MethodImplOptions.NoInlining)>]
        member private _.FinishExtendedProof
            (
                allowConditional: bool,
                noNonCommentContent: bool,
                source: string,
                lastLeftNonComment: int
            ) =
            if not (ensureBeforeParsed source) then
                false
            elif not allowConditional && not noNonCommentContent then
                let inputTrivia = before.LexerBuffer.TriviaSpan()
                let mutable ok = true
                let mutable idx = 0

                while ok && idx <= lastLeftNonComment do
                    let item = inputTrivia[idx]

                    match item.Kind with
                    | TriviaKind.BadDirectiveTrivia
                    | TriviaKind.LineSpanDirectiveTrivia
                    | TriviaKind.PragmaChecksumDirectiveTrivia
                    | TriviaKind.ReferenceDirectiveTrivia
                    | TriviaKind.LoadDirectiveTrivia
                    | TriviaKind.IgnoredDirectiveTrivia
                    | TriviaKind.SkippedTokensTrivia
                    | TriviaKind.ConflictMarkerTrivia -> ok <- false
                    | TriviaKind.ShebangDirectiveTrivia -> ok <- isValidShebang source &item
                    | kind when directive kind ->
                        let finish = item.Start + item.Length
                        let span = source.AsSpan(item.Start, item.Length)

                        let codeSpan =
                            if
                                kind = TriviaKind.RegionDirectiveTrivia
                                || kind = TriviaKind.EndRegionDirectiveTrivia
                            then
                                ReadOnlySpan<char>.Empty
                            else
                                match span.IndexOf("//".AsSpan(), StringComparison.Ordinal) with
                                | commentIndex when commentIndex >= 0 -> span.Slice(0, commentIndex)
                                | _ -> span

                        ok <-
                            item.Length > 0
                            && (finish = source.Length || isNewLine source[finish - 1])
                            && codeSpan.IndexOfAny('"', '\'') < 0
                            && not (span.Contains("/*".AsSpan(), StringComparison.Ordinal))
                    | _ -> ()

                    idx <- idx + 1

                ok
            else
                true

        member private this.SeparatorsOnlyEqualSpan
            (
                allowConditional: bool,
                options: PrinterOptions,
                source: string,
                formatted: ReadOnlySpan<char>,
                cachedFormatted: byref<string>,
                witness: TransformationWitness
            ) =
            let input = before.LexerBuffer
            let output = after.LexerBuffer

            if
                (not allowConditional
                 && (not (singleConfiguration input)
                     || not (singleConfiguration output)
                     || not (ensureBeforeParsed source)))
                || DeclaredTransformations.hasMalformedTrivia input
                || DeclaredTransformations.hasMalformedTrivia output
            then
                false
            else
                let noNonCommentContent =
                    not input.HasNonCommentContent && not output.HasNonCommentContent

                let mutable closingsState = 0
                let inputTokens = input.TokenSpan()
                let outputTokens = output.TokenSpan()
                let inputTrivia = input.TriviaSpan()
                let outputTrivia = output.TriviaSpan()
                let srcSpan = source.AsSpan()

                let startIdx =
                    if
                        lastLexicalId = lexedTexts
                        && Object.ReferenceEquals(lastLexicalSource, source)
                        && Object.ReferenceEquals(lastLexicalBefore, before)
                        && (if not (isNull cachedFormatted) then
                                Object.ReferenceEquals(lastLexicalFormatted, cachedFormatted)
                            else
                                isNull lastLexicalFormatted && afterLexedSpanId = lexedTexts)
                    then
                        lastLexicalPrefix
                    else
                        0

                let canSkipCondSuffix =
                    allowConditional
                    && curWindowedPairId = lexedTexts
                    && pinnedSuffixLexicallyEqual
                    && curSrcSuffixTok >= 0
                    && curFmtSuffixTok >= 0

                let lastLeftNonComment = input.LastNonCommentTrivia
                let lastRightNonComment = output.LastNonCommentTrivia

                let mutable nextLeftContent =
                    if lastLeftNonComment < 0 then
                        inputTrivia.Length
                    elif startIdx < inputTokens.Length then
                        let s = inputTokens[startIdx].TriviaStart

                        if s > lastLeftNonComment then inputTrivia.Length else s
                    else
                        inputTrivia.Length

                if nextLeftContent <= lastLeftNonComment then
                    while nextLeftContent <= lastLeftNonComment
                          && not (
                              nonCommentContentTriviaForProof
                                  allowConditional
                                  inputTrivia[nextLeftContent].Kind
                          ) do
                        nextLeftContent <- nextLeftContent + 1

                    if nextLeftContent > lastLeftNonComment then
                        nextLeftContent <- inputTrivia.Length

                let mutable nextRightContent =
                    if lastRightNonComment < 0 then
                        outputTrivia.Length
                    elif startIdx < outputTokens.Length then
                        let s = outputTokens[startIdx].TriviaStart

                        if s > lastRightNonComment then outputTrivia.Length else s
                    else
                        outputTrivia.Length

                if nextRightContent <= lastRightNonComment then
                    while nextRightContent <= lastRightNonComment
                          && not (
                              nonCommentContentTriviaForProof
                                  allowConditional
                                  outputTrivia[nextRightContent].Kind
                          ) do
                        nextRightContent <- nextRightContent + 1

                    if nextRightContent > lastRightNonComment then
                        nextRightContent <- outputTrivia.Length

                let mutable usedExtendedProof = false
                let mutable ok = true
                let mutable i = startIdx
                let mutable j = startIdx

                while ok && i < inputTokens.Length && j < outputTokens.Length do
                    if
                        canSkipCondSuffix
                        && i >= curSrcSuffixTok + 1
                        && inputTokens.Length - i = outputTokens.Length - j
                        && i - curSrcSuffixTok = j - curFmtSuffixTok
                    then
                        i <- inputTokens.Length
                        j <- outputTokens.Length
                    else
                        let left = &inputTokens[i]
                        let right = &outputTokens[j]

                        if left.Kind = right.Kind then
                            let mutable matched =
                                left.Kind <> TokenKind.BadToken
                                && (if
                                        left.Length = right.Length
                                        && sameTokenTextSpan srcSpan &left formatted &right
                                    then
                                        true
                                    else
                                        if isNull cachedFormatted then
                                            let s = String formatted
                                            cachedFormatted <- s
                                            this.BindLexedFormatted s

                                        let ext =
                                            this.MatchExtendedToken(
                                                allowConditional,
                                                options,
                                                source,
                                                cachedFormatted,
                                                witness,
                                                left,
                                                right
                                            )

                                        if ext then
                                            usedExtendedProof <- true

                                        ext)
                                && (left.Kind <> TokenKind.GreaterThanGreaterThanGreaterThanToken
                                    || let leftAdj =
                                        i + 1 < inputTokens.Length
                                        && inputTokens[i + 1].Start = left.End
                                        && inputTokens[i + 1].LeadingCount = 0 in

                                       let rightAdj =
                                           j + 1 < outputTokens.Length
                                           && outputTokens[j + 1].Start = right.End
                                           && outputTokens[j + 1].LeadingCount = 0 in

                                       leftAdj = rightAdj)

                            if matched && not noNonCommentContent then
                                let leftEnd =
                                    left.TriviaStart + left.LeadingCount + left.TrailingCount

                                let rightEnd =
                                    right.TriviaStart + right.LeadingCount + right.TrailingCount

                                if leftEnd > nextLeftContent || rightEnd > nextRightContent then
                                    matched <-
                                        this.CheckNonCommentTokenTrivia(
                                            allowConditional,
                                            source,
                                            formatted,
                                            input,
                                            output,
                                            &left,
                                            &right,
                                            lastLeftNonComment,
                                            lastRightNonComment,
                                            &nextLeftContent,
                                            &nextRightContent
                                        )

                            if matched then
                                i <- i + 1
                                j <- j + 1

                                if not allowConditional && not usedExtendedProof && i = j then
                                    lastLexicalPrefix <- i
                            else
                                ok <-
                                    this.TryStepMismatch(
                                        allowConditional,
                                        source,
                                        formatted,
                                        witness,
                                        noNonCommentContent,
                                        &closingsState,
                                        &usedExtendedProof,
                                        &i,
                                        &j
                                    )
                        else
                            ok <-
                                this.TryStepMismatch(
                                    allowConditional,
                                    source,
                                    formatted,
                                    witness,
                                    noNonCommentContent,
                                    &closingsState,
                                    &usedExtendedProof,
                                    &i,
                                    &j
                                )

                if usedExtendedProof && ok && i = inputTokens.Length && j = outputTokens.Length then
                    ok <-
                        this.FinishExtendedProof(
                            allowConditional,
                            noNonCommentContent,
                            source,
                            lastLeftNonComment
                        )

                ok && i = inputTokens.Length && j = outputTokens.Length

        member private this.SeparatorsOnlyEqual
            (
                allowConditional: bool,
                options: PrinterOptions,
                source: string,
                formatted: string,
                witness: TransformationWitness
            ) =
            let mutable cached = formatted

            this.SeparatorsOnlyEqualSpan(
                allowConditional,
                options,
                source,
                formatted.AsSpan(),
                &cached,
                witness
            )

        member _.CheckAndNormalizeWith
            (
                options: PrinterOptions,
                rules: DeclaredTransformations.Rule list,
                filePath: string,
                source: string,
                formatted: string,
                ?witness: TransformationWitness
            ) : Result<string, string> =
            let witness = defaultArg witness TransformationWitness.Searched
            fullyProvenSource <- null
            fullyProvenFormatted <- null
            agreedSource <- null
            agreedFormatted <- null
            beforeLexedFor <- null
            afterLexedSpanId <- -1
            sepDeclinedSpanId <- -1
            curWindowedPairId <- -1
            before <- ownedBefore
            parseText source before
            parseText formatted after
            let struct (preserved, _) = agree source formatted

            if preserved then
                Ok source
            else
                DeclaredTransformations.seedParsedPair source before formatted after false

                let mutable expected = source

                try
                    for rule in rules do
                        if rule.Witnessed witness then
                            expected <- rule.RewriteInput options expected formatted

                    if not (DeclaredTransformations.isParsedInSeededBefore expected before) then
                        parseText expected before
                finally
                    DeclaredTransformations.clearSeededPair ()

                let struct (same, index) = agree expected formatted

                if same then
                    Ok expected
                else
                    let declarations =
                        if List.isEmpty rules then
                            "none"
                        else
                            rules |> List.map (fun rule -> rule.Name) |> String.concat ", "

                    Error
                        $"{filePath}: token {index}: undeclared token transformation (expected count={before.TokenCount}, formatted count={after.TokenCount}; declared transformations: {declarations}).\n  expected: {describe expected before index}\n  formatted: {describe formatted after index}"

        member this.CheckWith(options, rules, filePath, source, formatted, ?witness) =
            this.CheckAndNormalizeWith(
                options,
                rules,
                filePath,
                source,
                formatted,
                ?witness = witness
            )
            |> Result.map ignore

        member this.CheckAndNormalize(options, filePath, source, formatted) =
            this.CheckAndNormalizeWith(
                options,
                DeclaredTransformations.rules,
                filePath,
                source,
                formatted
            )

        member this.Normalize
            (
                options: PrinterOptions,
                source: string,
                formatted: string,
                ?sourceTree: SyntaxTree,
                ?witness: TransformationWitness,
                ?symbols: string array,
                ?allowDirectProof: bool
            ) =
            let parsedTree =
                match sourceTree with
                | Some parsed -> parsed
                | None -> Unchecked.defaultof<SyntaxTree>

            let w =
                match witness with
                | Some v -> v
                | None -> TransformationWitness.Searched

            let syms =
                match symbols with
                | Some v -> v
                | None -> Array.empty

            let allowDirect =
                match allowDirectProof with
                | Some v -> v
                | None -> false

            this.NormalizeDirect(options, source, formatted, parsedTree, w, syms, allowDirect)

        member internal _.ClearPinnedConditionalPair() =
            pinnedCondSource <- null
            pinnedCondFormatted <- null
            pinnedSourceBuf <- savedDefaultBeforeBuf
            pinnedFormattedBuf <- savedDefaultAfterBuf
            pinnedSourceWin <- Unchecked.defaultof<_>
            pinnedFormattedWin <- Unchecked.defaultof<_>
            pinnedDefaultLexPrefix <- 0
            pinnedSourceCleanDirectives <- false
            pinnedFormattedCleanDirectives <- false
            pinnedSuffixLexicallyEqual <- false
            curWindowedPairId <- -1

        member internal this.PinDefaultConditionalPair
            (source: string, formatted: string, sourceTree: SyntaxTree)
            =
            this.ClearPinnedConditionalPair()

            let srcOrigin =
                if usableSourceTree sourceTree then
                    sourceTree.LexerBuffer
                else
                    before.LexerBuffer

            if
                Object.ReferenceEquals(afterLexedFor, formatted)
                && afterLexedSymbols.Length = 0
                && (not (singleConfiguration srcOrigin)
                    || not (singleConfiguration after.LexerBuffer))
            then

                if after.LexerBuffer.IsVerifyOnly then
                    let tokHint = after.LexerBuffer.TokenCount + 32
                    let trivHint = (after.LexerBuffer.TokenCount <<< 1) + 64
                    Parser.lexOnlyHinted tokHint trivHint formatted after

                let srcWin = Lexer.buildConditionalWindow srcOrigin
                let fmtWin = Lexer.buildConditionalWindow after.LexerBuffer

                if srcWin.Valid || fmtWin.Valid then
                    savedDefaultBeforeBuf.CopyAllFrom srcOrigin
                    savedDefaultAfterBuf.CopyAllFrom after.LexerBuffer
                    pinnedCondSource <- source
                    pinnedCondFormatted <- formatted
                    pinnedSourceBuf <- savedDefaultBeforeBuf
                    pinnedFormattedBuf <- savedDefaultAfterBuf
                    pinnedSourceWin <- srcWin
                    pinnedFormattedWin <- fmtWin

                    pinnedDefaultLexPrefix <-
                        if
                            lastLexicalId = lexedTexts
                            && Object.ReferenceEquals(lastLexicalSource, source)
                            && Object.ReferenceEquals(lastLexicalFormatted, formatted)
                            && Object.ReferenceEquals(lastLexicalBefore, before)
                        then
                            lastLexicalPrefix
                        else
                            0

                    pinnedSourceCleanDirectives <-
                        cleanBufferDirectives source savedDefaultBeforeBuf

                    pinnedFormattedCleanDirectives <-
                        cleanBufferDirectives formatted savedDefaultAfterBuf

                    pinnedSuffixLexicallyEqual <-
                        srcWin.Valid
                        && fmtWin.Valid
                        && srcWin.SuffixScanStart < Int32.MaxValue
                        && fmtWin.SuffixScanStart < Int32.MaxValue
                        && lexicallyEqualSuffixRange
                            (source.AsSpan())
                            (formatted.AsSpan())
                            savedDefaultBeforeBuf
                            srcWin.SuffixTokenIndex
                            savedDefaultAfterBuf
                            fmtWin.SuffixTokenIndex

        member internal this.NormalizeDirect
            (
                options: PrinterOptions,
                source: string,
                formatted: string,
                sourceTree: SyntaxTree,
                witness: TransformationWitness,
                syms: string array,
                allowDirectProof: bool
            ) =
            fullyProvenSource <- null
            fullyProvenFormatted <- null
            provenSource <- null
            agreedSource <- null
            agreedFormatted <- null
            afterLexedSpanId <- -1

            let alreadyDeclinedDirect =
                syms.Length = 0
                && Object.ReferenceEquals(sepDeclinedSource, source)
                && Object.ReferenceEquals(sepDeclinedFormatted, formatted)

            sepDeclinedSource <- null
            sepDeclinedFormatted <- null
            sepDeclinedSpanId <- -1

            if usableSourceTree sourceTree then
                before <- sourceTree
                beforeBuilt <- true
            else
                before <- ownedBefore

                if
                    Object.ReferenceEquals(beforeLexedFor, source)
                    && Object.ReferenceEquals(beforeLexedSymbols, syms)
                then
                    if not beforeBuilt || before.NodeCount = 0 then
                        buildFromLexed source before
                elif syms.Length > 0 then
                    let aBuf = after.LexerBuffer
                    let tokHint = aBuf.TokenCount + (aBuf.TokenCount >>> 3) + 64
                    let trivHint = aBuf.TriviaCount + (aBuf.TriviaCount >>> 2) + 64
                    parseTextWithHinted syms tokHint trivHint source before
                else
                    let aBuf = after.LexerBuffer
                    let tokHint = aBuf.TokenCount + (aBuf.TokenCount >>> 3) + 64
                    let trivHint = aBuf.TriviaCount + (aBuf.TriviaCount >>> 2) + 64
                    parseTextWithHinted Array.empty tokHint trivHint source before

                beforeBuilt <- true

            beforeLexedFor <- null
            beforeLexedSymbols <- Array.empty

            if
                Object.ReferenceEquals(afterLexedFor, formatted)
                && Object.ReferenceEquals(afterLexedSymbols, syms)
            then
                buildFromLexed formatted after
            elif syms.Length > 0 then
                let bBuf = before.LexerBuffer
                let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                let trivHint =
                    max (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64) (bBuf.TokenCount + 64)

                parseTextWithHinted syms tokHint trivHint formatted after
            else
                let bBuf = before.LexerBuffer
                let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                let trivHint =
                    max (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64) (bBuf.TokenCount + 64)

                parseTextWithHinted Array.empty tokHint trivHint formatted after

            afterLexedFor <- null
            afterLexedSymbols <- Array.empty

            let windowedConfig = syms.Length > 0 && curWindowedPairId = lexedTexts
            let struct (same, _) = agree source formatted

            if same then
                curWindowedPairId <- -1
                agreedSource <- source
                agreedFormatted <- formatted
                source
            elif
                allowDirectProof
                && not alreadyDeclinedDirect
                && before.IsComplete
                && after.IsComplete
                && (if before.TriviaCount = before.LexerBuffer.TriviaCount then
                        if
                            syms.Length = 0
                            && not (isNull pinnedCondSource)
                            && Object.ReferenceEquals(source, pinnedCondSource)
                        then
                            pinnedSourceCleanDirectives
                        elif windowedConfig && pinnedSourceCleanDirectives then
                            cleanBufferDirectivesRange
                                source
                                before.LexerBuffer
                                curSrcPrefixTriv
                                (if curSrcSuffixTriv >= 0 then
                                     curSrcSuffixTriv - 1
                                 else
                                     Int32.MaxValue)
                        else
                            cleanBufferDirectives source before.LexerBuffer
                    else
                        collectDirectives false source before beforeDirectives
                        && not (disabledTextMayOpen (source.AsSpan()) before.LexerBuffer))
                && (if after.TriviaCount = after.LexerBuffer.TriviaCount then
                        if
                            syms.Length = 0
                            && not (isNull pinnedCondFormatted)
                            && Object.ReferenceEquals(formatted, pinnedCondFormatted)
                        then
                            pinnedFormattedCleanDirectives
                        elif windowedConfig && pinnedFormattedCleanDirectives then
                            cleanBufferDirectivesRange
                                formatted
                                after.LexerBuffer
                                curFmtPrefixTriv
                                (if curFmtSuffixTriv >= 0 then
                                     curFmtSuffixTriv - 1
                                 else
                                     Int32.MaxValue)
                        else
                            cleanBufferDirectives formatted after.LexerBuffer
                    else
                        collectDirectives false formatted after afterDirectives
                        && not (disabledTextMayOpen (formatted.AsSpan()) after.LexerBuffer))
                && this.SeparatorsOnlyEqual(true, options, source, formatted, witness)
                && disabledRunsAgree source formatted
            then
                curWindowedPairId <- -1
                fullyProvenSource <- source
                fullyProvenFormatted <- formatted
                source
            else
                curWindowedPairId <- -1

                DeclaredTransformations.seedParsedPairWith
                    syms
                    source
                    before
                    ownedBefore
                    formatted
                    after
                    true

                let mutable expected = source

                try
                    for rule in DeclaredTransformations.rules do
                        if rule.Witnessed witness then
                            expected <- rule.RewriteInput options expected formatted

                    if DeclaredTransformations.isSeededBefore ownedBefore then
                        before <- ownedBefore

                    match
                        DeclaredTransformations.tryTakeSeparatorProof
                            expected
                            before
                            droppedCommas
                            addedCommas
                            commaClosings
                            provenEdits
                    with
                    | null ->
                        if not (DeclaredTransformations.isParsedInSeededBefore expected before) then
                            before <- ownedBefore

                            if syms.Length > 0 then
                                parseTextWith syms expected before
                            else
                                parseText expected before
                    | proven ->
                        provenSource <- proven
                        provenFormatted <- formatted
                        provenRewrite <- null
                        expected <- proven
                finally
                    DeclaredTransformations.clearSeededPair ()

                expected

        member _.NormalizedFallback(expected: string) =
            if Object.ReferenceEquals(expected, provenSource) then
                if isNull provenRewrite then
                    let baseSafe =
                        allowDisabledDeferral
                        && ensureSafeBaselineSuffix provenSource disabledDeferralPrefix

                    provenRewrite <- DeclaredTransformations.rewrite provenSource provenEdits

                    if
                        baseSafe
                        && not (Object.ReferenceEquals(provenRewrite, provenSource))
                        && canPreserveDisabledContext
                            provenSource
                            provenEdits
                            disabledDeferralPrefix
                    then
                        recordSafeChecked provenRewrite disabledDeferralPrefix true

                provenRewrite
            else
                expected

        member internal _.ParseWork = struct (lexedTexts, builtTrees)

        member internal _.ResetParseWork() =
            lexedTexts <- 0
            builtTrees <- 0
            tokScopeLexId <- -1

        member _.SymbolSets(source: string) = Preprocessor.symbolSets source before

        member _.CombinedIndependentSymbols(source: string, formatted: string) =
            let probeTree () =
                match probe with
                | ValueSome tree -> tree
                | ValueNone ->
                    let tree = SyntaxTree()
                    probe <- ValueSome tree
                    tree

            let parsesStandalone (fragment: string) =
                let tree = probeTree ()
                parseText fragment tree
                tree.IsComplete

            let lexicalBoundary (text: string) =
                text.Contains("/*", StringComparison.Ordinal)

            let scan (text: string) (tree: SyntaxTree) (items: ResizeArray<Trivia>) =
                orderDirectives tree items
                let symbols = ResizeArray<string>()
                let segments = ResizeArray<string>()
                let mutable bodyStart = -1
                let mutable gapStart = 0
                let mutable valid = true
                let mutable index = 0

                while valid && index < items.Count do
                    let item = items[index]

                    if directive item.Kind then
                        let value = text.Substring(item.Start, item.Length).Trim()

                        match item.Kind with
                        | TriviaKind.IfDirectiveTrivia when
                            bodyStart < 0
                            && value.Length > 3
                            && value.StartsWith("#if", StringComparison.Ordinal)
                            && Char.IsWhiteSpace value[3]
                            ->
                            let symbol = value.Substring(3).Trim()

                            valid <-
                                symbol.Length > 0
                                && (Char.IsLetter symbol[0] || symbol[0] = '_')
                                && (symbol
                                    |> Seq.forall (fun character ->
                                        Char.IsLetterOrDigit character || character = '_'))

                            if valid then
                                symbols.Add symbol
                                segments.Add(text.Substring(gapStart, item.Start - gapStart))
                                bodyStart <- item.Start + item.Length
                        | TriviaKind.EndIfDirectiveTrivia when bodyStart >= 0 && value = "#endif" ->
                            segments.Add(text.Substring(bodyStart, item.Start - bodyStart))
                            bodyStart <- -1
                            gapStart <- item.Start + item.Length
                        | _ -> valid <- false

                    index <- index + 1

                if valid && bodyStart < 0 && symbols.Count > 0 then
                    segments.Add(text.Substring(gapStart))

                    if segments |> Seq.forall parsesStandalone then
                        Some(symbols.ToArray())
                    else
                        None
                else
                    None

            if lexicalBoundary source || lexicalBoundary formatted then
                None
            else
                match scan source before beforeDirectives, scan formatted after afterDirectives with
                | Some left, Some right when left = right ->
                    let validCombined (text: string) =
                        let tree = probeTree ()
                        parseTextWith left text tree
                        tree.IsComplete

                    if validCombined source && validCombined formatted then
                        Some left
                    else
                        None
                | _ -> None

        member this.SeparatorsOnlyPreserved
            (
                source: string,
                formatted: string,
                ?witness: TransformationWitness,
                ?options: PrinterOptions
            ) =
            let w =
                match witness with
                | Some v -> v
                | None -> TransformationWitness.Searched

            let opts =
                match options with
                | Some v -> v
                | None -> PrinterOptions.Default

            this.SeparatorsOnlyPreservedDirect(source, formatted, w, opts)

        member internal this.SeparatorsOnlyPreservedDirect
            (
                source: string,
                formatted: string,
                witness: TransformationWitness,
                options: PrinterOptions
            ) =
            let mutable cached = formatted

            this.SeparatorsOnlyPreservedDirectSpan(
                source,
                formatted.AsSpan(),
                &cached,
                witness,
                options
            )

        member internal this.SeparatorsOnlyPreservedDirectSpan
            (
                source: string,
                formatted: ReadOnlySpan<char>,
                cachedFormatted: byref<string>,
                witness: TransformationWitness,
                options: PrinterOptions
            ) =
            sepDeclinedSource <- null
            sepDeclinedFormatted <- null
            sepDeclinedSpanId <- -1

            let validLex =
                if not (isNull cachedFormatted) then
                    Object.ReferenceEquals(afterLexedFor, cachedFormatted)
                else
                    afterLexedSpanId = lexedTexts

            if not validLex then
                false
            else
                beforeBuilt <- true

                let ok =
                    this.SeparatorsOnlyEqualSpan(
                        false,
                        options,
                        source,
                        formatted,
                        &cachedFormatted,
                        witness
                    )

                if
                    not ok
                    && singleConfiguration before.LexerBuffer
                    && singleConfiguration after.LexerBuffer
                then
                    sepDeclinedSource <- source

                    if not (isNull cachedFormatted) then
                        sepDeclinedFormatted <- cachedFormatted
                    else
                        sepDeclinedSpanId <- lexedTexts

                ok

        member this.LexicallyPreserved
            (
                source: string,
                formatted: string,
                ?sourceTree: SyntaxTree,
                ?witness: TransformationWitness
            ) =
            let parsedTree =
                match sourceTree with
                | Some parsed -> parsed
                | None -> Unchecked.defaultof<SyntaxTree>

            let hasWitness, w =
                match witness with
                | Some v -> true, v
                | None -> false, Unchecked.defaultof<TransformationWitness>

            this.LexicallyPreservedDirect(source, formatted, parsedTree, hasWitness, w)

        member internal _.LexicallyPreservedDirect
            (
                source: string,
                formatted: string,
                sourceTree: SyntaxTree,
                hasWitness: bool,
                w: TransformationWitness
            ) =
            fullyProvenSource <- null
            fullyProvenFormatted <- null
            agreedSource <- null
            agreedFormatted <- null
            provenSource <- null
            provenFormatted <- null
            sepDeclinedSource <- null
            sepDeclinedFormatted <- null
            sepDeclinedSpanId <- -1
            afterLexedSpanId <- -1
            curWindowedPairId <- -1
            lastLexicalSource <- null
            lastLexicalFormatted <- null

            beforeLexedFor <- null
            beforeLexedSymbols <- Array.empty

            if usableSourceTree sourceTree then
                before <- sourceTree
            else
                before <- ownedBefore
                parseText source before

            beforeBuilt <- true
            afterLexedFor <- null
            afterLexedSymbols <- Array.empty
            let bBuf = before.LexerBuffer
            let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

            if singleConfiguration bBuf then
                let trivHint =
                    if bBuf.HasComments || bBuf.HasNonCommentContent then
                        max 128 (bBuf.TriviaCount >>> 2)
                    else
                        64

                lexedTexts <- lexedTexts + 1
                Parser.lexOnlyVerifySpan tokHint trivHint (formatted.AsSpan()) after
            else
                let trivHint =
                    max (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64) (bBuf.TokenCount + 64)

                lexTextHinted tokHint trivHint formatted after

            afterLexedFor <- formatted

            let skipComparison =
                hasWitness
                && not (
                    w.SortedUsings
                    && w.SortedModifiers
                    && w.ChangedTrailingCommas
                    && w.ReindentedRawStrings
                )
                && (w.SortedUsings || w.SortedModifiers)
                && singleConfiguration before.LexerBuffer
                && singleConfiguration after.LexerBuffer

            not skipComparison
            && not (disabledTextMayOpen (source.AsSpan()) before.LexerBuffer)
            && not (disabledTextMayOpen (formatted.AsSpan()) after.LexerBuffer)
            && lexicallyEqual source formatted

        member internal _.LexicallyPreservedDirectSpan
            (
                source: string,
                formatted: ReadOnlySpan<char>,
                sourceTree: SyntaxTree,
                hasWitness: bool,
                w: TransformationWitness
            ) =
            fullyProvenSource <- null
            fullyProvenFormatted <- null
            agreedSource <- null
            agreedFormatted <- null
            provenSource <- null
            provenFormatted <- null
            sepDeclinedSource <- null
            sepDeclinedFormatted <- null
            sepDeclinedSpanId <- -1
            afterLexedSpanId <- -1
            curWindowedPairId <- -1
            lastLexicalSource <- null
            lastLexicalFormatted <- null

            beforeLexedFor <- null
            beforeLexedSymbols <- Array.empty

            if usableSourceTree sourceTree then
                before <- sourceTree
            else
                before <- ownedBefore
                parseText source before

            beforeBuilt <- true
            afterLexedFor <- null
            afterLexedSymbols <- Array.empty
            let bBuf = before.LexerBuffer
            let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

            if singleConfiguration bBuf then
                let trivHint =
                    if bBuf.HasComments || bBuf.HasNonCommentContent then
                        max 128 (bBuf.TriviaCount >>> 2)
                    else
                        64

                lexedTexts <- lexedTexts + 1
                Parser.lexOnlyVerifySpan tokHint trivHint formatted after
            else
                let trivHint =
                    max (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64) (bBuf.TokenCount + 64)

                lexedTexts <- lexedTexts + 1
                Parser.lexOnlyHintedSpan tokHint trivHint formatted after

            afterLexedSpanId <- lexedTexts

            let skipComparison =
                hasWitness
                && not (
                    w.SortedUsings
                    && w.SortedModifiers
                    && w.ChangedTrailingCommas
                    && w.ReindentedRawStrings
                )
                && (w.SortedUsings || w.SortedModifiers)
                && singleConfiguration before.LexerBuffer
                && singleConfiguration after.LexerBuffer

            if
                skipComparison
                || disabledTextMayOpen (source.AsSpan()) before.LexerBuffer
                || disabledTextMayOpen formatted after.LexerBuffer
            then
                false
            else
                lastLexicalSource <- source
                lastLexicalFormatted <- null
                lastLexicalBefore <- before
                lastLexicalId <- lexedTexts

                let struct (same, prefix) =
                    lexicallyEqualBuffers
                        (source.AsSpan())
                        formatted
                        before.LexerBuffer
                        after.LexerBuffer

                lastLexicalPrefix <- prefix
                same

        member internal _.BindLexedFormatted(formatted: string) =
            afterLexedFor <- formatted

            if not (isNull lastLexicalSource) && lastLexicalId = lexedTexts then
                lastLexicalFormatted <- formatted

            if sepDeclinedSpanId = lexedTexts && not (isNull sepDeclinedSource) then
                sepDeclinedFormatted <- formatted

        member _.LexicallyPreservedPair(source: string, formatted: string, ?symbols: string array) =
            let syms = defaultArg symbols Array.empty
            fullyProvenSource <- null
            fullyProvenFormatted <- null
            agreedSource <- null
            agreedFormatted <- null
            beforeLexedFor <- null
            afterLexedFor <- null
            beforeLexedSymbols <- Array.empty
            afterLexedSymbols <- Array.empty
            afterLexedSpanId <- -1
            sepDeclinedSpanId <- -1
            curWindowedPairId <- -1
            before <- ownedBefore
            beforeBuilt <- false

            let prevTok = max before.LexerBuffer.TokenCount after.LexerBuffer.TokenCount
            let prevTriv = max before.LexerBuffer.TriviaCount after.LexerBuffer.TriviaCount

            if
                syms.Length > 0
                && Object.ReferenceEquals(source, pinnedCondSource)
                && Object.ReferenceEquals(formatted, pinnedCondFormatted)
            then
                if pinnedSourceWin.Valid then
                    lexedTexts <- lexedTexts + 1

                    let struct (spTok, spTriv, ssTok, ssTriv) =
                        Parser.lexOnlySeededFromDefault
                            syms
                            source
                            pinnedSourceBuf
                            &pinnedSourceWin
                            before

                    curSrcPrefixTok <- spTok
                    curSrcPrefixTriv <- spTriv
                    curSrcSuffixTok <- ssTok
                    curSrcSuffixTriv <- ssTriv
                else
                    if prevTok > 0 then
                        lexTextWithHinted
                            syms
                            (prevTok + (prevTok >>> 4) + 32)
                            (prevTriv + (prevTriv >>> 4) + 64)
                            source
                            before
                    else
                        lexTextWith syms source before

                    curSrcPrefixTok <- 0
                    curSrcPrefixTriv <- 0
                    curSrcSuffixTok <- -1
                    curSrcSuffixTriv <- -1

                if pinnedFormattedWin.Valid then
                    lexedTexts <- lexedTexts + 1

                    let struct (fpTok, fpTriv, fsTok, fsTriv) =
                        Parser.lexOnlySeededFromDefault
                            syms
                            formatted
                            pinnedFormattedBuf
                            &pinnedFormattedWin
                            after

                    curFmtPrefixTok <- fpTok
                    curFmtPrefixTriv <- fpTriv
                    curFmtSuffixTok <- fsTok
                    curFmtSuffixTriv <- fsTriv
                else
                    let bBuf = before.LexerBuffer
                    let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                    let trivHint =
                        max
                            (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64)
                            (bBuf.TokenCount + 64)

                    lexTextWithHinted syms tokHint trivHint formatted after
                    curFmtPrefixTok <- 0
                    curFmtPrefixTriv <- 0
                    curFmtSuffixTok <- -1
                    curFmtSuffixTriv <- -1

                beforeLexedFor <- source
                afterLexedFor <- formatted
                beforeLexedSymbols <- syms
                afterLexedSymbols <- syms
                curWindowedPairId <- lexedTexts

                let startIdx =
                    max 0 (min pinnedDefaultLexPrefix (min curSrcPrefixTok curFmtPrefixTok) - 1)

                let endLimit =
                    if
                        pinnedSuffixLexicallyEqual
                        && curSrcSuffixTok >= 0
                        && curFmtSuffixTok >= 0
                        && before.LexerBuffer.TokenCount = after.LexerBuffer.TokenCount
                        && curSrcSuffixTok = curFmtSuffixTok
                    then
                        curSrcSuffixTok + 1
                    else
                        before.LexerBuffer.TokenCount

                lastLexicalSource <- source
                lastLexicalFormatted <- formatted
                lastLexicalBefore <- before
                lastLexicalId <- lexedTexts

                let struct (same, prefix) =
                    lexicallyEqualBuffersBounded
                        (source.AsSpan())
                        (formatted.AsSpan())
                        before.LexerBuffer
                        after.LexerBuffer
                        startIdx
                        endLimit

                lastLexicalPrefix <- prefix
                same
            else
                if syms.Length > 0 then
                    if prevTok > 0 then
                        lexTextWithHinted
                            syms
                            (prevTok + (prevTok >>> 4) + 32)
                            (prevTriv + (prevTriv >>> 4) + 64)
                            source
                            before
                    else
                        lexTextWith syms source before

                    let bBuf = before.LexerBuffer
                    let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                    let trivHint =
                        max
                            (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64)
                            (bBuf.TokenCount + 64)

                    lexTextWithHinted syms tokHint trivHint formatted after
                else
                    if prevTok > 0 then
                        lexTextHinted
                            (prevTok + (prevTok >>> 4) + 32)
                            (prevTriv + (prevTriv >>> 4) + 64)
                            source
                            before
                    else
                        lexText source before

                    let bBuf = before.LexerBuffer
                    let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                    let trivHint =
                        max
                            (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64)
                            (bBuf.TokenCount + 64)

                    lexTextHinted tokHint trivHint formatted after

                beforeLexedFor <- source
                afterLexedFor <- formatted
                beforeLexedSymbols <- syms
                afterLexedSymbols <- syms
                lexicallyEqual source formatted

        member this.CommentsPreserved
            (source: string, formatted: string, loaded: bool, ?sourceTree: SyntaxTree)
            =
            let parsedTree =
                match sourceTree with
                | Some parsed -> parsed
                | None -> Unchecked.defaultof<SyntaxTree>

            this.CommentsPreservedDirect(source, formatted, loaded, parsedTree)

        member internal _.BeginDisabledDeferral(enabled: bool) =
            allowDisabledDeferral <- enabled
            disabledDeferralPrefix <- 0
            clearDeferredDisabledSpans ()

        member internal _.EndDisabledDeferral() =
            allowDisabledDeferral <- false
            disabledDeferralPrefix <- 0
            clearDeferredDisabledSpans ()
            DeclaredTransformations.clearRewriteChain ()

        member internal _.SetDisabledDeferralPrefix(prefixLen: int) =
            disabledDeferralPrefix <- prefixLen

        member internal _.DeferredDisabledSpanCount = deferredDisabledSpans.Count

        member internal _.TruncateDeferredDisabledSpans(count: int) =
            truncateDeferredDisabledSpans count

        member internal _.AllDeferredDisabledSpansProvenBy
            (
                options: PrinterOptions,
                witness: TransformationWitness,
                formatted: string,
                provenConfigs: ResizeArray<struct (string array * string)>
            ) =
            if deferredDisabledSpans.Count = 0 then
                true
            elif provenConfigs.Count = 0 then
                false
            else
                let getHoleBuffer (depth: int) = getDepthBuffer interpHoleBuffers depth

                let getHoleTree (trees: ResizeArray<SyntaxTree>) (depth: int) =
                    while trees.Count <= depth do
                        trees.Add(SyntaxTree())

                    let tree = trees[depth]
                    tree.Reset()
                    tree

                let scanHoleTokens
                    (text: string)
                    (tree: SyntaxTree)
                    (tokens: ResizeArray<Token>)
                    (hStart: int)
                    (hEnd: int)
                    (startIdx: int)
                    (comments: ResizeArray<string>)
                    (nested: ResizeArray<Token>)
                    =
                    comments.Clear()
                    nested.Clear()
                    let mutable idx = startIdx

                    while idx < tokens.Count - 1 && tokens[idx].Start < hEnd do
                        let tok = tokens[idx]

                        if tok.Start >= hStart then
                            for k = 0 to tok.LeadingCount + tok.TrailingCount - 1 do
                                let triv = tree.Trivia(tok.TriviaStart + k)

                                if commentTrivia triv.Kind then
                                    comments.Add(commentKey text triv)

                            if tok.Kind = TokenKind.InterpolatedStringToken then
                                nested.Add tok

                        idx <- idx + 1

                    idx

                let rec interpolatedHoleCommentsEqual
                    (depth: int)
                    (leftText: string)
                    (leftTok: Token)
                    (rightText: string)
                    (rightTok: Token)
                    =
                    if depth >= 64 then
                        false
                    else
                        let leftTree = getHoleTree interpHoleTreesLeft depth
                        let rightTree = getHoleTree interpHoleTreesRight depth
                        let leftHoles = ResizeArray<struct (int * int)>()
                        let rightHoles = ResizeArray<struct (int * int)>()

                        let leftTokens =
                            InterpolationLexer.expandWithHoles leftText leftTok leftTree leftHoles

                        let rightTokens =
                            InterpolationLexer.expandWithHoles
                                rightText
                                rightTok
                                rightTree
                                rightHoles

                        if
                            leftTree.RecoveredTokens <> 0
                            || rightTree.RecoveredTokens <> 0
                            || leftHoles.Count <> rightHoles.Count
                        then
                            false
                        else
                            let leftComments = ResizeArray<string>()
                            let rightComments = ResizeArray<string>()
                            let leftNested = ResizeArray<Token>()
                            let rightNested = ResizeArray<Token>()
                            let mutable li = 1
                            let mutable ri = 1
                            let mutable holeIdx = 0
                            let mutable ok = true

                            while ok && holeIdx < leftHoles.Count do
                                let struct (lStart, lLen) = leftHoles[holeIdx]
                                let struct (rStart, rLen) = rightHoles[holeIdx]

                                li <-
                                    scanHoleTokens
                                        leftText
                                        leftTree
                                        leftTokens
                                        lStart
                                        (lStart + lLen)
                                        li
                                        leftComments
                                        leftNested

                                ri <-
                                    scanHoleTokens
                                        rightText
                                        rightTree
                                        rightTokens
                                        rStart
                                        (rStart + rLen)
                                        ri
                                        rightComments
                                        rightNested

                                if
                                    leftComments.Count <> rightComments.Count
                                    || leftNested.Count <> rightNested.Count
                                then
                                    ok <- false
                                else
                                    let mutable ci = 0

                                    while ok && ci < leftComments.Count do
                                        if
                                            not (
                                                String.Equals(
                                                    leftComments[ci],
                                                    rightComments[ci],
                                                    StringComparison.Ordinal
                                                )
                                            )
                                        then
                                            ok <- false

                                        ci <- ci + 1

                                    let mutable ni = 0

                                    while ok && ni < leftNested.Count do
                                        let ln = leftNested[ni]
                                        let rn = rightNested[ni]

                                        if
                                            leftText.AsSpan(ln.Start, ln.Length).IndexOf('/') >= 0
                                            || rightText.AsSpan(rn.Start, rn.Length).IndexOf('/')
                                               >= 0
                                        then
                                            ok <-
                                                interpolatedHoleCommentsEqual
                                                    (depth + 1)
                                                    leftText
                                                    ln
                                                    rightText
                                                    rn

                                        ni <- ni + 1

                                holeIdx <- holeIdx + 1

                            ok

                let rec interpTokenHasHoleComments (depth: int) (text: string) (tok: Token) =
                    if depth >= 64 then
                        true
                    elif text.AsSpan(tok.Start, tok.Length).IndexOf('/') < 0 then
                        false
                    else
                        let struct (valid, raw, verbatim, width, contentStart, contentEnd) =
                            parseInterpHeader true text tok

                        if not valid then
                            true
                        else
                            let mutable cursor = contentStart
                            let mutable found = false
                            let mutable stop = false
                            let holeBuf = getHoleBuffer depth

                            while not stop && not found && cursor < contentEnd do
                                let struct (okHole, holeOpen) =
                                    nextInterpHole text raw verbatim width cursor contentEnd

                                if not okHole then
                                    found <- true
                                elif holeOpen < 0 then
                                    stop <- true
                                else
                                    let exprStart = holeOpen + width

                                    let struct (boundary, hasFmt) =
                                        Lexer.lexInterpolationWithRecovery
                                            false
                                            text
                                            (exprStart - 1)
                                            contentEnd
                                            holeBuf

                                    if
                                        holeBuf.HasComments
                                        || holeBuf.HasDisabledText
                                        || DeclaredTransformations.hasMalformedTrivia holeBuf
                                    then
                                        found <- true
                                    elif holeBuf.InterpolatedCount > 0 then
                                        let mutable k = 0

                                        while not found && k < holeBuf.InterpolatedCount do
                                            let subTok = holeBuf.Token(holeBuf.Interpolated k)

                                            if
                                                interpTokenHasHoleComments (depth + 1) text subTok
                                            then
                                                found <- true

                                            k <- k + 1

                                    if not found then
                                        if boundary < 0 then
                                            found <- true
                                        elif hasFmt then
                                            let fmtStart = min contentEnd (boundary + 1)

                                            let closing =
                                                scanFormatEnd text raw verbatim fmtStart contentEnd

                                            if
                                                not (hasClosingWidth text closing contentEnd width)
                                            then
                                                found <- true
                                            else
                                                cursor <- closing + width
                                        elif
                                            not (hasClosingWidth text boundary contentEnd width)
                                        then
                                            found <- true
                                        else
                                            cursor <- boundary + width

                            found

                let remaining = ResizeArray(deferredDisabledSpans)

                remaining.Sort
                    (fun (struct (_, _, _, _, fs1, fe1)) (struct (_, _, _, _, fs2, fe2)) ->
                        let c = compare fs1 fs2
                        if c <> 0 then c else compare fe1 fe2)

                let blockedFlags = Array.zeroCreate<bool> remaining.Count

                let fmtCommentedLists = Array.zeroCreate<ResizeArray<Token>>(remaining.Count)

                let checkFormatted (text: string) (prefixLen: int) =
                    let buf = before.LexerBuffer

                    for remIdx = 0 to remaining.Count - 1 do
                        if not (isNull fmtCommentedLists[remIdx]) then
                            fmtCommentedLists[remIdx].Clear()

                    if buf.HasDisabledText || buf.HasComments || buf.HasInterpolated then
                        let trivia = buf.TriviaSpan()
                        let lastRelevant = max buf.LastNonCommentTrivia buf.LastCommentTrivia

                        let limit =
                            if lastRelevant < 0 then
                                0
                            else
                                min trivia.Length (lastRelevant + 1)

                        let tokens = buf.TokenSpan()
                        let ipCount = buf.InterpolatedCount
                        let mutable t = 0
                        let mutable ip = 0

                        for remIdx = 0 to remaining.Count - 1 do
                            let struct (_, _, _, _, fmtS, fmtE) = remaining[remIdx]

                            if fmtS < fmtE then
                                let pStart = fmtS + prefixLen
                                let pEnd = fmtE + prefixLen
                                let mutable blocked = false

                                if buf.HasDisabledText || buf.HasComments then
                                    while t < limit
                                          && (trivia[t].Start + trivia[t].Length <= pStart
                                              || (trivia[t].Kind <> TriviaKind.DisabledTextTrivia
                                                  && trivia[t].Kind
                                                     <> TriviaKind.MultiLineCommentTrivia
                                                  && trivia[t].Kind
                                                     <> TriviaKind
                                                         .MultiLineDocumentationCommentTrivia)) do
                                        t <- t + 1

                                    let mutable t2 = t

                                    while not blocked && t2 < limit && trivia[t2].Start < pEnd do
                                        let item = trivia[t2]

                                        if item.Kind = TriviaKind.DisabledTextTrivia then
                                            if pStart < item.Start + item.Length then
                                                blocked <- true
                                        elif
                                            item.Kind = TriviaKind.MultiLineCommentTrivia
                                            || item.Kind =
                                                TriviaKind.MultiLineDocumentationCommentTrivia
                                        then
                                            if
                                                item.Start <= pStart
                                                && pEnd <= item.Start + item.Length
                                            then
                                                blocked <- true

                                        t2 <- t2 + 1

                                if not blocked && ipCount > 0 then
                                    while ip < ipCount
                                          && tokens[buf.Interpolated ip].Start
                                             + tokens[buf.Interpolated ip].Length
                                             <= pStart do
                                        ip <- ip + 1

                                    let mutable ip2 = ip

                                    while ip2 < ipCount do
                                        let tok = buf.Token(buf.Interpolated ip2)

                                        if tok.Start >= pEnd then
                                            ip2 <- ipCount
                                        else
                                            if interpTokenHasHoleComments 0 text tok then
                                                let list =
                                                    match fmtCommentedLists[remIdx] with
                                                    | null ->
                                                        let r = ResizeArray<Token>()
                                                        fmtCommentedLists[remIdx] <- r
                                                        r
                                                    | existing -> existing

                                                list.Add tok

                                            ip2 <- ip2 + 1

                                if blocked then
                                    blockedFlags[remIdx] <- true

                let checkSourceGroup
                    (syms: string array)
                    (cfgPrefix: string)
                    (cfgPrefixLen: int)
                    (lexTarget: string)
                    (srcText: string)
                    (srcPrefixLen: int)
                    =
                    let rawSource =
                        if srcPrefixLen > 0 then
                            srcText.Substring(srcPrefixLen)
                        else
                            srcText

                    let lexSource =
                        if cfgPrefixLen > 0 then
                            cfgPrefix + rawSource
                        else
                            rawSource

                    if syms.Length > 0 then
                        lexTextWith syms lexSource before
                    else
                        lexText lexSource before

                    let buf = before.LexerBuffer
                    let trivia = buf.TriviaSpan()
                    let lastRelevant = max buf.LastNonCommentTrivia buf.LastCommentTrivia

                    let limit =
                        if lastRelevant < 0 then
                            0
                        else
                            min trivia.Length (lastRelevant + 1)

                    let tokens = buf.TokenSpan()
                    let ipCount = buf.InterpolatedCount
                    let mutable t = 0
                    let mutable ip = 0
                    let mutable prevStart = -1

                    for remIdx = 0 to remaining.Count - 1 do
                        let struct (itemText, itemPref, srcS, srcE, _, _) = remaining[remIdx]

                        if
                            not blockedFlags[remIdx]
                            && obj.ReferenceEquals(itemText, srcText)
                            && itemPref = srcPrefixLen
                        then
                            let fmtList = fmtCommentedLists[remIdx]
                            let fmtCommentedCount = if isNull fmtList then 0 else fmtList.Count

                            if srcS >= srcE then
                                if fmtCommentedCount > 0 then
                                    blockedFlags[remIdx] <- true
                            else
                                let pStart = srcS + cfgPrefixLen
                                let pEnd = srcE + cfgPrefixLen

                                if pStart < prevStart then
                                    t <- 0
                                    ip <- 0

                                prevStart <- pStart
                                let mutable blocked = false

                                if buf.HasDisabledText || buf.HasComments then
                                    while t < limit
                                          && (trivia[t].Start + trivia[t].Length <= pStart
                                              || (trivia[t].Kind <> TriviaKind.DisabledTextTrivia
                                                  && trivia[t].Kind
                                                     <> TriviaKind.MultiLineCommentTrivia
                                                  && trivia[t].Kind
                                                     <> TriviaKind
                                                         .MultiLineDocumentationCommentTrivia)) do
                                        t <- t + 1

                                    let mutable t2 = t

                                    while not blocked && t2 < limit && trivia[t2].Start < pEnd do
                                        let item = trivia[t2]

                                        if item.Kind = TriviaKind.DisabledTextTrivia then
                                            if pStart < item.Start + item.Length then
                                                blocked <- true
                                        elif
                                            item.Kind = TriviaKind.MultiLineCommentTrivia
                                            || item.Kind =
                                                TriviaKind.MultiLineDocumentationCommentTrivia
                                        then
                                            if
                                                item.Start <= pStart
                                                && pEnd <= item.Start + item.Length
                                            then
                                                blocked <- true

                                        t2 <- t2 + 1

                                let mutable srcMatched = 0

                                if not blocked && ipCount > 0 then
                                    while ip < ipCount
                                          && tokens[buf.Interpolated ip].Start
                                             + tokens[buf.Interpolated ip].Length
                                             <= pStart do
                                        ip <- ip + 1

                                    let mutable ip2 = ip

                                    while not blocked && ip2 < ipCount do
                                        let tok = buf.Token(buf.Interpolated ip2)

                                        if tok.Start >= pEnd then
                                            ip2 <- ipCount
                                        else
                                            if interpTokenHasHoleComments 0 lexSource tok then
                                                if srcMatched >= fmtCommentedCount then
                                                    blocked <- true
                                                else
                                                    let fTok = fmtList[srcMatched]

                                                    if
                                                        not (
                                                            (tok.Length = fTok.Length
                                                             && lexSource
                                                                 .AsSpan(tok.Start, tok.Length)
                                                                 .SequenceEqual(
                                                                     lexTarget.AsSpan(
                                                                         fTok.Start,
                                                                         fTok.Length
                                                                     )
                                                                 ))
                                                            || interpolatedStringsLexicallyEqual
                                                                true
                                                                lexSource
                                                                tok
                                                                lexTarget
                                                                fTok
                                                            || (witness.ReindentedRawStrings
                                                                && reindentedInterpolatedStringsEqual
                                                                    options
                                                                    lexSource
                                                                    tok
                                                                    lexTarget
                                                                    fTok)
                                                            || interpolatedHoleCommentsEqual
                                                                0
                                                                lexSource
                                                                tok
                                                                lexTarget
                                                                fTok
                                                        )
                                                    then
                                                        blocked <- true
                                                    else
                                                        srcMatched <- srcMatched + 1

                                            ip2 <- ip2 + 1

                                if not blocked && srcMatched <> fmtCommentedCount then
                                    blocked <- true

                                if blocked then
                                    blockedFlags[remIdx] <- true

                let mutable cfgIdx = 0

                while remaining.Count > 0 && cfgIdx < provenConfigs.Count do
                    let struct (syms, prefix) = provenConfigs[cfgIdx]
                    let prefixLen = if isNull prefix then 0 else prefix.Length
                    let lexTarget = if prefixLen > 0 then prefix + formatted else formatted
                    before <- ownedBefore
                    beforeLexedFor <- null
                    beforeLexedSymbols <- Array.empty
                    lastLexicalSource <- null
                    lastLexicalFormatted <- null

                    if syms.Length > 0 then
                        lexTextWith syms lexTarget before
                    else
                        lexText lexTarget before

                    Array.Clear(blockedFlags, 0, remaining.Count)
                    checkFormatted lexTarget prefixLen

                    let checkedGroups = ResizeArray<struct (string * int)>()
                    let mutable scanIdx = 0

                    while scanIdx < remaining.Count do
                        if not blockedFlags[scanIdx] then
                            let struct (srcText, srcPrefixLen, srcS, srcE, _, _) =
                                remaining[scanIdx]

                            let fmtList = fmtCommentedLists[scanIdx]

                            let needsSourceCheck =
                                (not (isNull fmtList) && fmtList.Count > 0)
                                || (srcS < srcE
                                    && srcText.AsSpan(srcS + srcPrefixLen, srcE - srcS).IndexOf('/')
                                       >= 0)

                            if needsSourceCheck then
                                let mutable alreadyChecked = false
                                let mutable g = 0

                                while not alreadyChecked && g < checkedGroups.Count do
                                    let struct (gText, gPref) = checkedGroups[g]

                                    if
                                        obj.ReferenceEquals(gText, srcText) && gPref = srcPrefixLen
                                    then
                                        alreadyChecked <- true

                                    g <- g + 1

                                if not alreadyChecked then
                                    checkedGroups.Add(struct (srcText, srcPrefixLen))

                                    checkSourceGroup
                                        syms
                                        prefix
                                        prefixLen
                                        lexTarget
                                        srcText
                                        srcPrefixLen

                        scanIdx <- scanIdx + 1

                    let mutable writeIdx = 0

                    for remIdx = 0 to remaining.Count - 1 do
                        if blockedFlags[remIdx] then
                            remaining[writeIdx] <- remaining[remIdx]
                            writeIdx <- writeIdx + 1

                    if writeIdx < remaining.Count then
                        remaining.RemoveRange(writeIdx, remaining.Count - writeIdx)

                    cfgIdx <- cfgIdx + 1

                remaining.Count = 0

        member internal this.CommentsPreservedPair
            (
                source: string,
                formatted: string,
                syms: string array,
                loaded: bool,
                allowDirectiveSpanningMultiLine: bool
            ) =
            if not loaded then
                before <- ownedBefore
                beforeBuilt <- false
                beforeLexedFor <- null
                beforeLexedSymbols <- Array.empty
                afterLexedFor <- null
                afterLexedSymbols <- Array.empty
                afterLexedSpanId <- -1

                if syms.Length > 0 then
                    lexTextWith syms source before
                    let bBuf = before.LexerBuffer
                    let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                    let trivHint =
                        max
                            (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64)
                            (bBuf.TokenCount + 64)

                    lexTextWithHinted syms tokHint trivHint formatted after
                else
                    lexText source before
                    let bBuf = before.LexerBuffer
                    let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                    let trivHint =
                        max
                            (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64)
                            (bBuf.TokenCount + 64)

                    lexTextHinted tokHint trivHint formatted after

                beforeLexedFor <- source
                afterLexedFor <- formatted
                beforeLexedSymbols <- syms
                afterLexedSymbols <- syms

            let mutable cached = formatted

            this.CommentsPreservedCore(
                source,
                formatted.AsSpan(),
                &cached,
                true,
                Unchecked.defaultof<SyntaxTree>,
                allowDirectiveSpanningMultiLine
            )

        member internal this.CommentsPreservedDirect
            (source: string, formatted: string, loaded: bool, sourceTree: SyntaxTree)
            =
            let mutable cached = formatted

            this.CommentsPreservedCore(
                source,
                formatted.AsSpan(),
                &cached,
                loaded,
                sourceTree,
                false
            )

        member private this.EnsureFmtStr(formatted: ReadOnlySpan<char>, cachedFmt: byref<string>) =
            if isNull cachedFmt then
                let s = String formatted
                cachedFmt <- s
                this.BindLexedFormatted s
                s
            else
                cachedFmt

        member private _.CheckRangeMultiset
            (
                allowDirectiveSpanning: bool,
                deferredRawSpans: ResizeArray<struct (int * int * int * int)>,
                lText: string,
                lBuf: TokenBuffer,
                lStart: int,
                lEnd: int,
                rText: string,
                rBuf: TokenBuffer,
                rStart: int,
                rEnd: int
            ) =
            let hasL = rangeHasComment lBuf lStart lEnd
            let hasR = rangeHasComment rBuf rStart rEnd

            if not hasL && not hasR then
                true
            elif hasL <> hasR then
                false
            else
                let struct (expected, actual) =
                    commentKeyPair lText lBuf lStart lEnd rText rBuf rStart rEnd

                let struct (lost, gained, _, _) = symmetricCommentDiff expected actual

                if lost = 0 && gained = 0 then
                    true
                else
                    let lLim = min lEnd lBuf.LastCommentTrivia
                    let rLim = min rEnd rBuf.LastCommentTrivia
                    let lCount = max 0 (lLim - lStart + 1)
                    let rCount = max 0 (rLim - rStart + 1)

                    if lCount = 0 || rCount = 0 then
                        false
                    else
                        let lostCounts = Dictionary<string, int>(max 4 lost, StringComparer.Ordinal)

                        let gainedCounts =
                            Dictionary<string, int>(max 4 gained, StringComparer.Ordinal)

                        let addCount (map: Dictionary<string, int>) (k: string) =
                            let mutable cnt = 0

                            if map.TryGetValue(k, &cnt) then
                                map[k] <- cnt + 1
                            else
                                map[k] <- 1

                        let mutable ei = 0
                        let mutable ai = 0

                        while ei < expected.Length && ai < actual.Length do
                            let cmp = String.CompareOrdinal(expected[ei], actual[ai])

                            if cmp = 0 then
                                ei <- ei + 1
                                ai <- ai + 1
                            elif cmp < 0 then
                                addCount lostCounts expected[ei]
                                ei <- ei + 1
                            else
                                addCount gainedCounts actual[ai]
                                ai <- ai + 1

                        while ei < expected.Length do
                            addCount lostCounts expected[ei]
                            ei <- ei + 1

                        while ai < actual.Length do
                            addCount gainedCounts actual[ai]
                            ai <- ai + 1

                        let takeCount (map: Dictionary<string, int>) (k: string) =
                            let mutable cnt = 0

                            if map.TryGetValue(k, &cnt) && cnt > 0 then
                                if cnt = 1 then
                                    map.Remove k |> ignore
                                else
                                    map[k] <- cnt - 1

                                true
                            else
                                false

                        let lTriv = lBuf.TriviaSpan()
                        let rTriv = rBuf.TriviaSpan()
                        let lToks = lBuf.TokenSpan()
                        let lSpan = lText.AsSpan()
                        let rSpan = rText.AsSpan()
                        let leftUsed = Array.zeroCreate<bool> lCount
                        let outerSpans = ResizeArray<struct (int * int * int * int)>()
                        let consumedKeys = ResizeArray<string>(4)
                        let mutable lostRem = lost
                        let mutable gainedRem = gained
                        let mutable hintLi = lStart
                        let mutable ri = rStart

                        while ri <= rLim && gainedRem > 0 do
                            let b = rTriv[ri]

                            if commentTrivia b.Kind then
                                let rKey = commentKey rText b
                                let mutable gCnt = 0

                                if gainedCounts.TryGetValue(rKey, &gCnt) && gCnt > 0 then
                                    let isMergedDoc =
                                        b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                                        && rKey.IndexOf('\n') >= 0

                                    let isSpanningMulti =
                                        allowDirectiveSpanning
                                        && (b.Kind = TriviaKind.MultiLineCommentTrivia
                                            || b.Kind =
                                                TriviaKind.MultiLineDocumentationCommentTrivia)

                                    if isMergedDoc || isSpanningMulti then
                                        let mutable matched = false
                                        let mutable pass = 0

                                        while not matched && pass < 2 do
                                            let mutable li = if pass = 0 then hintLi else lStart

                                            let stopLi =
                                                if pass = 0 then lLim else min (hintLi - 1) lLim

                                            while not matched && li <= stopLi do
                                                let a = lTriv[li]

                                                if not leftUsed[li - lStart] then
                                                    if isMergedDoc then
                                                        if
                                                            a.Kind =
                                                                TriviaKind
                                                                    .SingleLineDocumentationCommentTrivia
                                                            && lostCounts.ContainsKey(
                                                                commentKey lText a
                                                            )
                                                        then
                                                            let startTok =
                                                                if li > 0 then
                                                                    tokenIndexForTrivia lToks li
                                                                else
                                                                    0

                                                            let struct (nextLeft, _) =
                                                                mergedDocCommentEquivalentSpan
                                                                    lSpan
                                                                    lBuf
                                                                    li
                                                                    (lLim + 1)
                                                                    startTok
                                                                    rSpan
                                                                    b

                                                            if nextLeft > li then
                                                                consumedKeys.Clear()
                                                                let mutable spanOk = true
                                                                let mutable u = li

                                                                while spanOk && u < nextLeft do
                                                                    let lu = lTriv[u]

                                                                    if commentTrivia lu.Kind then
                                                                        if leftUsed[u - lStart] then
                                                                            spanOk <- false
                                                                        else
                                                                            let uKey =
                                                                                commentKey lText lu

                                                                            if
                                                                                takeCount
                                                                                    lostCounts
                                                                                    uKey
                                                                            then
                                                                                consumedKeys.Add
                                                                                    uKey
                                                                            else
                                                                                spanOk <- false

                                                                    u <- u + 1

                                                                if spanOk then
                                                                    for uIdx = li to nextLeft - 1 do
                                                                        if
                                                                            commentTrivia
                                                                                lTriv[uIdx].Kind
                                                                        then
                                                                            leftUsed[uIdx - lStart] <-
                                                                                true

                                                                    lostRem <-
                                                                        lostRem - consumedKeys.Count

                                                                    takeCount gainedCounts rKey
                                                                    |> ignore

                                                                    gainedRem <- gainedRem - 1
                                                                    hintLi <- nextLeft
                                                                    matched <- true
                                                                else
                                                                    for ci = consumedKeys.Count - 1 downto 0 do
                                                                        addCount
                                                                            lostCounts
                                                                            consumedKeys[ci]
                                                    elif a.Kind = b.Kind then
                                                        let lKey = commentKey lText a

                                                        if
                                                            lostCounts.ContainsKey lKey
                                                            && directiveSpanningMultiLineEquivalent
                                                                (lSpan.Slice(a.Start, a.Length))
                                                                (rSpan.Slice(b.Start, b.Length))
                                                                outerSpans
                                                        then
                                                            if not (isNull deferredRawSpans) then
                                                                for oi = 0 to outerSpans.Count - 1 do
                                                                    let struct (relLS, relLE, relRS,
                                                                                relRE) =
                                                                        outerSpans[oi]

                                                                    deferredRawSpans.Add(
                                                                        struct (a.Start + relLS,
                                                                                a.Start + relLE,
                                                                                b.Start + relRS,
                                                                                b.Start + relRE)
                                                                    )

                                                            leftUsed[li - lStart] <- true
                                                            takeCount lostCounts lKey |> ignore
                                                            lostRem <- lostRem - 1
                                                            takeCount gainedCounts rKey |> ignore
                                                            gainedRem <- gainedRem - 1
                                                            hintLi <- li + 1
                                                            matched <- true

                                                li <- li + 1

                                            pass <- pass + 1

                            ri <- ri + 1

                        lostRem = 0 && gainedRem = 0

        member private this.RemainingHolesHaveComments
            (
                depth: int,
                text: string,
                raw: bool,
                verbatim: bool,
                width: int,
                startCursor: int,
                cEnd: int
            ) =
            if depth >= 64 then
                false
            else
                let buf = getDepthBuffer interpScanDepthBuffers depth
                let mutable cursor = startCursor
                let mutable foundComment = false
                let mutable keepGoing = true

                while keepGoing && not foundComment && cursor < cEnd do
                    let struct (okHole, holeOpen) =
                        nextInterpHole text raw verbatim width cursor cEnd

                    if not okHole || holeOpen < 0 then
                        keepGoing <- false
                    else
                        let exprStart = holeOpen + width

                        let struct (boundary, hasFmt) =
                            Lexer.lexInterpolationWithRecovery false text (exprStart - 1) cEnd buf

                        if buf.HasComments then
                            foundComment <- true
                        elif buf.InterpolatedCount > 0 then
                            let mutable k = 0

                            while not foundComment && k < buf.InterpolatedCount do
                                let subTok = buf.Token(buf.Interpolated k)

                                if
                                    this.InterpolationTokenHasHoleComments(depth + 1, text, subTok)
                                then
                                    foundComment <- true

                                k <- k + 1

                        if not foundComment then
                            if boundary < 0 then
                                keepGoing <- false
                            elif hasFmt then
                                let fmtStart = min cEnd (boundary + 1)
                                let closing = scanFormatEnd text raw verbatim fmtStart cEnd
                                cursor <- min cEnd (closing + width)
                            else
                                cursor <- min cEnd (boundary + width)

                foundComment

        member private this.InterpolationTokenHasHoleComments
            (depth: int, text: string, tok: Token)
            =
            if depth >= 64 || text.AsSpan(tok.Start, tok.Length).IndexOf('/') < 0 then
                false
            else
                let struct (validHeader, raw, verbatim, width, cStart, cEnd) =
                    parseInterpHeader true text tok

                if not validHeader then
                    false
                else
                    this.RemainingHolesHaveComments(depth, text, raw, verbatim, width, cStart, cEnd)

        member private this.CheckInterpPair
            (
                depth: int,
                lText: string,
                lSpan: ReadOnlySpan<char>,
                rSpan: ReadOnlySpan<char>,
                lTok: Token,
                rTok: Token,
                cachedFmt: byref<string>
            ) : bool =
            if
                lTok.Length = rTok.Length
                && lSpan
                    .Slice(lTok.Start, lTok.Length)
                    .SequenceEqual(rSpan.Slice(rTok.Start, rTok.Length))
            then
                true
            elif
                lSpan.Slice(lTok.Start, lTok.Length).IndexOf('/') < 0
                && rSpan.Slice(rTok.Start, rTok.Length).IndexOf('/') < 0
            then
                true
            elif depth >= 64 then
                false
            else
                let rText = this.EnsureFmtStr(rSpan, &cachedFmt)

                let struct (lValid, lRaw, lVerb, lWidth, lStart, lEnd) =
                    parseInterpHeader true lText lTok

                let struct (rValid, rRaw, rVerb, rWidth, rStart, rEnd) =
                    parseInterpHeader true rText rTok

                if
                    not lValid || not rValid || lRaw <> rRaw || lVerb <> rVerb || lWidth <> rWidth
                then
                    not (
                        this.InterpolationTokenHasHoleComments(depth, lText, lTok)
                        || this.InterpolationTokenHasHoleComments(depth, rText, rTok)
                    )
                else
                    let lHoleBuf, rHoleBuf =
                        if depth = 0 then
                            interpLeft, interpRight
                        else
                            getDepthBuffer interpLeftDepthBuffers (depth - 1),
                            getDepthBuffer interpRightDepthBuffers (depth - 1)

                    let mutable ok = true
                    let mutable lCursor = lStart
                    let mutable rCursor = rStart

                    while ok && (lCursor < lEnd || rCursor < rEnd) do
                        let struct (lOk, lOpen) =
                            nextInterpHole lText lRaw lVerb lWidth lCursor lEnd

                        let struct (rOk, rOpen) =
                            nextInterpHole rText rRaw rVerb rWidth rCursor rEnd

                        if not lOk || not rOk || (lOpen >= 0) <> (rOpen >= 0) then
                            if
                                this.RemainingHolesHaveComments(
                                    depth,
                                    lText,
                                    lRaw,
                                    lVerb,
                                    lWidth,
                                    lCursor,
                                    lEnd
                                )
                                || this.RemainingHolesHaveComments(
                                    depth,
                                    rText,
                                    rRaw,
                                    rVerb,
                                    rWidth,
                                    rCursor,
                                    rEnd
                                )
                            then
                                ok <- false
                            else
                                lCursor <- lEnd
                                rCursor <- rEnd
                        elif lOpen < 0 then
                            lCursor <- lEnd
                            rCursor <- rEnd
                        else
                            let lExprStart = lOpen + lWidth
                            let rExprStart = rOpen + rWidth

                            let struct (lBound, lFmt) =
                                Lexer.lexInterpolationWithRecovery
                                    false
                                    lText
                                    (lExprStart - 1)
                                    lEnd
                                    lHoleBuf

                            let struct (rBound, rFmt) =
                                Lexer.lexInterpolationWithRecovery
                                    false
                                    rText
                                    (rExprStart - 1)
                                    rEnd
                                    rHoleBuf

                            let struct (holeOk, _, _) =
                                this.CheckAnchoredSpan(
                                    depth + 1,
                                    false,
                                    false,
                                    null,
                                    lText,
                                    lSpan,
                                    rSpan,
                                    lHoleBuf,
                                    rHoleBuf,
                                    0,
                                    &cachedFmt
                                )

                            if not holeOk then
                                ok <- false
                            elif lBound < 0 || rBound < 0 then
                                if
                                    lBound >= 0
                                    && this.RemainingHolesHaveComments(
                                        depth,
                                        lText,
                                        lRaw,
                                        lVerb,
                                        lWidth,
                                        min lEnd (lBound + lWidth),
                                        lEnd
                                    )
                                    || rBound >= 0
                                       && this.RemainingHolesHaveComments(
                                           depth,
                                           rText,
                                           rRaw,
                                           rVerb,
                                           rWidth,
                                           min rEnd (rBound + rWidth),
                                           rEnd
                                       )
                                then
                                    ok <- false
                                else
                                    lCursor <- lEnd
                                    rCursor <- rEnd
                            else
                                if lFmt then
                                    let lFmtStart = min lEnd (lBound + 1)
                                    let lClosing = scanFormatEnd lText lRaw lVerb lFmtStart lEnd
                                    lCursor <- min lEnd (lClosing + lWidth)
                                else
                                    lCursor <- min lEnd (lBound + lWidth)

                                if rFmt then
                                    let rFmtStart = min rEnd (rBound + 1)
                                    let rClosing = scanFormatEnd rText rRaw rVerb rFmtStart rEnd
                                    rCursor <- min rEnd (rClosing + rWidth)
                                else
                                    rCursor <- min rEnd (rBound + rWidth)

                    ok

        member private this.CheckModRunPermuted
            (
                isOuter: bool,
                allowDirectiveSpanning: bool,
                deferredRawSpans: ResizeArray<struct (int * int * int * int)>,
                lText: string,
                lSpan: ReadOnlySpan<char>,
                rSpan: ReadOnlySpan<char>,
                lBuf: TokenBuffer,
                rBuf: TokenBuffer,
                curI: int,
                curJ: int,
                inLeadSkip: int,
                outLeadSkip: int,
                inPendS: int,
                inPendC: int,
                outPendS: int,
                outPendC: int,
                cachedFmt: byref<string>
            ) =
            let inTokens = lBuf.TokenSpan()
            let outTokens = rBuf.TokenSpan()
            let inCount = inTokens.Length
            let outCount = outTokens.Length

            if
                not isOuter
                || curI >= inCount - 1
                || curJ >= outCount - 1
                || lexerModifierKindSpan lSpan inTokens[curI] = TokenKind.None
                || lexerModifierKindSpan rSpan outTokens[curJ] = TokenKind.None
            then
                struct (false, false, curI, curJ)
            else
                let a0 = inTokens[curI]
                let b0 = outTokens[curJ]

                if
                    a0.Kind = b0.Kind
                    && a0.Length = b0.Length
                    && sameTokenTextSpan lSpan &a0 rSpan &b0
                then
                    struct (false, false, curI, curJ)
                else
                    let struct (foundDecl, _, beforeCount, modOffset) =
                        findSortableModifierDecl lText a0.Start

                    let remCount = beforeCount - modOffset

                    if
                        foundDecl < 0
                        || modOffset < 0
                        || remCount < 2
                        || curI + remCount >= inCount
                        || curJ + remCount >= outCount
                        || lexerModifierKindSpan lSpan inTokens[curI + remCount] <> TokenKind.None
                        || lexerModifierKindSpan rSpan outTokens[curJ + remCount] <> TokenKind.None
                        || inTokens[curI + remCount].Kind <> outTokens[curJ + remCount].Kind
                    then
                        struct (false, false, curI, curJ)
                    else
                        let mutable validMods = true

                        for s = 0 to remCount - 1 do
                            if
                                lexerModifierKindSpan lSpan inTokens[curI + s] = TokenKind.None
                                || lexerModifierKindSpan rSpan outTokens[curJ + s] = TokenKind.None
                            then
                                validMods <- false

                        if not validMods then
                            struct (false, false, curI, curJ)
                        else
                            usingTaken <- grownFlags usingTaken remCount
                            Array.fill usingTaken 0 remCount false
                            childSlots <- grownIndices childSlots remCount
                            let mutable s = 0

                            while validMods && s < remCount do
                                let bt = inTokens[curI + s]
                                let mutable found = -1
                                let mutable c = 0

                                while found < 0 && c < remCount do
                                    if not usingTaken[c] then
                                        let at = outTokens[curJ + c]

                                        if
                                            bt.Kind = at.Kind
                                            && bt.Length = at.Length
                                            && sameTokenTextSpan lSpan &bt rSpan &at
                                        then
                                            found <- c

                                    c <- c + 1

                                if found < 0 then
                                    validMods <- false
                                else
                                    usingTaken[found] <- true
                                    childSlots[s] <- found
                                    s <- s + 1

                            if not validMods then
                                struct (false, false, curI, curJ)
                            else
                                let struct (pendOk, _) =
                                    checkSingleSliceComments
                                        allowDirectiveSpanning
                                        deferredRawSpans
                                        lSpan
                                        rSpan
                                        lBuf
                                        rBuf
                                        (max 0 (curI - 1))
                                        inPendS
                                        inPendC
                                        outPendS
                                        outPendC

                                if not pendOk then
                                    struct (true, false, curI, curJ)
                                else
                                    let mutable distinctKinds = true

                                    for x = 0 to remCount - 2 do
                                        let kx = lexerModifierKindSpan lSpan inTokens[curI + x]

                                        for y = x + 1 to remCount - 1 do
                                            if
                                                kx = lexerModifierKindSpan lSpan inTokens[curI + y]
                                            then
                                                distinctKinds <- false

                                    let mutable ok = true

                                    if distinctKinds then
                                        for x = 0 to remCount - 1 do
                                            if ok then
                                                let itok = inTokens[curI + x]

                                                let otok = outTokens[curJ + childSlots[x]]

                                                let struct (trOk, _) =
                                                    checkSingleSliceComments
                                                        allowDirectiveSpanning
                                                        deferredRawSpans
                                                        lSpan
                                                        rSpan
                                                        lBuf
                                                        rBuf
                                                        (curI + x)
                                                        (itok.TriviaStart + itok.LeadingCount)
                                                        itok.TrailingCount
                                                        (otok.TriviaStart + otok.LeadingCount)
                                                        otok.TrailingCount

                                                if not trOk then
                                                    ok <- false

                                    if ok then
                                        let lastIn = inTokens[curI + remCount - 1]
                                        let lastOut = outTokens[curJ + remCount - 1]
                                        let rText = this.EnsureFmtStr(rSpan, &cachedFmt)

                                        let inTrivStart = inTokens[curI].TriviaStart + inLeadSkip

                                        let inTrivEnd =
                                            min
                                                lBuf.LastCommentTrivia
                                                (lastIn.TriviaStart
                                                 + lastIn.LeadingCount
                                                 + lastIn.TrailingCount
                                                 - 1)

                                        let outTrivStart = outTokens[curJ].TriviaStart + outLeadSkip

                                        let outTrivEnd =
                                            min
                                                rBuf.LastCommentTrivia
                                                (lastOut.TriviaStart
                                                 + lastOut.LeadingCount
                                                 + lastOut.TrailingCount
                                                 - 1)

                                        ok <-
                                            this.CheckRangeMultiset(
                                                allowDirectiveSpanning,
                                                deferredRawSpans,
                                                lText,
                                                lBuf,
                                                inTrivStart,
                                                inTrivEnd,
                                                rText,
                                                rBuf,
                                                outTrivStart,
                                                outTrivEnd
                                            )

                                    struct (true, ok, curI + remCount, curJ + remCount)

        member private this.EnsureSlotRetryState(slotId: int) =
            if slotId >= runSlotRetryStates.Length then
                let mutable newLen = max 64 runSlotRetryStates.Length

                while newLen <= slotId do
                    newLen <- newLen * 2

                let nextArr = Array.zeroCreate<UsingSlotRetryState> newLen
                Array.Copy(runSlotRetryStates, nextArr, runSlotRetryStates.Length)
                runSlotRetryStates <- nextArr

            let existing = runSlotRetryStates[slotId]

            if not (isNull existing) then
                existing
            else
                let created = UsingSlotRetryState()
                runSlotRetryStates[slotId] <- created
                created

        member private this.UndoSlotRetryState
            (slotId: int, pendingRaw: ResizeArray<struct (int * int * int * int)>)
            =
            if slotId >= 0 && slotId < runSlotConsumedCount.Length then
                let cnt = runSlotConsumedCount[slotId]

                if cnt > 0 then
                    let startIdx = runSlotConsumedStart[slotId]

                    for i = 0 to cnt - 1 do
                        runInConsumed[runUndoRawIndices[startIdx + i]] <- false

                    if startIdx + cnt = runUndoRawIndices.Count then
                        runUndoRawIndices.RemoveRange(startIdx, cnt)

                    runSlotConsumedCount[slotId] <- 0

                let savedRaw = runSlotSavedRawStart[slotId]

                if not (isNull pendingRaw) && pendingRaw.Count > savedRaw then
                    pendingRaw.RemoveRange(savedRaw, pendingRaw.Count - savedRaw)

            if slotId >= 0 && slotId < runSlotRetryStates.Length then
                let st = runSlotRetryStates[slotId]

                if not (isNull st) then
                    st.RetryMode <- 0

        member private this.MatchUsingClauseSlice
            (
                allowDirectiveSpanning: bool,
                lSpan: ReadOnlySpan<char>,
                lTriv: ReadOnlySpan<Trivia>,
                rSpan: ReadOnlySpan<char>,
                rTriv: ReadOnlySpan<Trivia>,
                outS: int,
                outE: int,
                outHasDoc: bool,
                in1S: int,
                in1E: int,
                in2S: int,
                in2E: int,
                hasOutFooter: bool,
                inClauseFrame: int,
                inClauseRegionDepth: int,
                inClauseRegionSeq: int,
                outClauseFrame: int,
                outClauseRegionDepth: int,
                outClauseRegionSeq: int,
                clauseCount: int,
                bfCount: int,
                bfStartIdx: int,
                bfStartPos: int,
                slotId: int,
                allowMidDocBfStart: bool,
                startPreferSkipIn2: bool,
                pendingRaw: ResizeArray<struct (int * int * int * int)>
            ) =
            let savedRaw = if isNull pendingRaw then 0 else pendingRaw.Count
            let mutable matched = false
            let mutable preferSkipIn2 = startPreferSkipIn2
            let mutable tryNextAttempt = true
            let mutable endBfIdx = bfStartIdx
            let mutable endBfPos = bfStartPos
            let mutable retryMode = 0
            let mutable crossed1Out = false
            let mutable preferSkipOut = startPreferSkipIn2
            let mutable prefixOi = outS
            let mutable prefixIn2 = in2S
            let mutable prefixBfIdx = bfStartIdx
            let mutable prefixBfPos = bfStartPos
            let mutable prefixSavedRaw = savedRaw
            runMergedDocFailedScratch.Clear()
            let frameStack = runClauseStack
            let bfStack = runClauseBfStack
            let matchedRanges = runClauseMatchedRanges
            let memo3 = runClauseMemo3
            let noSkipMemo = runClauseMemo
            let noSkipVisited = runNoSkipVisited

            while not matched && tryNextAttempt do
                tryNextAttempt <- false
                retryMode <- 0
                runConsumedScratch.Clear()

                if not (isNull pendingRaw) && pendingRaw.Count > savedRaw then
                    pendingRaw.RemoveRange(savedRaw, pendingRaw.Count - savedRaw)

                let mutable oi = outS
                let mutable cur2 = in2S
                let mutable prefixOk = true
                let mutable crossed1 = false
                let mutable curBfIdx = bfStartIdx
                let mutable curBfPos = bfStartPos

                if in1S <= in1E then
                    let struct (hOk, nextOi, next2) =
                        tryMatchUsingHeaderPrefix
                            allowDirectiveSpanning
                            inRunComments
                            outRunComments
                            lSpan
                            lTriv
                            rSpan
                            rTriv
                            outS
                            outE
                            in1S
                            in1E
                            in2S
                            in2E
                            runInConsumed
                            runCanGoFooter
                            hasOutFooter
                            preferSkipIn2
                            true
                            inClauseFrame
                            inClauseRegionDepth
                            inClauseRegionSeq
                            outClauseFrame
                            outClauseRegionDepth
                            outClauseRegionSeq
                            runIsFloating
                            runRawOrigSlots
                            runOrderedToRaw
                            runOuterSpanScratch
                            pendingRaw
                            runConsumedScratch
                            runMergedDocFailedScratch
                            runMergedDocLinesScratch
                            runMergedDocSuffixScratch

                    prefixOk <- hOk
                    oi <- nextOi
                    cur2 <- next2
                    crossed1 <- hOk && next2 > in2S

                    if prefixOk && hasOutFooter && crossed1 then
                        let struct (gapsOk, gapBfIdx, gapBfPos) =
                            advanceFooterOverMergedGaps
                                allowDirectiveSpanning
                                allowMidDocBfStart
                                inRunComments
                                lSpan
                                lTriv
                                rSpan
                                rTriv
                                in2S
                                next2
                                runConsumedScratch
                                outBoundaryAndFooterComments
                                outBoundaryRequiresPreCond
                                bfCount
                                runFooterIndex
                                clauseCount
                                inClauseDirSeqs
                                runRawOrigSlots
                                runOrderedToRaw
                                runOuterSpanScratch
                                curBfIdx
                                curBfPos

                        if not gapsOk then
                            prefixOk <- false
                        else
                            curBfIdx <- gapBfIdx
                            curBfPos <- gapBfPos

                let mutable allOk = false
                endBfIdx <- curBfIdx
                endBfPos <- curBfPos

                if prefixOk then
                    let remOut = outE - oi + 1
                    let remIn = in2E - cur2 + 1

                    let remMaxIn =
                        if oi <= outE then
                            outMaxInPrefix[outE + 1] - outMaxInPrefix[oi]
                        else
                            0

                    if remIn < remOut then
                        allOk <- false
                    elif remIn = remOut then
                        allOk <-
                            tryMatchUsingStream2NoSkip
                                allowDirectiveSpanning
                                inRunComments
                                outRunComments
                                lSpan
                                lTriv
                                rSpan
                                rTriv
                                oi
                                outE
                                cur2
                                in2E
                                runInConsumed
                                true
                                inClauseFrame
                                inClauseRegionDepth
                                inClauseRegionSeq
                                outClauseFrame
                                outClauseRegionDepth
                                outClauseRegionSeq
                                runIsFloating
                                runOuterSpanScratch
                                pendingRaw
                                runConsumedScratch
                                null
                                null
                    else
                        let anyFooterEligible =
                            hasOutFooter && cur2 <= in2E && runNextFooterEligible[cur2] <= in2E

                        if anyFooterEligible then
                            let nonFooterCount =
                                runNonFooterPrefix[in2E + 1] - runNonFooterPrefix[cur2]

                            if nonFooterCount > remMaxIn then
                                allOk <- false
                            elif remOut = 0 then
                                if nonFooterCount > 0 then
                                    allOk <- false
                                else
                                    let mutable restOk = true
                                    let mutable k = cur2
                                    let mutable remBfIdx = curBfIdx
                                    let mutable remBfPos = curBfPos

                                    while restOk && k <= in2E do
                                        let origS = runRawOrigSlots[runOrderedToRaw[k]]

                                        let struct (nIdx, nPos) =
                                            advanceUsingFooterCursor
                                                allowDirectiveSpanning
                                                allowMidDocBfStart
                                                lSpan
                                                lTriv
                                                rSpan
                                                rTriv
                                                inRunComments[k]
                                                origS
                                                clauseCount
                                                inClauseDirSeqs
                                                outBoundaryAndFooterComments
                                                outBoundaryRequiresPreCond
                                                bfCount
                                                runFooterIndex
                                                remBfIdx
                                                remBfPos
                                                runOuterSpanScratch

                                        if nIdx < 0 then
                                            restOk <- false
                                        else
                                            remBfIdx <- nIdx
                                            remBfPos <- nPos

                                        k <- k + 1

                                    if restOk then
                                        endBfIdx <- remBfIdx
                                        endBfPos <- remBfPos
                                        allOk <- true
                                        crossed1Out <- crossed1
                                        preferSkipOut <- preferSkipIn2

                                        if
                                            not preferSkipIn2
                                            && in1S <= in1E
                                            && outHasDoc
                                            && crossed1
                                        then
                                            retryMode <- 2
                            elif
                                not (
                                    canMatchUsingSubsequence
                                        allowDirectiveSpanning
                                        inRunComments
                                        outRunComments
                                        lSpan
                                        lTriv
                                        rSpan
                                        rTriv
                                        oi
                                        outE
                                        cur2
                                        in2E
                                        true
                                        inClauseFrame
                                        inClauseRegionDepth
                                        inClauseRegionSeq
                                        outClauseFrame
                                        outClauseRegionDepth
                                        outClauseRegionSeq
                                        runIsFloating
                                        runOuterSpanScratch
                                    && canMatchMandatoryInOut
                                        allowDirectiveSpanning
                                        inRunComments
                                        outRunComments
                                        lSpan
                                        lTriv
                                        rSpan
                                        rTriv
                                        oi
                                        outE
                                        cur2
                                        in2E
                                        runCanGoFooter
                                        true
                                        inClauseFrame
                                        inClauseRegionDepth
                                        inClauseRegionSeq
                                        outClauseFrame
                                        outClauseRegionDepth
                                        outClauseRegionSeq
                                        runIsFloating
                                        runOuterSpanScratch
                                )
                            then
                                allOk <- false
                            else
                                prefixOi <- oi
                                prefixIn2 <- cur2
                                prefixBfIdx <- curBfIdx
                                prefixBfPos <- curBfPos
                                prefixSavedRaw <- if isNull pendingRaw then 0 else pendingRaw.Count
                                runPrefixConsumedScratch.Clear()

                                for pi = 0 to runConsumedScratch.Count - 1 do
                                    runPrefixConsumedScratch.Add runConsumedScratch[pi]

                                noSkipMemo.Clear()
                                memo3.Clear()
                                let mutable skippedEndIdx = curBfIdx
                                let mutable skippedEndPos = curBfPos

                                allOk <-
                                    tryMatchUsingStream2WithSkips
                                        allowDirectiveSpanning
                                        allowMidDocBfStart
                                        false
                                        inRunComments
                                        outRunComments
                                        lSpan
                                        lTriv
                                        rSpan
                                        rTriv
                                        outE
                                        in2E
                                        runCanGoFooter
                                        runInConsumed
                                        true
                                        inClauseFrame
                                        inClauseRegionDepth
                                        inClauseRegionSeq
                                        outClauseFrame
                                        outClauseRegionDepth
                                        outClauseRegionSeq
                                        runIsFloating
                                        inSameRunEnd
                                        outSameRunEnd
                                        runOuterSpanScratch
                                        pendingRaw
                                        runConsumedScratch
                                        matchedRanges
                                        runMergedDocScratch
                                        noSkipMemo
                                        memo3
                                        frameStack
                                        bfStack
                                        noSkipVisited
                                        runMergedDocFailedScratch
                                        runMergedDocLinesScratch
                                        runMergedDocSuffixScratch
                                        outBoundaryAndFooterComments
                                        outBoundaryRequiresPreCond
                                        bfCount
                                        runFooterIndex
                                        bfRemainingMaxIn
                                        outMaxInPrefix
                                        clauseCount
                                        inClauseDirSeqs
                                        runRawOrigSlots
                                        runOrderedToRaw
                                        oi
                                        cur2
                                        curBfIdx
                                        curBfPos
                                        &skippedEndIdx
                                        &skippedEndPos

                                if allOk then
                                    endBfIdx <- skippedEndIdx
                                    endBfPos <- skippedEndPos
                                    crossed1Out <- crossed1
                                    preferSkipOut <- preferSkipIn2

                                    if frameStack.Count > 0 then
                                        retryMode <- 1
                                    elif
                                        not preferSkipIn2
                                        && in1S <= in1E
                                        && outHasDoc
                                        && hasOutFooter
                                        && crossed1
                                    then
                                        retryMode <- 2
                        elif outHasDoc && oi <= outE && remIn <= remMaxIn then
                            allOk <-
                                tryMatchUsingStream2NoSkip
                                    allowDirectiveSpanning
                                    inRunComments
                                    outRunComments
                                    lSpan
                                    lTriv
                                    rSpan
                                    rTriv
                                    oi
                                    outE
                                    cur2
                                    in2E
                                    runInConsumed
                                    true
                                    inClauseFrame
                                    inClauseRegionDepth
                                    inClauseRegionSeq
                                    outClauseFrame
                                    outClauseRegionDepth
                                    outClauseRegionSeq
                                    runIsFloating
                                    runOuterSpanScratch
                                    pendingRaw
                                    runConsumedScratch
                                    null
                                    null
                        else
                            allOk <- false

                matched <- allOk

                if
                    not matched
                    && not preferSkipIn2
                    && in1S <= in1E
                    && outHasDoc
                    && hasOutFooter
                    && crossed1
                then
                    preferSkipIn2 <- true
                    tryNextAttempt <- true

            if matched then
                let consumedStart = runUndoRawIndices.Count

                for idx = 0 to runConsumedScratch.Count - 1 do
                    let rawIdx = runOrderedToRaw[runConsumedScratch[idx]]
                    runInConsumed[rawIdx] <- true

                    if hasOutFooter && slotId >= 0 then
                        runUndoRawIndices.Add rawIdx

                if hasOutFooter && slotId >= 0 then
                    runSlotSavedRawStart[slotId] <- savedRaw
                    runSlotConsumedStart[slotId] <- consumedStart
                    runSlotConsumedCount[slotId] <- runConsumedScratch.Count

                if hasOutFooter && slotId >= 0 && retryMode > 0 then
                    let st = this.EnsureSlotRetryState slotId
                    st.RetryMode <- retryMode
                    st.PreferSkipIn2 <- preferSkipOut
                    st.Crossed1 <- crossed1Out
                    st.OutS <- outS
                    st.OutE <- outE
                    st.OutHasDoc <- outHasDoc
                    st.In1S <- in1S
                    st.In1E <- in1E
                    st.In2S <- in2S
                    st.In2E <- in2E
                    st.InClauseFrame <- inClauseFrame
                    st.InClauseRegionDepth <- inClauseRegionDepth
                    st.InClauseRegionSeq <- inClauseRegionSeq
                    st.OutClauseFrame <- outClauseFrame
                    st.OutClauseRegionDepth <- outClauseRegionDepth
                    st.OutClauseRegionSeq <- outClauseRegionSeq
                    st.BfStartIdx <- bfStartIdx
                    st.BfStartPos <- bfStartPos
                    st.AllowMidDoc <- allowMidDocBfStart
                    st.SavedRawStart <- savedRaw
                    st.EndBfIdx <- endBfIdx
                    st.EndBfPos <- endBfPos

                    if retryMode = 1 then
                        st.PrefixSavedRaw <- prefixSavedRaw
                        st.PrefixOi <- prefixOi
                        st.PrefixIn2 <- prefixIn2
                        st.PrefixBfIdx <- prefixBfIdx
                        st.PrefixBfPos <- prefixBfPos
                        st.PrefixConsumed.Clear()

                        for pi = 0 to runPrefixConsumedScratch.Count - 1 do
                            st.PrefixConsumed.Add runPrefixConsumedScratch[pi]

                        st.FrameStack.Clear()

                        for fi = 0 to frameStack.Count - 1 do
                            st.FrameStack.Add frameStack[fi]

                        st.BfStack.Clear()

                        for bi = 0 to bfStack.Count - 1 do
                            st.BfStack.Add bfStack[bi]

                        st.MatchedRanges.Clear()

                        for mi = 0 to matchedRanges.Count - 1 do
                            st.MatchedRanges.Add matchedRanges[mi]

                        st.Memo3.Clear()

                        for key in memo3 do
                            st.Memo3.Add key |> ignore

                        st.NoSkipMemo.Clear()

                        for key in noSkipMemo do
                            st.NoSkipMemo.Add key |> ignore

                        st.NoSkipVisited.Clear()

                        for vi = 0 to noSkipVisited.Count - 1 do
                            st.NoSkipVisited.Add noSkipVisited[vi]
                elif slotId >= 0 && slotId < runSlotRetryStates.Length then
                    let existing = runSlotRetryStates[slotId]

                    if not (isNull existing) then
                        existing.RetryMode <- 0

                runLastEndBfIdx <- endBfIdx
                runLastEndBfPos <- endBfPos
                true
            else
                if slotId >= 0 && slotId < runSlotRetryStates.Length then
                    let existing = runSlotRetryStates[slotId]

                    if not (isNull existing) then
                        existing.RetryMode <- 0

                if not (isNull pendingRaw) && pendingRaw.Count > savedRaw then
                    pendingRaw.RemoveRange(savedRaw, pendingRaw.Count - savedRaw)

                false

        member private this.ResumeUsingClauseSlice
            (
                allowDirectiveSpanning: bool,
                lSpan: ReadOnlySpan<char>,
                lTriv: ReadOnlySpan<Trivia>,
                rSpan: ReadOnlySpan<char>,
                rTriv: ReadOnlySpan<Trivia>,
                clauseCount: int,
                bfCount: int,
                slotId: int,
                pendingRaw: ResizeArray<struct (int * int * int * int)>
            ) =
            let st = runSlotRetryStates[slotId]
            let mode = st.RetryMode
            this.UndoSlotRetryState(slotId, pendingRaw)

            if mode = 1 then
                runConsumedScratch.Clear()

                for pi = 0 to st.PrefixConsumed.Count - 1 do
                    runConsumedScratch.Add st.PrefixConsumed[pi]

                if st.PrefixSavedRaw > st.SavedRawStart && st.In1S <= st.In1E then
                    let struct (hOk, _, _) =
                        tryMatchUsingHeaderPrefix
                            allowDirectiveSpanning
                            inRunComments
                            outRunComments
                            lSpan
                            lTriv
                            rSpan
                            rTriv
                            st.OutS
                            st.OutE
                            st.In1S
                            st.In1E
                            st.In2S
                            st.In2E
                            runInConsumed
                            runCanGoFooter
                            true
                            st.PreferSkipIn2
                            true
                            st.InClauseFrame
                            st.InClauseRegionDepth
                            st.InClauseRegionSeq
                            st.OutClauseFrame
                            st.OutClauseRegionDepth
                            st.OutClauseRegionSeq
                            runIsFloating
                            runRawOrigSlots
                            runOrderedToRaw
                            runOuterSpanScratch
                            pendingRaw
                            runConsumedScratch
                            runMergedDocFailedScratch
                            runMergedDocLinesScratch
                            runMergedDocSuffixScratch

                    let _ = hOk
                    runConsumedScratch.Clear()

                    for pi = 0 to st.PrefixConsumed.Count - 1 do
                        runConsumedScratch.Add st.PrefixConsumed[pi]

                let mutable skippedEndIdx = st.PrefixBfIdx
                let mutable skippedEndPos = st.PrefixBfPos

                let resumed =
                    tryMatchUsingStream2WithSkips
                        allowDirectiveSpanning
                        st.AllowMidDoc
                        true
                        inRunComments
                        outRunComments
                        lSpan
                        lTriv
                        rSpan
                        rTriv
                        st.OutE
                        st.In2E
                        runCanGoFooter
                        runInConsumed
                        true
                        st.InClauseFrame
                        st.InClauseRegionDepth
                        st.InClauseRegionSeq
                        st.OutClauseFrame
                        st.OutClauseRegionDepth
                        st.OutClauseRegionSeq
                        runIsFloating
                        inSameRunEnd
                        outSameRunEnd
                        runOuterSpanScratch
                        pendingRaw
                        runConsumedScratch
                        st.MatchedRanges
                        runMergedDocScratch
                        st.NoSkipMemo
                        st.Memo3
                        st.FrameStack
                        st.BfStack
                        st.NoSkipVisited
                        runMergedDocFailedScratch
                        runMergedDocLinesScratch
                        runMergedDocSuffixScratch
                        outBoundaryAndFooterComments
                        outBoundaryRequiresPreCond
                        bfCount
                        runFooterIndex
                        bfRemainingMaxIn
                        outMaxInPrefix
                        clauseCount
                        inClauseDirSeqs
                        runRawOrigSlots
                        runOrderedToRaw
                        st.PrefixOi
                        st.PrefixIn2
                        st.PrefixBfIdx
                        st.PrefixBfPos
                        &skippedEndIdx
                        &skippedEndPos

                if resumed then
                    let consumedStart = runUndoRawIndices.Count

                    for idx = 0 to runConsumedScratch.Count - 1 do
                        let rawIdx = runOrderedToRaw[runConsumedScratch[idx]]
                        runInConsumed[rawIdx] <- true
                        runUndoRawIndices.Add rawIdx

                    runSlotSavedRawStart[slotId] <- st.SavedRawStart
                    runSlotConsumedStart[slotId] <- consumedStart
                    runSlotConsumedCount[slotId] <- runConsumedScratch.Count
                    st.EndBfIdx <- skippedEndIdx
                    st.EndBfPos <- skippedEndPos
                    runLastEndBfIdx <- skippedEndIdx
                    runLastEndBfPos <- skippedEndPos

                    if st.FrameStack.Count > 0 then
                        st.RetryMode <- 1
                    elif
                        not st.PreferSkipIn2 && st.In1S <= st.In1E && st.OutHasDoc && st.Crossed1
                    then
                        st.RetryMode <- 2
                    else
                        st.RetryMode <- 0

                    true
                else
                    if not (isNull pendingRaw) && pendingRaw.Count > st.SavedRawStart then
                        pendingRaw.RemoveRange(
                            st.SavedRawStart,
                            pendingRaw.Count - st.SavedRawStart
                        )

                    if
                        not st.PreferSkipIn2 && st.In1S <= st.In1E && st.OutHasDoc && st.Crossed1
                    then
                        this.MatchUsingClauseSlice(
                            allowDirectiveSpanning,
                            lSpan,
                            lTriv,
                            rSpan,
                            rTriv,
                            st.OutS,
                            st.OutE,
                            st.OutHasDoc,
                            st.In1S,
                            st.In1E,
                            st.In2S,
                            st.In2E,
                            true,
                            st.InClauseFrame,
                            st.InClauseRegionDepth,
                            st.InClauseRegionSeq,
                            st.OutClauseFrame,
                            st.OutClauseRegionDepth,
                            st.OutClauseRegionSeq,
                            clauseCount,
                            bfCount,
                            st.BfStartIdx,
                            st.BfStartPos,
                            slotId,
                            st.AllowMidDoc,
                            true,
                            pendingRaw
                        )
                    else
                        st.RetryMode <- 0
                        false
            elif mode = 2 then
                this.MatchUsingClauseSlice(
                    allowDirectiveSpanning,
                    lSpan,
                    lTriv,
                    rSpan,
                    rTriv,
                    st.OutS,
                    st.OutE,
                    st.OutHasDoc,
                    st.In1S,
                    st.In1E,
                    st.In2S,
                    st.In2E,
                    true,
                    st.InClauseFrame,
                    st.InClauseRegionDepth,
                    st.InClauseRegionSeq,
                    st.OutClauseFrame,
                    st.OutClauseRegionDepth,
                    st.OutClauseRegionSeq,
                    clauseCount,
                    bfCount,
                    st.BfStartIdx,
                    st.BfStartPos,
                    slotId,
                    st.AllowMidDoc,
                    true,
                    pendingRaw
                )
            else
                false

        member private this.MatchUsingSlot
            (
                allowDirectiveSpanning: bool,
                lSpan: ReadOnlySpan<char>,
                lTriv: ReadOnlySpan<Trivia>,
                rSpan: ReadOnlySpan<char>,
                rTriv: ReadOnlySpan<Trivia>,
                slotId: int,
                outSlotIdx: int,
                in1S: int,
                in1E: int,
                in2S: int,
                in2E: int,
                hasOutFooter: bool,
                clauseCount: int,
                bfCount: int,
                bfStartIdx: int,
                bfStartPos: int,
                allowMidDocBfStart: bool,
                pendingRaw: ResizeArray<struct (int * int * int * int)>
            ) =
            this.MatchUsingClauseSlice(
                allowDirectiveSpanning,
                lSpan,
                lTriv,
                rSpan,
                rTriv,
                outSlotStarts[outSlotIdx],
                outSlotEnds[outSlotIdx],
                outSlotHasDoc[outSlotIdx],
                in1S,
                in1E,
                in2S,
                in2E,
                hasOutFooter,
                inClauseFrames[slotId],
                inClauseRegionDepths[slotId],
                inClauseRegionSeqs[slotId],
                outClauseFrames[outSlotIdx],
                outClauseRegionDepths[outSlotIdx],
                outClauseRegionSeqs[outSlotIdx],
                clauseCount,
                bfCount,
                bfStartIdx,
                bfStartPos,
                slotId,
                allowMidDocBfStart,
                false,
                pendingRaw
            )

        member private this.MatchesUsingFooter
            (
                allowDirectiveSpanning: bool,
                lSpan: ReadOnlySpan<char>,
                lTriv: ReadOnlySpan<Trivia>,
                rSpan: ReadOnlySpan<char>,
                rTriv: ReadOnlySpan<Trivia>,
                clauseCount: int,
                bfCount: int,
                pendingRaw: ResizeArray<struct (int * int * int * int)>
            ) =
            tryMatchUsingFooterComments
                allowDirectiveSpanning
                rawInRunComments
                outBoundaryAndFooterComments
                lSpan
                lTriv
                rSpan
                rTriv
                0
                (bfCount - 1)
                runInConsumed
                outBoundaryRequiresPreCond
                clauseCount
                runBoundaryCount
                inClauseDirSeqs
                runRawOrigSlots
                runOuterSpanScratch
                pendingRaw
                runConsumedScratch

        member private this.TryResumeOtherUsingSlots
            (
                allowDirectiveSpanning: bool,
                lSpan: ReadOnlySpan<char>,
                lTriv: ReadOnlySpan<Trivia>,
                rSpan: ReadOnlySpan<char>,
                rTriv: ReadOnlySpan<Trivia>,
                clauseCount: int,
                bfCount: int,
                s0: int,
                usingPairs: int array,
                otherCount: int,
                hasFloating: bool,
                anySlotHasDoc: bool,
                otherLastRan: byref<int>,
                curOtherBfIdx: byref<int>,
                curOtherBfPos: byref<int>,
                preS0BfIdx: byref<int>,
                preS0BfPos: byref<int>,
                footerRetryBudget: byref<int>,
                pendingRaw: ResizeArray<struct (int * int * int * int)>
            ) =
            let mutable allOk = false

            while not allOk && footerRetryBudget > 0 do
                let mutable kPos = otherLastRan

                while kPos >= 0
                      && (let ks = runOtherSlotsScratch[kPos]

                          ks >= runSlotRetryStates.Length
                          || isNull runSlotRetryStates[ks]
                          || runSlotRetryStates[ks].RetryMode = 0) do
                    kPos <- kPos - 1

                if kPos < 0 then
                    footerRetryBudget <- 0
                else
                    footerRetryBudget <- footerRetryBudget - 1

                    for uPos = otherLastRan downto kPos + 1 do
                        this.UndoSlotRetryState(runOtherSlotsScratch[uPos], pendingRaw)

                    let ks = runOtherSlotsScratch[kPos]

                    let resumedOk =
                        this.ResumeUsingClauseSlice(
                            allowDirectiveSpanning,
                            lSpan,
                            lTriv,
                            rSpan,
                            rTriv,
                            clauseCount,
                            bfCount,
                            ks,
                            pendingRaw
                        )

                    if not resumedOk then
                        otherLastRan <- kPos - 1
                    else
                        otherLastRan <- kPos

                        if not hasFloating then
                            curOtherBfIdx <- runLastEndBfIdx
                            curOtherBfPos <- runLastEndBfPos

                            if ks < s0 then
                                preS0BfIdx <- curOtherBfIdx
                                preS0BfPos <- curOtherBfPos
                            elif kPos > 0 then
                                let prevKs = runOtherSlotsScratch[kPos - 1]
                                preS0BfIdx <- runSlotPreS0EndBfIdx[prevKs]
                                preS0BfPos <- runSlotPreS0EndBfPos[prevKs]
                            else
                                preS0BfIdx <- 0
                                preS0BfPos <- 0

                        runSlotPreS0EndBfIdx[ks] <- preS0BfIdx
                        runSlotPreS0EndBfPos[ks] <- preS0BfPos
                        let mutable fwdPos = kPos + 1
                        let mutable fwdOk = true

                        while fwdOk && fwdPos < otherCount do
                            let fs = runOtherSlotsScratch[fwdPos]
                            let fj = usingPairs[fs]
                            let bfStartIdx = if hasFloating then 0 else curOtherBfIdx
                            let bfStartPos = if hasFloating then 0 else curOtherBfPos

                            let allowMid =
                                if hasFloating then
                                    anySlotHasDoc
                                else
                                    inSlotHasDoc[0] || (fs > s0 && inSlotHasDoc[s0])

                            fwdOk <-
                                this.MatchUsingSlot(
                                    allowDirectiveSpanning,
                                    lSpan,
                                    lTriv,
                                    rSpan,
                                    rTriv,
                                    fs,
                                    fj,
                                    0,
                                    -1,
                                    inSlotStarts[fs],
                                    inSlotEnds[fs],
                                    true,
                                    clauseCount,
                                    bfCount,
                                    bfStartIdx,
                                    bfStartPos,
                                    allowMid,
                                    pendingRaw
                                )

                            if fwdOk then
                                otherLastRan <- fwdPos

                                if not hasFloating then
                                    curOtherBfIdx <- runLastEndBfIdx
                                    curOtherBfPos <- runLastEndBfPos

                                    if fs < s0 then
                                        preS0BfIdx <- curOtherBfIdx
                                        preS0BfPos <- curOtherBfPos

                                if bfCount > 0 then
                                    runSlotPreS0EndBfIdx[fs] <- preS0BfIdx
                                    runSlotPreS0EndBfPos[fs] <- preS0BfPos

                                fwdPos <- fwdPos + 1

                        allOk <- fwdOk

            allOk

        member private this.CheckUsingRunComments
            (
                allowDirectiveSpanning: bool,
                deferredRawSpans: ResizeArray<struct (int * int * int * int)>,
                lSpan: ReadOnlySpan<char>,
                lBuf: TokenBuffer,
                rSpan: ReadOnlySpan<char>,
                rBuf: TokenBuffer,
                curI: int,
                uInEnd: int,
                uOutEnd: int,
                count: int,
                inFooterSkip: int,
                outFooterSkip: int
            ) =
            let inTokens = lBuf.TokenSpan()
            let lTriv = lBuf.TriviaSpan()
            let outTokens = rBuf.TokenSpan()
            let rTriv = rBuf.TriviaSpan()

            inClauseFrames <- grownIndices inClauseFrames count
            outClauseFrames <- grownIndices outClauseFrames count
            inClauseRegionDepths <- grownIndices inClauseRegionDepths count
            outClauseRegionDepths <- grownIndices outClauseRegionDepths count
            inClauseRegionSeqs <- grownIndices inClauseRegionSeqs count
            outClauseRegionSeqs <- grownIndices outClauseRegionSeqs count
            inClauseDirSeqs <- grownIndices inClauseDirSeqs count
            outClauseDirSeqs <- grownIndices outClauseDirSeqs count
            outBoundaryEndIfDirSeqs <- grownIndices outBoundaryEndIfDirSeqs count
            inSlotStarts <- grownIndices inSlotStarts (count + 1)
            inSlotEnds <- grownIndices inSlotEnds (count + 1)
            inSlotHasDoc <- grownFlags inSlotHasDoc (count + 1)
            outSlotStarts <- grownIndices outSlotStarts (count + 1)
            outSlotEnds <- grownIndices outSlotEnds (count + 1)
            outSlotHasDoc <- grownFlags outSlotHasDoc count
            outSlotNonDocCounts <- grownIndices outSlotNonDocCounts count
            outSlotDocCounts <- grownIndices outSlotDocCounts count
            outSlotDocLines <- grownIndices outSlotDocLines count
            invUsingPairs <- grownIndices invUsingPairs count
            runSlotCounts <- grownIndices runSlotCounts (count + 1)
            runSlotOffsets <- grownIndices runSlotOffsets (count + 1)
            runOtherSlotsScratch <- grownIndices runOtherSlotsScratch count
            runSlotDisplaced <- grownFlags runSlotDisplaced count
            runSlotSavedRawStart <- grownIndices runSlotSavedRawStart count
            runSlotConsumedStart <- grownIndices runSlotConsumedStart count
            runSlotConsumedCount <- grownIndices runSlotConsumedCount count
            runSlotPreS0EndBfIdx <- grownIndices runSlotPreS0EndBfIdx count
            runSlotPreS0EndBfPos <- grownIndices runSlotPreS0EndBfPos count
            Array.fill runSlotConsumedCount 0 count 0
            Array.fill runSlotSavedRawStart 0 count 0
            Array.fill runSlotPreS0EndBfIdx 0 count 0
            Array.fill runSlotPreS0EndBfPos 0 count 0
            runUndoRawIndices.Clear()

            collectUsingRunComments
                lBuf
                inRunIgnoreCursor
                lSpan
                inTokens
                lTriv
                true
                curI
                inUsingLengths
                childSlots
                usingSlots
                count
                uInEnd
                inFooterSkip
                runDirStack
                runEffDirStack
                rawInRunComments
                inSlotStarts
                inSlotEnds
                inClauseFrames
                inClauseRegionDepths
                inClauseRegionSeqs
                inClauseDirSeqs
                null

            collectUsingRunComments
                rBuf
                outRunIgnoreCursor
                rSpan
                outTokens
                rTriv
                false
                0
                inUsingLengths
                childSlots
                usingSlots
                count
                uOutEnd
                outFooterSkip
                runDirStack
                runEffDirStack
                outRunComments
                outSlotStarts
                outSlotEnds
                outClauseFrames
                outClauseRegionDepths
                outClauseRegionSeqs
                outClauseDirSeqs
                outBoundaryEndIfDirSeqs

            if rawInRunComments.Count = 0 && outRunComments.Count = 0 then
                true
            elif (rawInRunComments.Count = 0) <> (outRunComments.Count = 0) then
                false
            else
                for s = 0 to count - 1 do
                    invUsingPairs[usingPairs[s]] <- s

                outBoundaryAndFooterComments.Clear()
                outBoundaryRequiresPreCond.Clear()

                for j = 1 to count - 1 do
                    let outClauseFrame = outClauseFrames[j]
                    let endIfDirSeq = outBoundaryEndIfDirSeqs[j]
                    let origOutS = outSlotStarts[j]
                    let mutable okBoundary = origOutS
                    let outE = outSlotEnds[j]

                    while okBoundary <= outE
                          && ((outRunComments[okBoundary].Frame <> outClauseFrame
                               && (outRunComments[okBoundary].DirSeq > 0
                                   || outRunComments[okBoundary].DirSeq < endIfDirSeq
                                   || isIgnoreEndComment
                                       rSpan
                                       rTriv[outRunComments[okBoundary].TriviaIndex]))
                              || (outRunComments[okBoundary].Frame = outClauseFrame
                                  && outRunComments[okBoundary].DirSeq < endIfDirSeq
                                  && let mk =
                                      ignoreCommentKind
                                          rSpan
                                          rTriv[outRunComments[okBoundary].TriviaIndex] in

                                     mk <> 1 && mk <> 2)) do
                        okBoundary <- okBoundary + 1

                    let sOwner = invUsingPairs[j]

                    let detachEnd =
                        findPairedUsingBoundaryDetachEnd
                            allowDirectiveSpanning
                            lSpan
                            lTriv
                            rSpan
                            rTriv
                            rawInRunComments
                            outRunComments
                            inSlotStarts[sOwner]
                            inSlotEnds[sOwner]
                            inClauseFrames[sOwner]
                            inClauseRegionDepths[sOwner]
                            inClauseRegionSeqs[sOwner]
                            inClauseDirSeqs[sOwner]
                            outClauseFrame
                            outClauseRegionDepths[j]
                            outClauseRegionSeqs[j]
                            outClauseDirSeqs[j]
                            origOutS
                            okBoundary
                            runOuterSpanScratch

                    for bIdx = origOutS to detachEnd - 1 do
                        let oc = outRunComments[bIdx]

                        outBoundaryRequiresPreCond.Add(
                            (oc.DirSeq = 0 || oc.Frame = outClauseFrame)
                            && not (isIgnoreEndComment rSpan rTriv[oc.TriviaIndex])
                        )

                        outBoundaryAndFooterComments.Add oc

                    outSlotStarts[j] <- detachEnd

                let boundaryCount = outBoundaryAndFooterComments.Count
                runBoundaryCount <- boundaryCount

                let mutable maxPrevPair = -1

                for s = 0 to count - 1 do
                    let p = usingPairs[s]
                    runSlotDisplaced[s] <- p < maxPrevPair

                    if p > maxPrevPair then
                        maxPrevPair <- p

                let mutable minNextPair = count

                for s = count - 1 downto 0 do
                    let p = usingPairs[s]

                    if p > minNextPair then
                        runSlotDisplaced[s] <- true

                    if p < minNextPair then
                        minNextPair <- p

                let outCommentCount = outRunComments.Count
                outMaxInPrefix <- grownIndices outMaxInPrefix (outCommentCount + 1)
                outMaxInPrefix[0] <- 0

                for k = 0 to outCommentCount - 1 do
                    let b = rTriv[outRunComments[k].TriviaIndex]

                    let w =
                        if b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                            countDocLines rSpan b
                        else
                            1

                    outMaxInPrefix[k + 1] <- outMaxInPrefix[k] + w

                for j = 0 to count - 1 do
                    let mutable hasDoc = false
                    let mutable nonDocCnt = 0
                    let mutable docCnt = 0
                    let mutable docLineCnt = 0

                    for oi = outSlotStarts[j] to outSlotEnds[j] do
                        let b = rTriv[outRunComments[oi].TriviaIndex]

                        if b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                            hasDoc <- true
                            docCnt <- docCnt + 1
                            docLineCnt <- docLineCnt + countDocLines rSpan b
                        else
                            nonDocCnt <- nonDocCnt + 1

                    outSlotHasDoc[j] <- hasDoc
                    outSlotNonDocCounts[j] <- nonDocCnt
                    outSlotDocCounts[j] <- docCnt
                    outSlotDocLines[j] <- docLineCnt

                for k = outSlotStarts[count] to outSlotEnds[count] do
                    outBoundaryRequiresPreCond.Add false
                    outBoundaryAndFooterComments.Add outRunComments[k]

                let rawCount = rawInRunComments.Count
                runTargetSlots <- grownIndices runTargetSlots rawCount
                runOrderedToRaw <- grownIndices runOrderedToRaw rawCount
                runRawOrigSlots <- grownIndices runRawOrigSlots rawCount
                runRawIsFloating <- grownFlags runRawIsFloating rawCount
                runIsFloating <- grownFlags runIsFloating rawCount
                runInConsumed <- grownFlags runInConsumed rawCount
                runCanGoFooter <- grownFlags runCanGoFooter rawCount
                Array.fill runRawIsFloating 0 rawCount false

                let mutable hasFloating = false

                for s = 0 to count do
                    for k = inSlotStarts[s] to inSlotEnds[s] do
                        runTargetSlots[k] <- s
                        runRawOrigSlots[k] <- s

                runNextClauseFrames.Clear()

                for s = count - 1 downto 1 do
                    let clauseFrame = inClauseFrames[s]
                    let outS = outSlotStarts[usingPairs[s]]
                    let outE = outSlotEnds[usingPairs[s]]
                    let mutable outFramesBuilt = false

                    for k = inSlotStarts[s] to inSlotEnds[s] do
                        let inC = rawInRunComments[k]

                        if inC.Frame <> clauseFrame then
                            if not outFramesBuilt then
                                runOutSlotFrames.Clear()

                                for oi = outS to outE do
                                    runOutSlotFrames.Add outRunComments[oi].Frame |> ignore

                                outFramesBuilt <- true

                            if not (runOutSlotFrames.Contains inC.Frame) then
                                match runNextClauseFrames.TryGetValue inC.Frame with
                                | true, target ->
                                    runTargetSlots[k] <- target
                                    runRawIsFloating[k] <- true
                                    hasFloating <- true
                                | false, _ -> ()

                    runNextClauseFrames[clauseFrame] <- s

                inRunComments.Clear()

                if not hasFloating then
                    for k = 0 to rawCount - 1 do
                        inRunComments.Add rawInRunComments[k]
                        runOrderedToRaw[k] <- k
                        runIsFloating[k] <- false
                else
                    for s = 0 to count do
                        runSlotCounts[s] <- 0

                    for k = 0 to rawCount - 1 do
                        let target = runTargetSlots[k]
                        runSlotCounts[target] <- runSlotCounts[target] + 1

                    let mutable offset = 0

                    for s = 0 to count do
                        let cnt = runSlotCounts[s]
                        inSlotStarts[s] <- offset
                        inSlotEnds[s] <- offset + cnt - 1
                        runSlotOffsets[s] <- offset
                        offset <- offset + cnt

                    while inRunComments.Count < rawCount do
                        inRunComments.Add Unchecked.defaultof<UsingRunComment>

                    for k = 0 to rawCount - 1 do
                        let target = runTargetSlots[k]
                        let pos = runSlotOffsets[target]
                        inRunComments[pos] <- rawInRunComments[k]
                        runOrderedToRaw[pos] <- k
                        runIsFloating[pos] <- runRawIsFloating[k]
                        runSlotOffsets[target] <- pos + 1

                for k = 0 to rawCount - 1 do
                    runInConsumed[k] <- false

                let mutable anySlotHasDoc = false

                for s = 0 to count do
                    let mutable sDoc = false
                    let sEnd = inSlotEnds[s]
                    let mutable k = inSlotStarts[s]

                    while not sDoc && k <= sEnd do
                        if
                            lTriv[inRunComments[k].TriviaIndex].Kind =
                                TriviaKind.SingleLineDocumentationCommentTrivia
                        then
                            sDoc <- true

                        k <- k + 1

                    inSlotHasDoc[s] <- sDoc

                    if sDoc then
                        anySlotHasDoc <- true

                let bfCount = outBoundaryAndFooterComments.Count
                let hasOutFooter = bfCount > 0

                if hasOutFooter then
                    for s = 0 to min (count - 1) (runSlotRetryStates.Length - 1) do
                        if not (isNull runSlotRetryStates[s]) then
                            runSlotRetryStates[s].RetryMode <- 0

                    bfRemainingMaxIn <- grownIndices bfRemainingMaxIn (bfCount + 1)
                    bfRemainingMaxIn[bfCount] <- 0

                    for idx = bfCount - 1 downto 0 do
                        let b = rTriv[outBoundaryAndFooterComments[idx].TriviaIndex]

                        let w =
                            if b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                                countDocLines rSpan b
                            else
                                1

                        bfRemainingMaxIn[idx] <- bfRemainingMaxIn[idx + 1] + w

                    runFooterIndex.Hashes <- grownHashes runFooterIndex.Hashes bfCount

                    runFooterIndex.BfDocStartOff <-
                        grownIndices runFooterIndex.BfDocStartOff bfCount

                    runFooterIndex.BfDocPolyOff <- grownIndices runFooterIndex.BfDocPolyOff bfCount

                    runFooterIndex.BfDocLineCounts <-
                        grownIndices runFooterIndex.BfDocLineCounts bfCount

                    Array.fill runFooterIndex.BfDocStartOff 0 bfCount -1
                    Array.fill runFooterIndex.BfDocLineCounts 0 bfCount 0
                    runFooterDocStates.Clear()
                    runFooterIndex.DocPrefixBfIdxs.Clear()
                    runFooterIndex.DocMidBfIdxs.Clear()
                    runFooterIndex.DocMidStarts.Clear()
                    runFooterIndex.DocMidLineIdxs.Clear()
                    runFooterIndex.DocMidMultiBfIdxs.Clear()
                    runFooterIndex.DocMidMultiStarts.Clear()
                    runFooterIndex.DocMidMultiLineIdxs.Clear()
                    runFooterIndex.IndexedMidLens.Clear()
                    runFooterIndex.DocAllStarts.Clear()
                    runFooterIndex.DocAllPolys.Clear()
                    runFooterIndex.MaxBfDocLines <- 0
                    runDocBfSpansScratch.Clear()
                    runFooterSpanningEntries.Clear()
                    runFooterIndex.SpanningBfIndices.Clear()
                    runFooterIndex.InertBfIdxs.Clear()
                    let mutable docPrefixCount = 0
                    let mutable docMidCount = 0
                    let mutable docMidMultiCount = 0
                    let mutable totalDocMidLines = 0
                    let mutable maxBfDocLines = 0
                    let mutable inertCount = 0

                    for idx = 0 to bfCount - 1 do
                        let outC = outBoundaryAndFooterComments[idx]
                        let b = rTriv[outC.TriviaIndex]
                        let reqPreCond = outBoundaryRequiresPreCond[idx]
                        let hBase = hashUsingCommentKey rSpan b outC outC.DirSeq
                        runFooterIndex.Hashes[idx] <- mixUsingPreCondHash hBase reqPreCond

                        if outC.IsInertIgnoreEnd then
                            if inertCount >= runFooterIndex.InertHashes.Length then
                                runFooterIndex.InertHashes <-
                                    grownHashes runFooterIndex.InertHashes (inertCount + 1)

                            let hEffBase = hashUsingCommentKey rSpan b outC outC.EffDirSeq

                            runFooterIndex.InertHashes[inertCount] <-
                                mixUsingPreCondHash hEffBase reqPreCond

                            runFooterIndex.InertBfIdxs.Add idx
                            inertCount <- inertCount + 1

                        if b.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                            runFooterDocStates.Add(
                                struct (outC.Frame,
                                        outC.Ctx,
                                        outC.RegionDepth,
                                        outC.DirSeq,
                                        reqPreCond)
                            )
                            |> ignore

                            let bFinish = b.Start + b.Length

                            let struct (_, _, next0) = CommentContent.lineSpan rSpan bFinish b.Start

                            if next0 < bFinish then
                                runDocTempStarts.Clear()
                                runDocTempPolys.Clear()
                                runDocTempPolys.Add 0UL
                                let mutable p = b.Start

                                while p < bFinish do
                                    let struct (ls, len, pNext) =
                                        CommentContent.lineSpan rSpan bFinish p

                                    let fp = hashUsingDocLineFp rSpan ls len
                                    let lineNum = runDocTempStarts.Count + 1
                                    let poly = runDocTempPolys[lineNum - 1] * docPolyBase + fp
                                    runDocTempStarts.Add p
                                    runDocTempPolys.Add poly

                                    if pNext < bFinish then
                                        if
                                            docPrefixCount >= runFooterIndex.DocPrefixHashes.Length
                                        then
                                            runFooterIndex.DocPrefixHashes <-
                                                grownHashes
                                                    runFooterIndex.DocPrefixHashes
                                                    (docPrefixCount + 1)

                                        runFooterIndex.DocPrefixHashes[docPrefixCount] <-
                                            mixUsingDocSliceKey outC poly lineNum reqPreCond

                                        runFooterIndex.DocPrefixBfIdxs.Add idx
                                        docPrefixCount <- docPrefixCount + 1

                                    if lineNum >= 2 then
                                        if docMidCount >= runFooterIndex.DocMidHashes.Length then
                                            runFooterIndex.DocMidHashes <-
                                                grownHashes
                                                    runFooterIndex.DocMidHashes
                                                    (docMidCount + 1)

                                        runFooterIndex.DocMidHashes[docMidCount] <-
                                            mixUsingDocSliceKey outC fp 1 reqPreCond

                                        runFooterIndex.DocMidBfIdxs.Add idx
                                        runFooterIndex.DocMidStarts.Add p
                                        runFooterIndex.DocMidLineIdxs.Add(lineNum - 1)
                                        docMidCount <- docMidCount + 1

                                    p <- pNext

                                let kLines = runDocTempStarts.Count
                                totalDocMidLines <- totalDocMidLines + max 0 (kLines - 1)

                                if kLines >= 3 then
                                    if kLines > maxBfDocLines then
                                        maxBfDocLines <- kLines

                                    runFooterIndex.BfDocStartOff[idx] <-
                                        runFooterIndex.DocAllStarts.Count

                                    runFooterIndex.BfDocPolyOff[idx] <-
                                        runFooterIndex.DocAllPolys.Count

                                    runFooterIndex.BfDocLineCounts[idx] <- kLines

                                    for ti = 0 to kLines - 1 do
                                        runFooterIndex.DocAllStarts.Add runDocTempStarts[ti]

                                    for pi = 0 to kLines do
                                        runFooterIndex.DocAllPolys.Add runDocTempPolys[pi]

                                    runDocBfSpansScratch.Add idx
                        elif
                            allowDirectiveSpanning
                            && (b.Kind = TriviaKind.MultiLineCommentTrivia
                                || b.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                            && hasConditionalDirectiveSpanningLine (rSpan.Slice(b.Start, b.Length))
                        then
                            runFooterIndex.SpanningBfIndices.Add idx

                            let struct (rExited, rKept, rLeaves, rSkippedWs) =
                                extractDirectiveCommentSegments (rSpan.Slice(b.Start, b.Length))

                            if rExited then
                                runFooterSpanningEntries.Add
                                    {
                                        Comment = outC
                                        Kind = b.Kind
                                        LeavesCount = rLeaves.Count
                                        HasSkippedWs = rSkippedWs
                                        Kept = rKept
                                        RequiresPreCond = reqPreCond
                                    }

                    runFooterIndex.MaxBfDocLines <- maxBfDocLines

                    if runDocBfSpansScratch.Count > 0 then
                        if runFooterIndex.PowBase.Count = 0 then
                            runFooterIndex.PowBase.Add 1UL

                        while runFooterIndex.PowBase.Count <= maxBfDocLines do
                            runFooterIndex.PowBase.Add(
                                runFooterIndex.PowBase[runFooterIndex.PowBase.Count - 1]
                                * docPolyBase
                            )

                        runDocMidFreqScratch.Clear()
                        runDocMidLensScratch.Clear()
                        runDocSelectedLensScratch.Clear()

                        for k = 0 to rawCount - 1 do
                            let a = lTriv[inRunComments[k].TriviaIndex]

                            if a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia then
                                let aFinish = a.Start + a.Length

                                let struct (_, _, next0) =
                                    CommentContent.lineSpan lSpan aFinish a.Start

                                if next0 < aFinish then
                                    let m = countDocLines lSpan a

                                    if m >= 2 && m < maxBfDocLines then
                                        match runDocMidFreqScratch.TryGetValue m with
                                        | true, cnt -> runDocMidFreqScratch[m] <- cnt + 1
                                        | false, _ -> runDocMidFreqScratch[m] <- 1

                        if runDocMidFreqScratch.Count > 0 then
                            let histLen = maxBfDocLines + 2
                            runDocKHistScratch <- grownIndices runDocKHistScratch histLen
                            runDocKSumScratch <- grownIndices runDocKSumScratch histLen
                            Array.fill runDocKHistScratch 0 histLen 0
                            Array.fill runDocKSumScratch 0 histLen 0

                            for bi = 0 to runDocBfSpansScratch.Count - 1 do
                                let bfIdx = runDocBfSpansScratch[bi]
                                let kl = runFooterIndex.BfDocLineCounts[bfIdx]
                                runDocKHistScratch[kl] <- runDocKHistScratch[kl] + 1
                                runDocKSumScratch[kl] <- runDocKSumScratch[kl] + kl

                            for k = maxBfDocLines downto 0 do
                                runDocKHistScratch[k] <-
                                    runDocKHistScratch[k] + runDocKHistScratch[k + 1]

                                runDocKSumScratch[k] <-
                                    runDocKSumScratch[k] + runDocKSumScratch[k + 1]

                            let costOf (m: int) : int64 =
                                int64 runDocKSumScratch[m + 1]
                                - int64 m * int64 runDocKHistScratch[m + 1]

                            let midBudget = max 256L (4L * int64 totalDocMidLines)
                            let mutable totalCostAll = 0L

                            for kv in runDocMidFreqScratch do
                                runDocMidLensScratch.Add(struct (kv.Key, kv.Value))

                                if totalCostAll <= midBudget then
                                    totalCostAll <- totalCostAll + costOf kv.Key

                            if totalCostAll <= midBudget then
                                for mi = 0 to runDocMidLensScratch.Count - 1 do
                                    let struct (m, _) = runDocMidLensScratch[mi]
                                    runDocSelectedLensScratch.Add m
                                    runFooterIndex.IndexedMidLens.Add m |> ignore
                            else
                                runDocMidLensScratch.Sort(fun struct (m1, f1) struct (m2, f2) ->
                                    let fc = compare f2 f1
                                    if fc <> 0 then fc else compare m1 m2)

                                let cost2 = costOf 2
                                let mutable usedCost = 0L

                                if cost2 > 0L && cost2 <= midBudget then
                                    runDocSelectedLensScratch.Add 2
                                    runFooterIndex.IndexedMidLens.Add 2 |> ignore
                                    usedCost <- cost2

                                for mi = 0 to runDocMidLensScratch.Count - 1 do
                                    let struct (m, _) = runDocMidLensScratch[mi]

                                    if m <> 2 then
                                        let c = costOf m

                                        if c > 0L && c <= midBudget - usedCost then
                                            runDocSelectedLensScratch.Add m
                                            runFooterIndex.IndexedMidLens.Add m |> ignore
                                            usedCost <- usedCost + c

                            runDocSelectedLensScratch.Sort()

                            for bi = 0 to runDocBfSpansScratch.Count - 1 do
                                let bfIdx = runDocBfSpansScratch[bi]
                                let kLines = runFooterIndex.BfDocLineCounts[bfIdx]
                                let startOff = runFooterIndex.BfDocStartOff[bfIdx]
                                let polyOff = runFooterIndex.BfDocPolyOff[bfIdx]
                                let outC = outBoundaryAndFooterComments[bfIdx]
                                let reqPreCond = outBoundaryRequiresPreCond[bfIdx]

                                for s = 1 to kLines - 2 do
                                    let mutable mi = 0

                                    while mi < runDocSelectedLensScratch.Count
                                          && s + runDocSelectedLensScratch[mi] <= kLines do
                                        let m = runDocSelectedLensScratch[mi]

                                        let slicePoly =
                                            runFooterIndex.DocAllPolys[polyOff + s + m]
                                            - runFooterIndex.DocAllPolys[polyOff + s]
                                              * runFooterIndex.PowBase[m]

                                        if
                                            docMidMultiCount
                                            >= runFooterIndex.DocMidMultiHashes.Length
                                        then
                                            runFooterIndex.DocMidMultiHashes <-
                                                grownHashes
                                                    runFooterIndex.DocMidMultiHashes
                                                    (docMidMultiCount + 1)

                                        runFooterIndex.DocMidMultiHashes[docMidMultiCount] <-
                                            mixUsingDocSliceKey outC slicePoly m reqPreCond

                                        runFooterIndex.DocMidMultiBfIdxs.Add bfIdx

                                        runFooterIndex.DocMidMultiStarts.Add
                                            runFooterIndex.DocAllStarts[startOff + s]

                                        runFooterIndex.DocMidMultiLineIdxs.Add s
                                        docMidMultiCount <- docMidMultiCount + 1
                                        mi <- mi + 1

                    let struct (m0, c0, o0, it0) =
                        buildUsingFooterCsr
                            bfCount
                            runFooterIndex.Hashes
                            runFooterIndex.BucketCounts
                            runFooterIndex.BucketOffsets
                            runFooterIndex.BucketItems

                    runFooterIndex.BucketMask <- m0
                    runFooterIndex.BucketCounts <- c0
                    runFooterIndex.BucketOffsets <- o0
                    runFooterIndex.BucketItems <- it0

                    if docPrefixCount > 0 then
                        let struct (mp, cp, op, itp) =
                            buildUsingFooterCsr
                                docPrefixCount
                                runFooterIndex.DocPrefixHashes
                                runFooterIndex.DocPrefixBucketCounts
                                runFooterIndex.DocPrefixBucketOffsets
                                runFooterIndex.DocPrefixBucketItems

                        runFooterIndex.DocPrefixBucketMask <- mp
                        runFooterIndex.DocPrefixBucketCounts <- cp
                        runFooterIndex.DocPrefixBucketOffsets <- op
                        runFooterIndex.DocPrefixBucketItems <- itp

                    if docMidCount > 0 then
                        let struct (mm, cm, om, itm) =
                            buildUsingFooterCsr
                                docMidCount
                                runFooterIndex.DocMidHashes
                                runFooterIndex.DocMidBucketCounts
                                runFooterIndex.DocMidBucketOffsets
                                runFooterIndex.DocMidBucketItems

                        runFooterIndex.DocMidBucketMask <- mm
                        runFooterIndex.DocMidBucketCounts <- cm
                        runFooterIndex.DocMidBucketOffsets <- om
                        runFooterIndex.DocMidBucketItems <- itm

                    if docMidMultiCount > 0 then
                        let struct (mmm, cmm, omm, itmm) =
                            buildUsingFooterCsr
                                docMidMultiCount
                                runFooterIndex.DocMidMultiHashes
                                runFooterIndex.DocMidMultiBucketCounts
                                runFooterIndex.DocMidMultiBucketOffsets
                                runFooterIndex.DocMidMultiBucketItems

                        runFooterIndex.DocMidMultiBucketMask <- mmm
                        runFooterIndex.DocMidMultiBucketCounts <- cmm
                        runFooterIndex.DocMidMultiBucketOffsets <- omm
                        runFooterIndex.DocMidMultiBucketItems <- itmm

                    if inertCount > 0 then
                        let struct (mi, ci, oi, iti) =
                            buildUsingFooterCsr
                                inertCount
                                runFooterIndex.InertHashes
                                runFooterIndex.InertBucketCounts
                                runFooterIndex.InertBucketOffsets
                                runFooterIndex.InertBucketItems

                        runFooterIndex.InertBucketMask <- mi
                        runFooterIndex.InertBucketCounts <- ci
                        runFooterIndex.InertBucketOffsets <- oi
                        runFooterIndex.InertBucketItems <- iti

                    let mutable spanBucketMask = 0

                    if runFooterSpanningEntries.Count > 0 then
                        let spanEntryCount = runFooterSpanningEntries.Count
                        let mutable spanBucketCount = 64

                        while spanBucketCount < spanEntryCount * 2 && spanBucketCount < (1 <<< 30) do
                            spanBucketCount <- spanBucketCount <<< 1

                        runFooterSpanningBuckets <-
                            grownIndices runFooterSpanningBuckets spanBucketCount

                        Array.fill runFooterSpanningBuckets 0 spanBucketCount -1
                        runFooterSpanningNext <- grownIndices runFooterSpanningNext spanEntryCount

                        runFooterSpanningHashes <-
                            grownHashes runFooterSpanningHashes spanEntryCount

                        spanBucketMask <- spanBucketCount - 1

                        for ei = 0 to spanEntryCount - 1 do
                            let entry = runFooterSpanningEntries[ei]

                            let sh =
                                hashDirectiveSpanningKey
                                    entry.Comment
                                    entry.Kind
                                    entry.LeavesCount
                                    entry.Kept

                            runFooterSpanningHashes[ei] <- sh
                            let sb = usingFooterBucketIndex sh spanBucketMask
                            runFooterSpanningNext[ei] <- runFooterSpanningBuckets[sb]
                            runFooterSpanningBuckets[sb] <- ei

                    for k = 0 to rawCount - 1 do
                        let inC = inRunComments[k]
                        let rawIdx = runOrderedToRaw[k]
                        let origSlot = runRawOrigSlots[rawIdx]
                        let a = lTriv[inC.TriviaIndex]
                        let isDoc = a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia

                        let allowDocFooter =
                            not isDoc
                            || origSlot >= count
                            || runSlotDisplaced[origSlot]
                            || runRawIsFloating[rawIdx]
                            || inC.Frame <> inClauseFrames[origSlot]
                            || inC.DirSeq < inClauseDirSeqs[origSlot]
                            || (let outSlot = usingPairs[origSlot]

                                inClauseRegionDepths[origSlot] <> outClauseRegionDepths[outSlot]
                                || inClauseRegionSeqs[origSlot] <> outClauseRegionSeqs[outSlot])

                        let mutable eligible = false

                        if allowDocFooter then
                            let canUsePreCond =
                                origSlot < count && inC.DirSeq < inClauseDirSeqs[origSlot]

                            eligible <-
                                findBestExactFooterMatch
                                    allowDirectiveSpanning
                                    lSpan
                                    lTriv
                                    rSpan
                                    rTriv
                                    inC
                                    a
                                    origSlot
                                    count
                                    inClauseDirSeqs
                                    outBoundaryAndFooterComments
                                    outBoundaryRequiresPreCond
                                    runFooterIndex
                                    0
                                    bfCount
                                    canUsePreCond
                                    runOuterSpanScratch
                                >= 0

                            if not eligible && isDoc then
                                eligible <-
                                    runFooterDocStates.Contains(
                                        struct (inC.Frame,
                                                inC.Ctx,
                                                inC.RegionDepth,
                                                inC.DirSeq,
                                                false)
                                    )
                                    || (canUsePreCond
                                        && runFooterDocStates.Contains(
                                            struct (inC.Frame,
                                                    inC.Ctx,
                                                    inC.RegionDepth,
                                                    inC.DirSeq,
                                                    true)
                                        ))

                            if
                                not eligible
                                && allowDirectiveSpanning
                                && runFooterSpanningEntries.Count > 0
                                && (a.Kind = TriviaKind.MultiLineCommentTrivia
                                    || a.Kind = TriviaKind.MultiLineDocumentationCommentTrivia)
                                && hasConditionalDirectiveSpanningLine (
                                    lSpan.Slice(a.Start, a.Length)
                                )
                            then
                                let struct (lExited, lKept, lLeaves, lSkippedWs) =
                                    extractDirectiveCommentSegments (lSpan.Slice(a.Start, a.Length))

                                if lExited then
                                    let sh = hashDirectiveSpanningKey inC a.Kind lLeaves.Count lKept

                                    let sb = usingFooterBucketIndex sh spanBucketMask
                                    let mutable ei = runFooterSpanningBuckets[sb]

                                    while not eligible && ei >= 0 do
                                        if runFooterSpanningHashes[ei] = sh then
                                            let entry = runFooterSpanningEntries[ei]
                                            let outC = entry.Comment

                                            if
                                                usingFooterPreCondMatches
                                                    entry.RequiresPreCond
                                                    inC
                                                    origSlot
                                                    count
                                                    inClauseDirSeqs
                                                && inC.Frame = outC.Frame
                                                && inC.Ctx = outC.Ctx
                                                && inC.RegionDepth = outC.RegionDepth
                                                && inC.DirSeq = outC.DirSeq
                                                && a.Kind = entry.Kind
                                                && lLeaves.Count = entry.LeavesCount
                                                && (entry.LeavesCount > 0
                                                    || lSkippedWs
                                                    || entry.HasSkippedWs)
                                                && sameDirectiveCommentSegmentList lKept entry.Kept
                                            then
                                                eligible <- true

                                        ei <- runFooterSpanningNext[ei]

                        runCanGoFooter[k] <- eligible

                    runNextFooterEligible <- grownIndices runNextFooterEligible rawCount
                    runNonFooterPrefix <- grownIndices runNonFooterPrefix (rawCount + 1)
                    runNonFooterPrefix[0] <- 0

                    for k = 0 to rawCount - 1 do
                        runNonFooterPrefix[k + 1] <-
                            runNonFooterPrefix[k] + (if runCanGoFooter[k] then 0 else 1)

                    for s = 0 to count do
                        let sStart = inSlotStarts[s]
                        let sEnd = inSlotEnds[s]

                        if sStart <= sEnd then
                            let mutable nextF = sEnd + 1

                            for k = sEnd downto sStart do
                                if runCanGoFooter[k] then
                                    nextF <- k

                                runNextFooterEligible[k] <- nextF

                    inSameRunEnd <- grownIndices inSameRunEnd rawCount

                    for s = 0 to count do
                        let sStart = inSlotStarts[s]
                        let sEnd = inSlotEnds[s]

                        if sStart <= sEnd then
                            inSameRunEnd[sEnd] <- sEnd

                            for k = sEnd - 1 downto sStart do
                                let curC = inRunComments[k]
                                let nextC = inRunComments[k + 1]
                                let a = lTriv[curC.TriviaIndex]
                                let b = lTriv[nextC.TriviaIndex]

                                let canGroup =
                                    runCanGoFooter[k]
                                    && runCanGoFooter[k + 1]
                                    && runIsFloating[k] = runIsFloating[k + 1]
                                    && runRawOrigSlots[runOrderedToRaw[k]] =
                                        runRawOrigSlots[runOrderedToRaw[k + 1]]
                                    && curC.Frame = nextC.Frame
                                    && curC.Ctx = nextC.Ctx
                                    && curC.RegionDepth = nextC.RegionDepth
                                    && curC.RegionSeq = nextC.RegionSeq
                                    && curC.DirSeq = nextC.DirSeq
                                    && a.Kind = b.Kind
                                    && a.Kind <> TriviaKind.SingleLineDocumentationCommentTrivia
                                    && not (
                                        allowDirectiveSpanning
                                        && (a.Kind = TriviaKind.MultiLineCommentTrivia
                                            || a.Kind =
                                                TriviaKind.MultiLineDocumentationCommentTrivia)
                                        && hasConditionalDirectiveSpanningLine (
                                            lSpan.Slice(a.Start, a.Length)
                                        )
                                    )
                                    && (lSpan
                                           .Slice(a.Start, a.Length)
                                           .SequenceEqual(lSpan.Slice(b.Start, b.Length))
                                        || CommentContent.equivalentSpan lSpan a lSpan b)

                                inSameRunEnd[k] <- if canGroup then inSameRunEnd[k + 1] else k

                    outSameRunEnd <- grownIndices outSameRunEnd outCommentCount

                    for j = 0 to count - 1 do
                        let oStart = outSlotStarts[j]
                        let oEnd = outSlotEnds[j]

                        if oStart <= oEnd then
                            outSameRunEnd[oEnd] <- oEnd

                            for k = oEnd - 1 downto oStart do
                                let curC = outRunComments[k]
                                let nextC = outRunComments[k + 1]
                                let a = rTriv[curC.TriviaIndex]
                                let b = rTriv[nextC.TriviaIndex]

                                let canGroup =
                                    curC.Frame = nextC.Frame
                                    && curC.Ctx = nextC.Ctx
                                    && curC.RegionDepth = nextC.RegionDepth
                                    && curC.RegionSeq = nextC.RegionSeq
                                    && a.Kind = b.Kind
                                    && a.Kind <> TriviaKind.SingleLineDocumentationCommentTrivia
                                    && (rSpan
                                           .Slice(a.Start, a.Length)
                                           .SequenceEqual(rSpan.Slice(b.Start, b.Length))
                                        || CommentContent.equivalentSpan rSpan a rSpan b)

                                outSameRunEnd[k] <- if canGroup then outSameRunEnd[k + 1] else k
                else
                    for k = 0 to rawCount - 1 do
                        runCanGoFooter[k] <- false

                runNonDocPrefix <- grownIndices runNonDocPrefix (rawCount + 1)
                runDocCountPrefix <- grownIndices runDocCountPrefix (rawCount + 1)
                runDocLinePrefix <- grownIndices runDocLinePrefix (rawCount + 1)
                runNonFooterNonDocPrefix <- grownIndices runNonFooterNonDocPrefix (rawCount + 1)
                runNonFooterDocPrefix <- grownIndices runNonFooterDocPrefix (rawCount + 1)
                runNonDocPrefix[0] <- 0
                runDocCountPrefix[0] <- 0
                runDocLinePrefix[0] <- 0
                runNonFooterNonDocPrefix[0] <- 0
                runNonFooterDocPrefix[0] <- 0

                for k = 0 to rawCount - 1 do
                    let a = lTriv[inRunComments[k].TriviaIndex]
                    let isDoc = a.Kind = TriviaKind.SingleLineDocumentationCommentTrivia
                    let isMandatory = not runCanGoFooter[k]

                    runNonDocPrefix[k + 1] <- runNonDocPrefix[k] + (if isDoc then 0 else 1)
                    runDocCountPrefix[k + 1] <- runDocCountPrefix[k] + (if isDoc then 1 else 0)

                    runDocLinePrefix[k + 1] <-
                        runDocLinePrefix[k] + (if isDoc then countDocLines lSpan a else 0)

                    runNonFooterNonDocPrefix[k + 1] <-
                        runNonFooterNonDocPrefix[k] + (if isMandatory && not isDoc then 1 else 0)

                    runNonFooterDocPrefix[k + 1] <-
                        runNonFooterDocPrefix[k] + (if isMandatory && isDoc then 1 else 0)

                runTempRawSpans.Clear()

                let pendingRaw =
                    if allowDirectiveSpanning && not (isNull deferredRawSpans) then
                        runTempRawSpans
                    else
                        null

                let mutable ok = true
                let mutable footerRetryBudget = 64

                if usingPairs[0] = 0 then
                    let mutable s = 0
                    let mutable curBfIdx = 0
                    let mutable curBfPos = 0
                    let mutable lastRan = -1

                    while ok && s < count do
                        let j = usingPairs[s]
                        let bfStartIdx = if hasFloating then 0 else curBfIdx
                        let bfStartPos = if hasFloating then 0 else curBfPos

                        ok <-
                            this.MatchUsingSlot(
                                allowDirectiveSpanning,
                                lSpan,
                                lTriv,
                                rSpan,
                                rTriv,
                                s,
                                j,
                                0,
                                -1,
                                inSlotStarts[s],
                                inSlotEnds[s],
                                hasOutFooter,
                                count,
                                bfCount,
                                bfStartIdx,
                                bfStartPos,
                                hasFloating && anySlotHasDoc,
                                pendingRaw
                            )

                        if ok then
                            lastRan <- s

                            if not hasFloating then
                                curBfIdx <- runLastEndBfIdx
                                curBfPos <- runLastEndBfPos

                            s <- s + 1

                    let mutable solved =
                        ok
                        && this.MatchesUsingFooter(
                            allowDirectiveSpanning,
                            lSpan,
                            lTriv,
                            rSpan,
                            rTriv,
                            count,
                            bfCount,
                            pendingRaw
                        )

                    while hasOutFooter && not solved && footerRetryBudget > 0 do
                        let mutable k = lastRan

                        while k >= 0
                              && (k >= runSlotRetryStates.Length
                                  || isNull runSlotRetryStates[k]
                                  || runSlotRetryStates[k].RetryMode = 0) do
                            k <- k - 1

                        if k < 0 then
                            footerRetryBudget <- 0
                        else
                            footerRetryBudget <- footerRetryBudget - 1

                            for u = lastRan downto k + 1 do
                                this.UndoSlotRetryState(u, pendingRaw)

                            let resumedOk =
                                this.ResumeUsingClauseSlice(
                                    allowDirectiveSpanning,
                                    lSpan,
                                    lTriv,
                                    rSpan,
                                    rTriv,
                                    count,
                                    bfCount,
                                    k,
                                    pendingRaw
                                )

                            if not resumedOk then
                                lastRan <- k - 1
                            else
                                curBfIdx <- if hasFloating then 0 else runLastEndBfIdx
                                curBfPos <- if hasFloating then 0 else runLastEndBfPos
                                lastRan <- k
                                let mutable fwd = k + 1
                                let mutable fwdOk = true

                                while fwdOk && fwd < count do
                                    let j = usingPairs[fwd]
                                    let bfStartIdx = if hasFloating then 0 else curBfIdx
                                    let bfStartPos = if hasFloating then 0 else curBfPos

                                    fwdOk <-
                                        this.MatchUsingSlot(
                                            allowDirectiveSpanning,
                                            lSpan,
                                            lTriv,
                                            rSpan,
                                            rTriv,
                                            fwd,
                                            j,
                                            0,
                                            -1,
                                            inSlotStarts[fwd],
                                            inSlotEnds[fwd],
                                            hasOutFooter,
                                            count,
                                            bfCount,
                                            bfStartIdx,
                                            bfStartPos,
                                            hasFloating && anySlotHasDoc,
                                            pendingRaw
                                        )

                                    if fwdOk then
                                        lastRan <- fwd

                                        if not hasFloating then
                                            curBfIdx <- runLastEndBfIdx
                                            curBfPos <- runLastEndBfPos

                                        fwd <- fwd + 1

                                if
                                    fwdOk
                                    && this.MatchesUsingFooter(
                                        allowDirectiveSpanning,
                                        lSpan,
                                        lTriv,
                                        rSpan,
                                        rTriv,
                                        count,
                                        bfCount,
                                        pendingRaw
                                    )
                                then
                                    solved <- true

                    ok <- solved
                else
                    let s0 = invUsingPairs[0]
                    let j0 = usingPairs[0]
                    let mutable otherCount = 0

                    for os = 1 to count - 1 do
                        if os <> s0 then
                            runOtherSlotsScratch[otherCount] <- os
                            otherCount <- otherCount + 1

                    let mutable preS0BfIdx = 0
                    let mutable preS0BfPos = 0
                    let mutable curOtherBfIdx = 0
                    let mutable curOtherBfPos = 0
                    let mutable otherLastRan = -1
                    let mutable oi = 0

                    while ok && oi < otherCount do
                        let s = runOtherSlotsScratch[oi]
                        let j = usingPairs[s]
                        let bfStartIdx = if hasFloating then 0 else curOtherBfIdx
                        let bfStartPos = if hasFloating then 0 else curOtherBfPos

                        let allowMid =
                            if hasFloating then
                                anySlotHasDoc
                            else
                                inSlotHasDoc[0] || (s > s0 && inSlotHasDoc[s0])

                        ok <-
                            this.MatchUsingSlot(
                                allowDirectiveSpanning,
                                lSpan,
                                lTriv,
                                rSpan,
                                rTriv,
                                s,
                                j,
                                0,
                                -1,
                                inSlotStarts[s],
                                inSlotEnds[s],
                                hasOutFooter,
                                count,
                                bfCount,
                                bfStartIdx,
                                bfStartPos,
                                allowMid,
                                pendingRaw
                            )

                        if ok then
                            otherLastRan <- oi

                            if not hasFloating then
                                curOtherBfIdx <- runLastEndBfIdx
                                curOtherBfPos <- runLastEndBfPos

                                if s < s0 then
                                    preS0BfIdx <- curOtherBfIdx
                                    preS0BfPos <- curOtherBfPos

                            if hasOutFooter then
                                runSlotPreS0EndBfIdx[s] <- preS0BfIdx
                                runSlotPreS0EndBfPos[s] <- preS0BfPos

                            oi <- oi + 1

                    if hasOutFooter && not ok && footerRetryBudget > 0 then
                        ok <-
                            this.TryResumeOtherUsingSlots(
                                allowDirectiveSpanning,
                                lSpan,
                                lTriv,
                                rSpan,
                                rTriv,
                                count,
                                bfCount,
                                s0,
                                usingPairs,
                                otherCount,
                                hasFloating,
                                anySlotHasDoc,
                                &otherLastRan,
                                &curOtherBfIdx,
                                &curOtherBfPos,
                                &preS0BfIdx,
                                &preS0BfPos,
                                &footerRetryBudget,
                                pendingRaw
                            )

                    if ok then
                        let mutable baseRaw = if isNull pendingRaw then 0 else pendingRaw.Count
                        let mutable baseUndoCount = runUndoRawIndices.Count
                        let in0S = inSlotStarts[0]
                        let in0E = inSlotEnds[0]
                        let pCount = max 0 (in0E - in0S + 1)
                        let s0S = inSlotStarts[s0]
                        let s0E = inSlotEnds[s0]
                        let s0Count = max 0 (s0E - s0S + 1)
                        let out0Count = max 0 (outSlotEnds[0] - outSlotStarts[0] + 1)
                        let outJ0Count = max 0 (outSlotEnds[j0] - outSlotStarts[j0] + 1)
                        let out0NonDoc = outSlotNonDocCounts[0]
                        let out0Doc = outSlotDocCounts[0]
                        let out0DocLines = outSlotDocLines[0]
                        let out0MaxIn = out0NonDoc + out0DocLines
                        let outJ0NonDoc = outSlotNonDocCounts[j0]
                        let outJ0Doc = outSlotDocCounts[j0]
                        let outJ0DocLines = outSlotDocLines[j0]
                        let outJ0MaxIn = outJ0NonDoc + outJ0DocLines
                        let bfMaxIn = if hasOutFooter then bfRemainingMaxIn[0] else 0

                        let in0HasFooter =
                            hasOutFooter && in0S <= in0E && runNextFooterEligible[in0S] <= in0E

                        let s0HasFooter =
                            hasOutFooter && s0S <= s0E && runNextFooterEligible[s0S] <= s0E

                        let s0NonDoc =
                            if s0S <= s0E then
                                runNonDocPrefix[s0E + 1] - runNonDocPrefix[s0S]
                            else
                                0

                        let s0Doc =
                            if s0S <= s0E then
                                runDocCountPrefix[s0E + 1] - runDocCountPrefix[s0S]
                            else
                                0

                        let s0DocLines =
                            if s0S <= s0E then
                                runDocLinePrefix[s0E + 1] - runDocLinePrefix[s0S]
                            else
                                0

                        let s0NonFooterNonDoc =
                            if s0S <= s0E then
                                runNonFooterNonDocPrefix[s0E + 1] - runNonFooterNonDocPrefix[s0S]
                            else
                                0

                        let s0NonFooterDoc =
                            if s0S <= s0E then
                                runNonFooterDocPrefix[s0E + 1] - runNonFooterDocPrefix[s0S]
                            else
                                0

                        let hUpper =
                            if (pCount + s0Count) - (out0MaxIn + outJ0MaxIn) > bfMaxIn then
                                -1
                            else
                                let rawUpper =
                                    if out0Count = 0 then
                                        0
                                    else
                                        maxUsingHeaderSplitPrefix
                                            allowDirectiveSpanning
                                            inRunComments
                                            outRunComments
                                            lSpan
                                            lTriv
                                            rSpan
                                            rTriv
                                            in0S
                                            in0E
                                            outSlotStarts[0]
                                            outSlotEnds[0]
                                            runOuterSpanScratch

                                let mutable u =
                                    min
                                        rawUpper
                                        (min (pCount - outJ0Count) (out0MaxIn + bfMaxIn - s0Count))

                                if pCount > 0 then
                                    u <-
                                        min
                                            u
                                            (maxSplitForSuffixMin
                                                runNonDocPrefix
                                                in0S
                                                pCount
                                                outJ0NonDoc)

                                    u <-
                                        min
                                            u
                                            (maxSplitForSuffixMin
                                                runDocCountPrefix
                                                in0S
                                                pCount
                                                outJ0Doc)

                                    u <-
                                        min
                                            u
                                            (maxSplitForSuffixMin
                                                runDocLinePrefix
                                                in0S
                                                pCount
                                                outJ0DocLines)

                                    u <-
                                        min
                                            u
                                            (maxSplitForPrefixMax
                                                runNonDocPrefix
                                                in0S
                                                pCount
                                                (out0NonDoc - s0NonFooterNonDoc))

                                    u <-
                                        min
                                            u
                                            (maxSplitForPrefixMax
                                                runDocCountPrefix
                                                in0S
                                                pCount
                                                (out0DocLines - s0NonFooterDoc))
                                elif
                                    outJ0Count > 0
                                    || s0NonFooterNonDoc > out0NonDoc
                                    || s0NonFooterDoc > out0DocLines
                                then
                                    u <- -1

                                u

                        let hLower =
                            let mutable l =
                                max
                                    (if outJ0Count = 0 && not hasOutFooter then pCount else 0)
                                    (max
                                        (max 0 (out0Count - s0Count))
                                        (pCount - outJ0MaxIn - bfMaxIn))

                            if pCount > 0 then
                                l <-
                                    max
                                        l
                                        (minSplitForSuffixMax
                                            runNonFooterNonDocPrefix
                                            in0S
                                            pCount
                                            outJ0NonDoc)

                                l <-
                                    max
                                        l
                                        (minSplitForSuffixMax
                                            runNonFooterDocPrefix
                                            in0S
                                            pCount
                                            outJ0DocLines)

                                l <-
                                    max
                                        l
                                        (minSplitForPrefixMin
                                            runNonDocPrefix
                                            in0S
                                            pCount
                                            (max 0 (out0NonDoc - s0NonDoc)))

                                l <-
                                    max
                                        l
                                        (minSplitForPrefixMin
                                            runDocCountPrefix
                                            in0S
                                            pCount
                                            (max 0 (out0Doc - s0Doc)))

                                l <-
                                    max
                                        l
                                        (minSplitForPrefixMin
                                            runDocLinePrefix
                                            in0S
                                            pCount
                                            (max 0 (out0DocLines - s0DocLines)))

                            l

                        let mutable foundSplit = false
                        let mutable otherRetryBudget = 16
                        let mutable tryOtherAgain = true

                        while not foundSplit && tryOtherAgain do
                            tryOtherAgain <- false
                            let mutable dirtyConsumed = false
                            let mutable h = min pCount hUpper

                            while not foundSplit && h >= hLower do
                                if dirtyConsumed then
                                    for k = in0S to in0E do
                                        runInConsumed[runOrderedToRaw[k]] <- false

                                    for k = s0S to s0E do
                                        runInConsumed[runOrderedToRaw[k]] <- false

                                    dirtyConsumed <- false

                                if not (isNull pendingRaw) && pendingRaw.Count > baseRaw then
                                    pendingRaw.RemoveRange(baseRaw, pendingRaw.Count - baseRaw)

                                if runUndoRawIndices.Count > baseUndoCount then
                                    runUndoRawIndices.RemoveRange(
                                        baseUndoCount,
                                        runUndoRawIndices.Count - baseUndoCount
                                    )

                                runSlotConsumedCount[0] <- 0
                                runSlotConsumedCount[s0] <- 0

                                let mutable j0Ok =
                                    this.MatchUsingSlot(
                                        allowDirectiveSpanning,
                                        lSpan,
                                        lTriv,
                                        rSpan,
                                        rTriv,
                                        0,
                                        j0,
                                        0,
                                        -1,
                                        in0S + h,
                                        in0E,
                                        hasOutFooter,
                                        count,
                                        bfCount,
                                        0,
                                        0,
                                        hasFloating && anySlotHasDoc,
                                        pendingRaw
                                    )

                                let j0HadInitialMatch = j0Ok
                                let mutable s0HadAnyMatch = false

                                if j0Ok then
                                    dirtyConsumed <- true

                                while not foundSplit && j0Ok do
                                    let mutable s0BfIdx = 0
                                    let mutable s0BfPos = 0

                                    if not hasFloating then
                                        if
                                            runLastEndBfIdx > preS0BfIdx
                                            || (runLastEndBfIdx = preS0BfIdx
                                                && runLastEndBfPos > preS0BfPos)
                                        then
                                            s0BfIdx <- runLastEndBfIdx
                                            s0BfPos <- runLastEndBfPos
                                        else
                                            s0BfIdx <- preS0BfIdx
                                            s0BfPos <- preS0BfPos

                                    let s0Ok =
                                        this.MatchUsingSlot(
                                            allowDirectiveSpanning,
                                            lSpan,
                                            lTriv,
                                            rSpan,
                                            rTriv,
                                            s0,
                                            0,
                                            in0S,
                                            in0S + h - 1,
                                            s0S,
                                            s0E,
                                            hasOutFooter,
                                            count,
                                            bfCount,
                                            s0BfIdx,
                                            s0BfPos,
                                            hasFloating && anySlotHasDoc,
                                            pendingRaw
                                        )

                                    if s0Ok then
                                        s0HadAnyMatch <- true

                                        if
                                            this.MatchesUsingFooter(
                                                allowDirectiveSpanning,
                                                lSpan,
                                                lTriv,
                                                rSpan,
                                                rTriv,
                                                count,
                                                bfCount,
                                                pendingRaw
                                            )
                                        then
                                            foundSplit <- true

                                    while hasOutFooter
                                          && not foundSplit
                                          && footerRetryBudget > 0
                                          && s0 < runSlotRetryStates.Length
                                          && not (isNull runSlotRetryStates[s0])
                                          && runSlotRetryStates[s0].RetryMode > 0 do
                                        footerRetryBudget <- footerRetryBudget - 1

                                        let s0ResOk =
                                            this.ResumeUsingClauseSlice(
                                                allowDirectiveSpanning,
                                                lSpan,
                                                lTriv,
                                                rSpan,
                                                rTriv,
                                                count,
                                                bfCount,
                                                s0,
                                                pendingRaw
                                            )

                                        if s0ResOk then
                                            s0HadAnyMatch <- true

                                            if
                                                this.MatchesUsingFooter(
                                                    allowDirectiveSpanning,
                                                    lSpan,
                                                    lTriv,
                                                    rSpan,
                                                    rTriv,
                                                    count,
                                                    bfCount,
                                                    pendingRaw
                                                )
                                            then
                                                foundSplit <- true

                                    if not foundSplit then
                                        if
                                            hasOutFooter
                                            && footerRetryBudget > 0
                                            && 0 < runSlotRetryStates.Length
                                            && not (isNull runSlotRetryStates[0])
                                            && runSlotRetryStates[0].RetryMode > 0
                                        then
                                            this.UndoSlotRetryState(s0, pendingRaw)
                                            footerRetryBudget <- footerRetryBudget - 1

                                            j0Ok <-
                                                this.ResumeUsingClauseSlice(
                                                    allowDirectiveSpanning,
                                                    lSpan,
                                                    lTriv,
                                                    rSpan,
                                                    rTriv,
                                                    count,
                                                    bfCount,
                                                    0,
                                                    pendingRaw
                                                )
                                        else
                                            j0Ok <- false

                                if not foundSplit then
                                    if j0HadInitialMatch then
                                        if s0HadAnyMatch && not in0HasFooter && not s0HasFooter then
                                            h <- hLower - 1
                                        else
                                            h <- h - 1
                                    elif
                                        hasOutFooter
                                        && in0S + h <= in0E
                                        && inSameRunEnd[in0S + h] - (in0S + h) + 1 >= outJ0NonDoc
                                    then
                                        let mutable nextH = h - 1

                                        while nextH >= hLower
                                              && inSameRunEnd[in0S + nextH] >= in0S + h do
                                            nextH <- nextH - 1

                                        h <- nextH
                                    else
                                        h <- h - 1

                            if
                                not foundSplit
                                && hasOutFooter
                                && otherRetryBudget > 0
                                && footerRetryBudget > 0
                                && otherCount > 0
                            then
                                if dirtyConsumed then
                                    for k = in0S to in0E do
                                        runInConsumed[runOrderedToRaw[k]] <- false

                                    for k = s0S to s0E do
                                        runInConsumed[runOrderedToRaw[k]] <- false

                                if not (isNull pendingRaw) && pendingRaw.Count > baseRaw then
                                    pendingRaw.RemoveRange(baseRaw, pendingRaw.Count - baseRaw)

                                if runUndoRawIndices.Count > baseUndoCount then
                                    runUndoRawIndices.RemoveRange(
                                        baseUndoCount,
                                        runUndoRawIndices.Count - baseUndoCount
                                    )

                                runSlotConsumedCount[0] <- 0
                                runSlotConsumedCount[s0] <- 0

                                otherRetryBudget <- otherRetryBudget - 1

                                if
                                    this.TryResumeOtherUsingSlots(
                                        allowDirectiveSpanning,
                                        lSpan,
                                        lTriv,
                                        rSpan,
                                        rTriv,
                                        count,
                                        bfCount,
                                        s0,
                                        usingPairs,
                                        otherCount,
                                        hasFloating,
                                        anySlotHasDoc,
                                        &otherLastRan,
                                        &curOtherBfIdx,
                                        &curOtherBfPos,
                                        &preS0BfIdx,
                                        &preS0BfPos,
                                        &footerRetryBudget,
                                        pendingRaw
                                    )
                                then
                                    baseRaw <- if isNull pendingRaw then 0 else pendingRaw.Count
                                    baseUndoCount <- runUndoRawIndices.Count
                                    tryOtherAgain <- true

                        ok <- foundSplit

                if ok && not (isNull pendingRaw) && pendingRaw.Count > 0 then
                    for pi = 0 to pendingRaw.Count - 1 do
                        deferredRawSpans.Add pendingRaw[pi]

                ok

        member private this.CheckUsingRunPermuted
            (
                isOuter: bool,
                allowDirectiveSpanning: bool,
                deferredRawSpans: ResizeArray<struct (int * int * int * int)>,
                lText: string,
                lSpan: ReadOnlySpan<char>,
                rSpan: ReadOnlySpan<char>,
                lBuf: TokenBuffer,
                rBuf: TokenBuffer,
                curI: int,
                curJ: int,
                inPendS: int,
                inPendC: int,
                outPendS: int,
                outPendC: int,
                unchangedUsingEndI: byref<int>,
                cachedFmt: byref<string>
            ) =
            let inTokens = lBuf.TokenSpan()
            let outTokens = rBuf.TokenSpan()
            let inCount = inTokens.Length
            let outCount = outTokens.Length

            if
                not isOuter
                || curI < unchangedUsingEndI
                || curI >= inCount - 1
                || curJ >= outCount - 1
            then
                struct (false, false, curI, curJ, 0, 0)
            else
                let inFirst = inTokens[curI]
                let outFirst = outTokens[curJ]

                let inLooksUsing =
                    inFirst.Kind = TokenKind.UsingKeyword
                    || (inFirst.Kind = TokenKind.IdentifierToken
                        && inFirst.Length = 6
                        && lSpan.Slice(inFirst.Start, 6).SequenceEqual("global".AsSpan())
                        && (inTokens[curI + 1]).Kind = TokenKind.UsingKeyword)

                let outLooksUsing =
                    outFirst.Kind = TokenKind.UsingKeyword
                    || (outFirst.Kind = TokenKind.IdentifierToken
                        && outFirst.Length = 6
                        && rSpan.Slice(outFirst.Start, 6).SequenceEqual("global".AsSpan())
                        && (outTokens[curJ + 1]).Kind = TokenKind.UsingKeyword)

                if not inLooksUsing || not outLooksUsing then
                    struct (false, false, curI, curJ, 0, 0)
                else
                    let struct (validScope, count, totalTokens) =
                        findUsingRunScope false 1 lText curI

                    let mutable outTotalTokens = 0

                    if not validScope || count < 1 || curI + totalTokens > inCount then
                        struct (false, false, curI, curJ, 0, 0)
                    else
                        usingPairs <- grownIndices usingPairs count

                        if
                            not (
                                pairUsingClauses
                                    lSpan
                                    rSpan
                                    curI
                                    curJ
                                    count
                                    totalTokens
                                    true
                                    false
                                    usingPairs
                                    &outTotalTokens
                            )
                        then
                            unchangedUsingEndI <- curI + totalTokens
                            struct (false, false, curI, curJ, 0, 0)
                        else
                            let mutable allInOrder = true

                            for s = 0 to count - 1 do
                                if usingPairs[s] <> s then
                                    allInOrder <- false

                            let uInEnd = curI + totalTokens
                            let uOutEnd = curJ + outTotalTokens
                            let lTriv = lBuf.TriviaSpan()
                            let rTriv = rBuf.TriviaSpan()
                            let mutable preInSkip = 0
                            let mutable preOutSkip = 0
                            let mutable cachedRText: string = null
                            let mutable runPermsOrFooter = not allInOrder && count >= 2

                            if
                                not runPermsOrFooter
                                && uInEnd < inCount
                                && uOutEnd < outCount
                                && (hasFooterDirectiveOrIgnoreEnd lSpan lTriv inTokens[uInEnd]
                                    || hasFooterDirectiveOrIgnoreEnd rSpan rTriv outTokens[uOutEnd])
                            then
                                let rText = this.EnsureFmtStr(rSpan, &cachedFmt)
                                cachedRText <- rText

                                let struct (inFooterSkip, outFooterSkip, hasAnyCondFooter) =
                                    usingFooterPrefixLengths
                                        lText
                                        lSpan
                                        lTriv
                                        inTokens[uInEnd]
                                        rText
                                        rSpan
                                        rTriv
                                        outTokens[uOutEnd]

                                preInSkip <- inFooterSkip
                                preOutSkip <- outFooterSkip

                                runPermsOrFooter <-
                                    hasAnyCondFooter || inFooterSkip <> outFooterSkip

                            if not runPermsOrFooter then
                                unchangedUsingEndI <- curI + totalTokens
                                struct (false, false, curI, curJ, 0, 0)
                            else
                                let struct (pendOk, _) =
                                    checkSingleSliceComments
                                        allowDirectiveSpanning
                                        deferredRawSpans
                                        lSpan
                                        rSpan
                                        lBuf
                                        rBuf
                                        (max 0 (curI - 1))
                                        inPendS
                                        inPendC
                                        outPendS
                                        outPendC

                                if not pendOk then
                                    struct (true, false, curI, curJ, 0, 0)
                                else
                                    let mutable ok = true
                                    let mutable inClauseStart = curI
                                    let mutable slot = 0

                                    while ok && slot < count do
                                        let inLen = inUsingLengths[slot]
                                        let outIdx = usingPairs[slot]
                                        let outClauseStart = childSlots[outIdx]
                                        let outLen = usingSlots[outIdx]

                                        let mutable ti = 0
                                        let mutable tj = 0

                                        while ok && ti < inLen && tj < outLen do
                                            let itok = inTokens[inClauseStart + ti]
                                            let otok = outTokens[outClauseStart + tj]

                                            let inW = greaterWidth itok.Kind
                                            let outW = greaterWidth otok.Kind

                                            if inW > 0 && outW > 0 && itok.Kind <> otok.Kind then
                                                let mutable ci = ti
                                                let mutable cj = tj
                                                let mutable inGt = inW
                                                let mutable outGt = outW

                                                while ok && inGt <> outGt do
                                                    if inGt < outGt then
                                                        let tPrev = inTokens[inClauseStart + ci]
                                                        let tNext = inTokens[inClauseStart + ci + 1]

                                                        if
                                                            sliceHasComment
                                                                lBuf
                                                                lTriv
                                                                (tPrev.TriviaStart
                                                                 + tPrev.LeadingCount)
                                                                tPrev.TrailingCount
                                                            || sliceHasComment
                                                                lBuf
                                                                lTriv
                                                                tNext.TriviaStart
                                                                tNext.LeadingCount
                                                        then
                                                            ok <- false
                                                        else
                                                            ci <- ci + 1

                                                            inGt <-
                                                                inGt
                                                                + greaterWidth
                                                                    inTokens[inClauseStart + ci]
                                                                        .Kind
                                                    else
                                                        let tPrev = outTokens[outClauseStart + cj]

                                                        let tNext =
                                                            outTokens[outClauseStart + cj + 1]

                                                        if
                                                            sliceHasComment
                                                                rBuf
                                                                rTriv
                                                                (tPrev.TriviaStart
                                                                 + tPrev.LeadingCount)
                                                                tPrev.TrailingCount
                                                            || sliceHasComment
                                                                rBuf
                                                                rTriv
                                                                tNext.TriviaStart
                                                                tNext.LeadingCount
                                                        then
                                                            ok <- false
                                                        else
                                                            cj <- cj + 1

                                                            outGt <-
                                                                outGt
                                                                + greaterWidth
                                                                    outTokens[outClauseStart + cj]
                                                                        .Kind

                                                if ok && ti > 0 then
                                                    let struct (lOk, _) =
                                                        checkSingleSliceComments
                                                            allowDirectiveSpanning
                                                            deferredRawSpans
                                                            lSpan
                                                            rSpan
                                                            lBuf
                                                            rBuf
                                                            (inClauseStart + ti)
                                                            itok.TriviaStart
                                                            itok.LeadingCount
                                                            otok.TriviaStart
                                                            otok.LeadingCount

                                                    if not lOk then
                                                        ok <- false

                                                if ok then
                                                    let endIn = inTokens[inClauseStart + ci]
                                                    let endOut = outTokens[outClauseStart + cj]

                                                    let struct (tOk, _) =
                                                        checkSingleSliceComments
                                                            allowDirectiveSpanning
                                                            deferredRawSpans
                                                            lSpan
                                                            rSpan
                                                            lBuf
                                                            rBuf
                                                            (inClauseStart + ci)
                                                            (endIn.TriviaStart + endIn.LeadingCount)
                                                            endIn.TrailingCount
                                                            (endOut.TriviaStart
                                                             + endOut.LeadingCount)
                                                            endOut.TrailingCount

                                                    if not tOk then
                                                        ok <- false

                                                ti <- ci + 1
                                                tj <- cj + 1
                                            else
                                                if ti > 0 then
                                                    let struct (lOk, _) =
                                                        checkSingleSliceComments
                                                            allowDirectiveSpanning
                                                            deferredRawSpans
                                                            lSpan
                                                            rSpan
                                                            lBuf
                                                            rBuf
                                                            (inClauseStart + ti)
                                                            itok.TriviaStart
                                                            itok.LeadingCount
                                                            otok.TriviaStart
                                                            otok.LeadingCount

                                                    if not lOk then
                                                        ok <- false

                                                if ok then
                                                    let struct (tOk, _) =
                                                        checkSingleSliceComments
                                                            allowDirectiveSpanning
                                                            deferredRawSpans
                                                            lSpan
                                                            rSpan
                                                            lBuf
                                                            rBuf
                                                            (inClauseStart + ti)
                                                            (itok.TriviaStart + itok.LeadingCount)
                                                            itok.TrailingCount
                                                            (otok.TriviaStart + otok.LeadingCount)
                                                            otok.TrailingCount

                                                    if not tOk then
                                                        ok <- false

                                                ti <- ti + 1
                                                tj <- tj + 1

                                        inClauseStart <- inClauseStart + inLen
                                        slot <- slot + 1

                                    let mutable inIgnSkip = 0
                                    let mutable outIgnSkip = 0

                                    if ok then
                                        let struct (inFooterSkip, outFooterSkip) =
                                            if not (isNull cachedRText) then
                                                struct (preInSkip, preOutSkip)
                                            else
                                                let rText = this.EnsureFmtStr(rSpan, &cachedFmt)

                                                let struct (inSkip, outSkip, _) =
                                                    usingFooterPrefixLengths
                                                        lText
                                                        lSpan
                                                        lTriv
                                                        inTokens[uInEnd]
                                                        rText
                                                        rSpan
                                                        rTriv
                                                        outTokens[uOutEnd]

                                                struct (inSkip, outSkip)

                                        inIgnSkip <- inFooterSkip
                                        outIgnSkip <- outFooterSkip

                                        ok <-
                                            this.CheckUsingRunComments(
                                                allowDirectiveSpanning,
                                                deferredRawSpans,
                                                lSpan,
                                                lBuf,
                                                rSpan,
                                                rBuf,
                                                curI,
                                                uInEnd,
                                                uOutEnd,
                                                count,
                                                inFooterSkip,
                                                outFooterSkip
                                            )

                                    struct (true,
                                            ok,
                                            curI + totalTokens,
                                            curJ + outTotalTokens,
                                            inIgnSkip,
                                            outIgnSkip)

        member private this.CheckAnchoredSpan
            (
                depth: int,
                isOuter: bool,
                allowDirectiveSpanning: bool,
                deferredRawSpans: ResizeArray<struct (int * int * int * int)>,
                lText: string,
                lSpan: ReadOnlySpan<char>,
                rSpan: ReadOnlySpan<char>,
                lBuf: TokenBuffer,
                rBuf: TokenBuffer,
                startTok: int,
                cachedFmt: byref<string>
            ) : struct (bool * string * bool) =
            let inTokens = lBuf.TokenSpan()
            let outTokens = rBuf.TokenSpan()
            let inCount = inTokens.Length
            let outCount = outTokens.Length
            let mutable i = startTok
            let mutable j = startTok
            let mutable inPendS = 0
            let mutable inPendC = 0
            let mutable outPendS = 0
            let mutable outPendC = 0
            let mutable inLeadSkip = 0
            let mutable outLeadSkip = 0
            let mutable failedComment = false
            let mutable failedHole = false
            let mutable mismatchKey = ""
            let mutable tokenStopped = false
            let mutable unchangedUsingEndI = 0

            while not failedComment && not tokenStopped && i < inCount && j < outCount do
                let inHead = inTokens[i]

                let struct (uHandled, uOk, uNextI, uNextJ, uInIgn, uOutIgn) =
                    if
                        isOuter
                        && i >= unchangedUsingEndI
                        && (inHead.Kind = TokenKind.UsingKeyword
                            || (inHead.Kind = TokenKind.IdentifierToken && inHead.Length = 6))
                    then
                        this.CheckUsingRunPermuted(
                            isOuter,
                            allowDirectiveSpanning,
                            deferredRawSpans,
                            lText,
                            lSpan,
                            rSpan,
                            lBuf,
                            rBuf,
                            i,
                            j,
                            inPendS,
                            inPendC,
                            outPendS,
                            outPendC,
                            &unchangedUsingEndI,
                            &cachedFmt
                        )
                    else
                        struct (false, false, i, j, 0, 0)

                if uHandled then
                    if not uOk then
                        failedComment <- true
                    else
                        i <- uNextI
                        j <- uNextJ
                        inPendS <- 0
                        inPendC <- 0
                        outPendS <- 0
                        outPendC <- 0
                        inLeadSkip <- uInIgn
                        outLeadSkip <- uOutIgn
                else
                    let struct (mHandled, mOk, mNextI, mNextJ) =
                        if
                            isOuter
                            && (DeclaredTransformations.isModifierTokenKind inHead.Kind
                                || (inHead.Kind = TokenKind.IdentifierToken
                                    && (inHead.Length = 4
                                        || inHead.Length = 5
                                        || inHead.Length = 7
                                        || inHead.Length = 8)))
                        then
                            this.CheckModRunPermuted(
                                isOuter,
                                allowDirectiveSpanning,
                                deferredRawSpans,
                                lText,
                                lSpan,
                                rSpan,
                                lBuf,
                                rBuf,
                                i,
                                j,
                                inLeadSkip,
                                outLeadSkip,
                                inPendS,
                                inPendC,
                                outPendS,
                                outPendC,
                                &cachedFmt
                            )
                        else
                            struct (false, false, i, j)

                    if mHandled then
                        if not mOk then
                            failedComment <- true
                        else
                            i <- mNextI
                            j <- mNextJ
                            inPendS <- 0
                            inPendC <- 0
                            outPendS <- 0
                            outPendC <- 0
                            inLeadSkip <- 0
                            outLeadSkip <- 0
                    else
                        let mutable lS1, lC1, lS2, lC2 = 0, 0, 0, 0
                        let mutable rS1, rC1, rS2, rC2 = 0, 0, 0, 0

                        if
                            i + 1 < inCount
                            && inTokens[i].Kind = TokenKind.CommaToken
                            && isCloseDelimiter inTokens[i + 1].Kind
                            && outTokens[j].Kind = inTokens[i + 1].Kind
                        then
                            let commaTok = inTokens[i]
                            lS1 <- commaTok.TriviaStart + inLeadSkip
                            lC1 <- commaTok.LeadingCount - inLeadSkip
                            inLeadSkip <- 0
                            lS2 <- commaTok.TriviaStart + commaTok.LeadingCount
                            lC2 <- commaTok.TrailingCount
                            i <- i + 1
                        elif
                            j + 1 < outCount
                            && outTokens[j].Kind = TokenKind.CommaToken
                            && isCloseDelimiter outTokens[j + 1].Kind
                            && inTokens[i].Kind = outTokens[j + 1].Kind
                        then
                            let commaTok = outTokens[j]
                            rS1 <- commaTok.TriviaStart + outLeadSkip
                            rC1 <- commaTok.LeadingCount - outLeadSkip
                            outLeadSkip <- 0
                            rS2 <- commaTok.TriviaStart + commaTok.LeadingCount
                            rC2 <- commaTok.TrailingCount
                            j <- j + 1

                        let curIn = inTokens[i]
                        let curOut = outTokens[j]

                        let struct (gapOk, gapDesc) =
                            if
                                not (
                                    gapRangeHasComment
                                        lBuf
                                        (lBuf.TriviaSpan())
                                        inPendS
                                        inPendC
                                        lS1
                                        lC1
                                        lS2
                                        lC2
                                        (curIn.TriviaStart + inLeadSkip)
                                        (curIn.LeadingCount - inLeadSkip)
                                )
                                && not (
                                    gapRangeHasComment
                                        rBuf
                                        (rBuf.TriviaSpan())
                                        outPendS
                                        outPendC
                                        rS1
                                        rC1
                                        rS2
                                        rC2
                                        (curOut.TriviaStart + outLeadSkip)
                                        (curOut.LeadingCount - outLeadSkip)
                                )
                            then
                                struct (true, "")
                            else
                                checkGapComments
                                    isOuter
                                    allowDirectiveSpanning
                                    deferredRawSpans
                                    lSpan
                                    rSpan
                                    lBuf
                                    rBuf
                                    i
                                    (inPendS,
                                     inPendC,
                                     lS1,
                                     lC1,
                                     lS2,
                                     lC2,
                                     curIn.TriviaStart + inLeadSkip,
                                     curIn.LeadingCount - inLeadSkip)
                                    (outPendS,
                                     outPendC,
                                     rS1,
                                     rC1,
                                     rS2,
                                     rC2,
                                     curOut.TriviaStart + outLeadSkip,
                                     curOut.LeadingCount - outLeadSkip)

                        inLeadSkip <- 0
                        outLeadSkip <- 0

                        if not gapOk then
                            mismatchKey <- gapDesc
                            failedComment <- true
                        elif i = inCount - 1 && j = outCount - 1 then
                            i <- inCount
                            j <- outCount
                        elif
                            curIn.Kind = curOut.Kind
                            && (curIn.Kind = TokenKind.InterpolatedStringToken
                                || (curIn.Length = curOut.Length
                                    && sameTokenTextSpan lSpan &curIn rSpan &curOut))
                        then
                            if
                                curIn.Kind = TokenKind.InterpolatedStringToken
                                && not (
                                    this.CheckInterpPair(
                                        depth,
                                        lText,
                                        lSpan,
                                        rSpan,
                                        curIn,
                                        curOut,
                                        &cachedFmt
                                    )
                                )
                            then
                                failedComment <- true
                                failedHole <- true
                            else
                                inPendS <- curIn.TriviaStart + curIn.LeadingCount
                                inPendC <- curIn.TrailingCount
                                outPendS <- curOut.TriviaStart + curOut.LeadingCount
                                outPendC <- curOut.TrailingCount
                                i <- i + 1
                                j <- j + 1
                        elif isGreaterRun curIn.Kind && isGreaterRun curOut.Kind then
                            let mutable inGt = greaterWidth curIn.Kind
                            let mutable outGt = greaterWidth curOut.Kind
                            let mutable ci = i
                            let mutable cj = j
                            let mutable splitOk = true

                            while splitOk && inGt <> outGt do
                                if inGt < outGt then
                                    if
                                        ci + 1 >= inCount - 1
                                        || not (isGreaterRun inTokens[ci + 1].Kind)
                                    then
                                        splitOk <- false
                                    else
                                        let tPrev = inTokens[ci]
                                        let tNext = inTokens[ci + 1]
                                        let inT = lBuf.TriviaSpan()

                                        if
                                            sliceHasComment
                                                lBuf
                                                inT
                                                (tPrev.TriviaStart + tPrev.LeadingCount)
                                                tPrev.TrailingCount
                                            || sliceHasComment
                                                lBuf
                                                inT
                                                tNext.TriviaStart
                                                tNext.LeadingCount
                                        then
                                            failedComment <- true
                                            splitOk <- false
                                        else
                                            ci <- ci + 1
                                            inGt <- inGt + greaterWidth inTokens[ci].Kind
                                else if
                                    cj + 1 >= outCount - 1
                                    || not (isGreaterRun outTokens[cj + 1].Kind)
                                then
                                    splitOk <- false
                                else
                                    let tPrev = outTokens[cj]
                                    let tNext = outTokens[cj + 1]
                                    let outT = rBuf.TriviaSpan()

                                    if
                                        sliceHasComment
                                            rBuf
                                            outT
                                            (tPrev.TriviaStart + tPrev.LeadingCount)
                                            tPrev.TrailingCount
                                        || sliceHasComment
                                            rBuf
                                            outT
                                            tNext.TriviaStart
                                            tNext.LeadingCount
                                    then
                                        failedComment <- true
                                        splitOk <- false
                                    else
                                        cj <- cj + 1
                                        outGt <- outGt + greaterWidth outTokens[cj].Kind

                            if not splitOk then
                                if not failedComment then
                                    tokenStopped <- true
                            else
                                let endIn = inTokens[ci]
                                let endOut = outTokens[cj]
                                inPendS <- endIn.TriviaStart + endIn.LeadingCount
                                inPendC <- endIn.TrailingCount
                                outPendS <- endOut.TriviaStart + endOut.LeadingCount
                                outPendC <- endOut.TrailingCount
                                i <- ci + 1
                                j <- cj + 1
                        else
                            tokenStopped <- true

            if failedComment then
                struct (false, mismatchKey, failedHole)
            elif not tokenStopped && i >= inCount && j >= outCount then
                struct (true, "", false)
            else
                let frontI = i
                let frontJ = j
                let mutable bi = inCount - 1
                let mutable bj = outCount - 1
                let mutable backStopped = false

                while not failedComment && not backStopped && bi > frontI && bj > frontJ do
                    let mutable prevI = bi - 1
                    let mutable prevJ = bj - 1
                    let mutable lS1, lC1, lS2, lC2 = 0, 0, 0, 0
                    let mutable rS1, rC1, rS2, rC2 = 0, 0, 0, 0

                    if
                        isCloseDelimiter inTokens[bi].Kind && inTokens[bi].Kind = outTokens[bj].Kind
                    then
                        if
                            prevI > frontI
                            && inTokens[prevI].Kind = TokenKind.CommaToken
                            && outTokens[prevJ].Kind <> TokenKind.CommaToken
                        then
                            let commaTok = inTokens[prevI]
                            lS1 <- commaTok.TriviaStart
                            lC1 <- commaTok.LeadingCount
                            lS2 <- commaTok.TriviaStart + commaTok.LeadingCount
                            lC2 <- commaTok.TrailingCount
                            prevI <- prevI - 1
                        elif
                            prevJ > frontJ
                            && outTokens[prevJ].Kind = TokenKind.CommaToken
                            && inTokens[prevI].Kind <> TokenKind.CommaToken
                        then
                            let commaTok = outTokens[prevJ]
                            rS1 <- commaTok.TriviaStart
                            rC1 <- commaTok.LeadingCount
                            rS2 <- commaTok.TriviaStart + commaTok.LeadingCount
                            rC2 <- commaTok.TrailingCount
                            prevJ <- prevJ - 1

                    let pIn = inTokens[prevI]
                    let pOut = outTokens[prevJ]

                    let matchedPrev =
                        if
                            pIn.Kind = pOut.Kind
                            && (pIn.Kind = TokenKind.InterpolatedStringToken
                                || (pIn.Length = pOut.Length
                                    && sameTokenTextSpan lSpan &pIn rSpan &pOut))
                        then
                            if
                                pIn.Kind = TokenKind.InterpolatedStringToken
                                && not (
                                    this.CheckInterpPair(
                                        depth,
                                        lText,
                                        lSpan,
                                        rSpan,
                                        pIn,
                                        pOut,
                                        &cachedFmt
                                    )
                                )
                            then
                                failedComment <- true
                                failedHole <- true
                                false
                            else
                                true
                        elif isGreaterRun pIn.Kind && isGreaterRun pOut.Kind then
                            let mutable inGt = greaterWidth pIn.Kind
                            let mutable outGt = greaterWidth pOut.Kind
                            let mutable ci = prevI
                            let mutable cj = prevJ
                            let mutable okGt = true

                            while okGt && inGt <> outGt do
                                if inGt < outGt then
                                    if
                                        ci - 1 < frontI || not (isGreaterRun inTokens[ci - 1].Kind)
                                    then
                                        okGt <- false
                                    else
                                        let tPrev = inTokens[ci - 1]
                                        let tNext = inTokens[ci]
                                        let inT = lBuf.TriviaSpan()

                                        if
                                            sliceHasComment
                                                lBuf
                                                inT
                                                (tPrev.TriviaStart + tPrev.LeadingCount)
                                                tPrev.TrailingCount
                                            || sliceHasComment
                                                lBuf
                                                inT
                                                tNext.TriviaStart
                                                tNext.LeadingCount
                                        then
                                            failedComment <- true
                                            okGt <- false
                                        else
                                            ci <- ci - 1
                                            inGt <- inGt + greaterWidth inTokens[ci].Kind
                                else if
                                    cj - 1 < frontJ || not (isGreaterRun outTokens[cj - 1].Kind)
                                then
                                    okGt <- false
                                else
                                    let tPrev = outTokens[cj - 1]
                                    let tNext = outTokens[cj]
                                    let outT = rBuf.TriviaSpan()

                                    if
                                        sliceHasComment
                                            rBuf
                                            outT
                                            (tPrev.TriviaStart + tPrev.LeadingCount)
                                            tPrev.TrailingCount
                                        || sliceHasComment
                                            rBuf
                                            outT
                                            tNext.TriviaStart
                                            tNext.LeadingCount
                                    then
                                        failedComment <- true
                                        okGt <- false
                                    else
                                        cj <- cj - 1
                                        outGt <- outGt + greaterWidth outTokens[cj].Kind

                            if okGt then
                                prevI <- ci
                                prevJ <- cj
                                true
                            else
                                false
                        else
                            false

                    if failedComment then
                        ()
                    elif not matchedPrev then
                        backStopped <- true
                    else
                        let ltTrailS = pIn.TriviaStart + pIn.LeadingCount
                        let ltTrailC = pIn.TrailingCount
                        let rtTrailS = pOut.TriviaStart + pOut.LeadingCount
                        let rtTrailC = pOut.TrailingCount
                        let curBi = inTokens[bi]
                        let curBj = outTokens[bj]

                        let struct (gapOk, gapDesc) =
                            checkGapComments
                                isOuter
                                allowDirectiveSpanning
                                deferredRawSpans
                                lSpan
                                rSpan
                                lBuf
                                rBuf
                                bi
                                (ltTrailS,
                                 ltTrailC,
                                 lS1,
                                 lC1,
                                 lS2,
                                 lC2,
                                 curBi.TriviaStart,
                                 curBi.LeadingCount)
                                (rtTrailS,
                                 rtTrailC,
                                 rS1,
                                 rC1,
                                 rS2,
                                 rC2,
                                 curBj.TriviaStart,
                                 curBj.LeadingCount)

                        if not gapOk then
                            mismatchKey <- gapDesc
                            failedComment <- true
                        else
                            bi <- prevI
                            bj <- prevJ

                if failedComment then
                    struct (false, mismatchKey, failedHole)
                else
                    let mutable remOk = true
                    let mutable holeRemFail = false

                    let mutable inInterpCount = 0

                    for k = frontI to bi - 1 do
                        if inTokens[k].Kind = TokenKind.InterpolatedStringToken then
                            inInterpCount <- inInterpCount + 1

                    let mutable outInterpCount = 0

                    for k = frontJ to bj - 1 do
                        if outTokens[k].Kind = TokenKind.InterpolatedStringToken then
                            outInterpCount <- outInterpCount + 1

                    if inInterpCount > 0 || outInterpCount > 0 then
                        if inInterpCount = outInterpCount then
                            let mutable ui = frontI
                            let mutable uj = frontJ

                            while remOk && ui < bi && uj < bj do
                                while ui < bi
                                      && inTokens[ui].Kind <> TokenKind.InterpolatedStringToken do
                                    ui <- ui + 1

                                while uj < bj
                                      && outTokens[uj].Kind <> TokenKind.InterpolatedStringToken do
                                    uj <- uj + 1

                                if ui < bi && uj < bj then
                                    if
                                        not (
                                            this.CheckInterpPair(
                                                depth,
                                                lText,
                                                lSpan,
                                                rSpan,
                                                inTokens[ui],
                                                outTokens[uj],
                                                &cachedFmt
                                            )
                                        )
                                    then
                                        remOk <- false
                                        holeRemFail <- true

                                    ui <- ui + 1
                                    uj <- uj + 1
                        else
                            let mutable ui = frontI

                            while remOk && ui < bi do
                                if
                                    inTokens[ui].Kind = TokenKind.InterpolatedStringToken
                                    && this.InterpolationTokenHasHoleComments(
                                        depth,
                                        lText,
                                        inTokens[ui]
                                    )
                                then
                                    remOk <- false
                                    holeRemFail <- true

                                ui <- ui + 1

                            let mutable uj = frontJ

                            while remOk && uj < bj do
                                if outTokens[uj].Kind = TokenKind.InterpolatedStringToken then
                                    let rText = this.EnsureFmtStr(rSpan, &cachedFmt)

                                    if
                                        this.InterpolationTokenHasHoleComments(
                                            depth,
                                            rText,
                                            outTokens[uj]
                                        )
                                    then
                                        remOk <- false
                                        holeRemFail <- true

                                uj <- uj + 1

                    if not remOk then
                        struct (false, "", holeRemFail)
                    else
                        let inRemStart =
                            if frontI < bi then
                                inTokens[frontI].TriviaStart + inTokens[frontI].LeadingCount
                            else
                                0

                        let inRemEnd =
                            if frontI < bi then
                                min
                                    lBuf.LastCommentTrivia
                                    (inTokens[bi].TriviaStart + inTokens[bi].LeadingCount - 1)
                            else
                                -1

                        let outRemStart =
                            if frontJ < bj then
                                outTokens[frontJ].TriviaStart + outTokens[frontJ].LeadingCount
                            else
                                0

                        let outRemEnd =
                            if frontJ < bj then
                                min
                                    rBuf.LastCommentTrivia
                                    (outTokens[bj].TriviaStart + outTokens[bj].LeadingCount - 1)
                            else
                                -1

                        let hasRemIn = rangeHasComment lBuf inRemStart inRemEnd
                        let hasRemOut = rangeHasComment rBuf outRemStart outRemEnd

                        if not hasRemIn && not hasRemOut then
                            struct (true, "", false)
                        else
                            let rText = this.EnsureFmtStr(rSpan, &cachedFmt)

                            if
                                this.CheckRangeMultiset(
                                    allowDirectiveSpanning,
                                    deferredRawSpans,
                                    lText,
                                    lBuf,
                                    inRemStart,
                                    inRemEnd,
                                    rText,
                                    rBuf,
                                    outRemStart,
                                    outRemEnd
                                )
                            then
                                struct (true, "", false)
                            else
                                struct (false,
                                        firstCommentKey
                                            lSpan
                                            (lBuf.TriviaSpan())
                                            inRemStart
                                            (inRemEnd - inRemStart + 1),
                                        false)

        member private this.RewindAnchoredStart(srcSpan: ReadOnlySpan<char>, k: int) =
            let input = before.LexerBuffer
            let output = after.LexerBuffer

            if k <= 0 || k >= input.TokenCount || k >= output.TokenCount then
                0
            else
                let inTokens = input.TokenSpan()
                let mutable r = k

                while r > 0 && lexerModifierKindSpan srcSpan inTokens[r - 1] <> TokenKind.None do
                    r <- r - 1

                let mutable rewindUsing = true

                while rewindUsing && r > 0 do
                    let mutable p = r - 1

                    if inTokens[p].Kind = TokenKind.SemicolonToken then
                        if p = 0 then rewindUsing <- false else p <- p - 1

                    if rewindUsing then
                        while p > 0
                              && inTokens[p].Kind <> TokenKind.SemicolonToken
                              && inTokens[p].Kind <> TokenKind.OpenBraceToken
                              && inTokens[p].Kind <> TokenKind.CloseBraceToken do
                            p <- p - 1

                        let clauseStart =
                            if
                                inTokens[p].Kind = TokenKind.SemicolonToken
                                || inTokens[p].Kind = TokenKind.OpenBraceToken
                                || inTokens[p].Kind = TokenKind.CloseBraceToken
                            then
                                p + 1
                            else
                                0

                        if
                            clauseStart < r
                            && isUsingDirectiveHeadToken inTokens srcSpan clauseStart
                        then
                            r <- clauseStart
                        else
                            rewindUsing <- false

                r

        member internal this.CommentsPreservedDirectSpan
            (
                source: string,
                formatted: ReadOnlySpan<char>,
                cachedFormatted: byref<string>,
                loaded: bool,
                sourceTree: SyntaxTree
            ) =
            this.CommentsPreservedCore(
                source,
                formatted,
                &cachedFormatted,
                loaded,
                sourceTree,
                false
            )

        member private this.CommentsPreservedCore
            (
                source: string,
                formatted: ReadOnlySpan<char>,
                cachedFormatted: byref<string>,
                loaded: bool,
                sourceTree: SyntaxTree,
                allowDirectiveSpanningMultiLine: bool
            ) =
            if not loaded then
                beforeLexedFor <- null
                beforeLexedSymbols <- Array.empty

                if usableSourceTree sourceTree then
                    before <- sourceTree
                else
                    before <- ownedBefore
                    parseText source before

                beforeBuilt <- true

                afterLexedFor <- null
                afterLexedSymbols <- Array.empty
                afterLexedSpanId <- -1
                let bBuf = before.LexerBuffer
                let tokHint = bBuf.TokenCount + (bBuf.TokenCount >>> 4) + 32

                let trivHint =
                    max (bBuf.TriviaCount + (bBuf.TriviaCount >>> 4) + 64) (bBuf.TokenCount + 64)

                lexedTexts <- lexedTexts + 1
                Parser.lexOnlyHintedSpan tokHint trivHint formatted after

                if not (isNull cachedFormatted) then
                    afterLexedFor <- cachedFormatted
                else
                    afterLexedSpanId <- lexedTexts

            let input = before.LexerBuffer
            let output = after.LexerBuffer

            if
                not input.HasComments
                && not output.HasComments
                && not input.HasInterpolated
                && not output.HasInterpolated
            then
                struct (true, "")
            else
                let srcSpan = source.AsSpan()

                let startTok =
                    if
                        lastLexicalId = lexedTexts
                        && Object.ReferenceEquals(lastLexicalSource, source)
                        && Object.ReferenceEquals(lastLexicalBefore, before)
                        && lastLexicalPrefix > 0
                        && (if not (isNull cachedFormatted) then
                                Object.ReferenceEquals(lastLexicalFormatted, cachedFormatted)
                            else
                                isNull lastLexicalFormatted && afterLexedSpanId = lexedTexts)
                    then
                        this.RewindAnchoredStart(srcSpan, lastLexicalPrefix)
                    else
                        0

                let deferredRawSpans =
                    if allowDirectiveSpanningMultiLine && allowDisabledDeferral then
                        ResizeArray<struct (int * int * int * int)>()
                    else
                        null

                let struct (ok, mismatchKey, holeFailure) =
                    if
                        not input.HasComments
                        && not output.HasComments
                        && not input.IsVerifyOnly
                        && not output.IsVerifyOnly
                    then
                        let inTokens = input.TokenSpan()
                        let outTokens = output.TokenSpan()

                        if input.InterpolatedCount = output.InterpolatedCount then
                            let mutable sameAll = true
                            let mutable k = 0

                            while sameAll && k < input.InterpolatedCount do
                                let lTok = inTokens[input.Interpolated k]
                                let rTok = outTokens[output.Interpolated k]

                                if
                                    not (
                                        this.CheckInterpPair(
                                            0,
                                            source,
                                            srcSpan,
                                            formatted,
                                            lTok,
                                            rTok,
                                            &cachedFormatted
                                        )
                                    )
                                then
                                    sameAll <- false

                                k <- k + 1

                            if sameAll then
                                struct (true, "", false)
                            else
                                struct (false, "", true)
                        else
                            let mutable anyHoleComment = false
                            let mutable k = 0

                            while not anyHoleComment && k < input.InterpolatedCount do
                                if
                                    this.InterpolationTokenHasHoleComments(
                                        0,
                                        source,
                                        inTokens[input.Interpolated k]
                                    )
                                then
                                    anyHoleComment <- true

                                k <- k + 1

                            if not anyHoleComment then
                                let fmtStr = this.EnsureFmtStr(formatted, &cachedFormatted)
                                let mutable okOut = 0

                                while not anyHoleComment && okOut < output.InterpolatedCount do
                                    if
                                        this.InterpolationTokenHasHoleComments(
                                            0,
                                            fmtStr,
                                            outTokens[output.Interpolated okOut]
                                        )
                                    then
                                        anyHoleComment <- true

                                    okOut <- okOut + 1

                            if anyHoleComment then
                                struct (false, "", true)
                            else
                                struct (true, "", false)
                    else
                        this.CheckAnchoredSpan(
                            0,
                            true,
                            allowDirectiveSpanningMultiLine,
                            deferredRawSpans,
                            source,
                            srcSpan,
                            formatted,
                            input,
                            output,
                            startTok,
                            &cachedFormatted
                        )

                if ok then
                    if not (isNull deferredRawSpans) && deferredRawSpans.Count > 0 then
                        for di = 0 to deferredRawSpans.Count - 1 do
                            let struct (ls, le, rs, re) = deferredRawSpans[di]

                            addDeferredDisabledSpan (
                                struct (source,
                                        disabledDeferralPrefix,
                                        ls - disabledDeferralPrefix,
                                        le - disabledDeferralPrefix,
                                        rs - disabledDeferralPrefix,
                                        re - disabledDeferralPrefix)
                            )

                    struct (true, "")
                elif holeFailure then
                    struct (false, "interpolated string hole comment changed")
                else
                    let fmtStr = this.EnsureFmtStr(formatted, &cachedFormatted)

                    let struct (fullExpected, fullActual) =
                        commentKeyPairFull source input fmtStr output

                    let struct (fullLost, fullGained, fullLostKey, fullGainedKey) =
                        symmetricCommentDiff fullExpected fullActual

                    if fullLost > 0 || fullGained > 0 then
                        struct (false,
                                String.Format(
                                    "of the input's {0} comments the output's {1} are missing {2} and add {3}; it lost {4} and gained {5}",
                                    fullExpected.Length,
                                    fullActual.Length,
                                    fullLost,
                                    fullGained,
                                    (if fullLost = 0 then "nothing" else fullLostKey),
                                    (if fullGained = 0 then "nothing" else fullGainedKey)
                                ))
                    else
                        struct (false,
                                (if String.IsNullOrEmpty mismatchKey then
                                     "comment moved to a different token"
                                 else
                                     String.Format(
                                         "comment {0} moved to a different token",
                                         mismatchKey
                                     )))

        member this.FastEquivalent(source: string, formatted: string) =
            this.FastEquivalentCore(source, formatted, false)

        member internal this.FastEquivalentUnrewritten(source: string, formatted: string) =
            this.FastEquivalentCore(source, formatted, true)

        member private _.FastEquivalentCore(source: string, formatted: string, recovered: bool) =
            if
                Object.ReferenceEquals(source, fullyProvenSource)
                && Object.ReferenceEquals(formatted, fullyProvenFormatted)
            then
                true
            else
                let tolerant =
                    Object.ReferenceEquals(source, provenSource)
                    && Object.ReferenceEquals(formatted, provenFormatted)

                let agreed =
                    Object.ReferenceEquals(source, agreedSource)
                    && Object.ReferenceEquals(formatted, agreedFormatted)

                let streams =
                    if tolerant || agreed then
                        true
                    else
                        let struct (tokensAgree, _) = agree source formatted
                        tokensAgree

                let permissive = not streams

                let mutable same =
                    collectDirectives true source before beforeDirectives
                    && collectDirectives true formatted after afterDirectives

                let placements =
                    same
                    && (beforeDirectives.Count > 0 || afterDirectives.Count > 0)
                    && beforePlacement.Load(before, beforeDirectives)
                    && afterPlacement.Load(after, afterDirectives)

                let sameTokens (left: Node) (right: Node) =
                    let mutable index = 0
                    let mutable equal = left.TokenCount = right.TokenCount

                    while equal && index < left.TokenCount do
                        let a = before.Token(left.TokenStart + index)
                        let b = after.Token(right.TokenStart + index)

                        equal <-
                            a.Kind = b.Kind
                            && a.Length = b.Length
                            && sameTokenText source &a formatted &b

                        index <- index + 1

                    equal

                let pairUsings (left: Node) (right: Node) =
                    childSlots <- grownIndices childSlots (left.ChildCount + 1)
                    let mutable count = 0
                    let mutable shaped = true
                    let mutable member_ = false
                    let mutable index = 0
                    let mutable beforeExternSeg = 0
                    let mutable afterExternSeg = 0
                    let mutable hasOrdinaryInSeg = false
                    let mutable lastOrdinaryPlacement = struct (0, 0)

                    let mutable ordinaryPlacements: ValueOption<HashSet<struct (int * int)>> =
                        ValueNone

                    let first =
                        if left.Kind = NodeKind.CompilationUnit then
                            0
                        else
                            let mutable lead = 0

                            while lead < left.ChildCount
                                  && (let child = before.Child(left.ChildStart + lead)

                                      child >= 0
                                      && (before.Node child).Kind = NodeKind.AttributeList) do
                                lead <- lead + 1

                            lead + 3

                    while shaped && index < left.ChildCount do
                        childSlots[index] <- index
                        let a = before.Child(left.ChildStart + index)
                        let b = after.Child(right.ChildStart + index)

                        let leftUsing = a >= 0 && before.Node(a).Kind = NodeKind.UsingDirective
                        let rightUsing = b >= 0 && after.Node(b).Kind = NodeKind.UsingDirective

                        if leftUsing <> rightUsing then
                            shaped <- false
                        elif leftUsing && index >= first then
                            let bNode = after.Node b
                            let mutable globalOrderOk = true

                            let isGlobal =
                                bNode.TokenCount > 0
                                && (after.Token bNode.TokenStart).Kind = TokenKind.GlobalKeyword

                            let placement =
                                struct (afterPlacement.Frame b, afterPlacement.Segment b)

                            if isGlobal then
                                if hasOrdinaryInSeg then
                                    if placement = lastOrdinaryPlacement then
                                        globalOrderOk <- false
                                    else
                                        match ordinaryPlacements with
                                        | ValueSome seen when seen.Contains placement ->
                                            globalOrderOk <- false
                                        | _ -> ()
                            elif not hasOrdinaryInSeg then
                                hasOrdinaryInSeg <- true
                                lastOrdinaryPlacement <- placement
                            elif placement <> lastOrdinaryPlacement then
                                match ordinaryPlacements with
                                | ValueSome seen -> seen.Add placement |> ignore
                                | ValueNone ->
                                    let seen = HashSet<struct (int * int)>()
                                    seen.Add lastOrdinaryPlacement |> ignore
                                    seen.Add placement |> ignore
                                    ordinaryPlacements <- ValueSome seen

                                lastOrdinaryPlacement <- placement

                            shaped <-
                                globalOrderOk
                                && not member_
                                && importShaped before (before.Node a)
                                && importShaped after bNode

                            if shaped then
                                usingSlots <- grownIndices usingSlots (count + 1)
                                usingSegmentsBefore <- grownIndices usingSegmentsBefore (count + 1)
                                usingSegmentsAfter <- grownIndices usingSegmentsAfter (count + 1)
                                usingSlots[count] <- index
                                usingSegmentsBefore[count] <- beforeExternSeg
                                usingSegmentsAfter[count] <- afterExternSeg
                                count <- count + 1
                        elif index >= first then
                            let beforeIsExtern =
                                a >= 0 && before.Node(a).Kind = NodeKind.ExternAliasDirective

                            let afterIsExtern =
                                b >= 0 && after.Node(b).Kind = NodeKind.ExternAliasDirective

                            if beforeIsExtern then
                                beforeExternSeg <- beforeExternSeg + 1

                            if afterIsExtern then
                                afterExternSeg <- afterExternSeg + 1
                                hasOrdinaryInSeg <- false

                                match ordinaryPlacements with
                                | ValueSome seen -> seen.Clear()
                                | ValueNone -> ()

                            if (a >= 0 && not beforeIsExtern) || (b >= 0 && not afterIsExtern) then
                                member_ <- true

                        index <- index + 1

                    if not shaped || count < 2 then
                        false
                    else
                        usingTaken <- grownFlags usingTaken count
                        Array.fill usingTaken 0 count false
                        let mutable matched = true
                        let mutable slot = 0

                        while matched && slot < count do
                            let a = before.Child(left.ChildStart + usingSlots[slot])
                            let mutable found = -1
                            let mutable offset = 0

                            while found < 0 && offset < count do
                                let candidate = (slot + offset) % count

                                if not usingTaken[candidate] then
                                    let b = after.Child(right.ChildStart + usingSlots[candidate])

                                    if
                                        beforePlacement.Frame a = afterPlacement.Frame b
                                        && beforePlacement.Segment a = afterPlacement.Segment b
                                        && usingSegmentsBefore[slot] = usingSegmentsAfter[candidate]
                                        && sameTokens (before.Node a) (after.Node b)
                                    then
                                        found <- candidate

                                offset <- offset + 1

                            if found < 0 then
                                matched <- false
                            else
                                usingTaken[found] <- true
                                childSlots[usingSlots[slot]] <- usingSlots[found]
                                slot <- slot + 1

                        matched

                let mutable visited = 0
                skippedBefore.Clear()
                skippedAfter.Clear()
                pendingCount <- 0

                if same then
                    if
                        not tolerant
                        && not permissive
                        && before.IsComplete
                        && after.IsComplete
                        && before.RootIndex = after.RootIndex
                        && MemoryMarshal
                            .AsBytes(before.NodeSpan())
                            .SequenceEqual(MemoryMarshal.AsBytes(after.NodeSpan()))
                        && before.ChildSpan().SequenceEqual(after.ChildSpan())
                        && (not placements || beforePlacement.SamePlacements afterPlacement)
                    then
                        pendingCount <- 0
                    else
                        pendingLeft[0] <- before.RootIndex
                        pendingRight[0] <- after.RootIndex
                        pendingCount <- 1

                let canPairUsings =
                    permissive
                    || (placements && not (beforePlacement.SamePlacements afterPlacement))

                while same && pendingCount > 0 do
                    pendingCount <- pendingCount - 1
                    let leftIndex = pendingLeft[pendingCount]
                    let rightIndex = pendingRight[pendingCount]
                    let left = before.Node leftIndex
                    let right = after.Node rightIndex
                    same <- left.Kind = right.Kind && left.ChildCount = right.ChildCount
                    let mutable leftComma = -1
                    let mutable rightComma = -1

                    if not same && tolerant && left.Kind = right.Kind then
                        if left.ChildCount = right.ChildCount + 1 then
                            leftComma <- commaChildSlot before left droppedCommas
                            same <- leftComma >= 0
                        elif right.ChildCount = left.ChildCount + 1 then
                            rightComma <- commaChildSlot after right addedCommas
                            same <- rightComma >= 0
                    elif not same && permissive && left.Kind = right.Kind then
                        if left.ChildCount = right.ChildCount + 1 then
                            leftComma <- trailingCommaSlot before left
                            same <- leftComma >= 0

                            if same then
                                skippedBefore.Add(~~~before.Child(left.ChildStart + leftComma))
                                |> ignore
                        elif right.ChildCount = left.ChildCount + 1 then
                            rightComma <- trailingCommaSlot after right
                            same <- rightComma >= 0

                            if same then
                                skippedAfter.Add(~~~after.Child(right.ChildStart + rightComma))
                                |> ignore

                    let shared =
                        if leftComma >= 0 then
                            left.ChildCount - 1
                        else
                            left.ChildCount

                    let permuted =
                        same
                        && canPairUsings
                        && placements
                        && holdsUsings left.Kind
                        && pairUsings left right

                    let leftGate = if leftComma >= 0 then leftComma else Int32.MaxValue
                    let rightGate = if rightComma >= 0 then rightComma else Int32.MaxValue
                    let mutable index = 0

                    while same && index < shared do
                        let leftSlot = if index >= leftGate then index + 1 else index

                        let rightSlot =
                            if permuted then childSlots[leftSlot]
                            elif index >= rightGate then index + 1
                            else index

                        let a = before.Child(left.ChildStart + leftSlot)
                        let b = after.Child(right.ChildStart + rightSlot)

                        if a >= 0 && b >= 0 then
                            if placements && (before.Node a).Kind = NodeKind.UsingDirective then
                                same <-
                                    beforePlacement.Frame a = afterPlacement.Frame b
                                    && beforePlacement.Segment a = afterPlacement.Segment b

                            if pendingCount = pendingLeft.Length then
                                let grownLeft = Array.zeroCreate<int>(pendingCount * 2)
                                let grownRight = Array.zeroCreate<int>(pendingCount * 2)
                                Array.blit pendingLeft 0 grownLeft 0 pendingCount
                                Array.blit pendingRight 0 grownRight 0 pendingCount
                                pendingLeft <- grownLeft
                                pendingRight <- grownRight

                            pendingLeft[pendingCount] <- a
                            pendingRight[pendingCount] <- b
                            pendingCount <- pendingCount + 1
                        elif a < 0 && b < 0 then
                            let leftToken = before.Token(~~~a)
                            let rightToken = after.Token(~~~b)

                            if permissive then
                                visited <- visited + 1

                            same <-
                                leftToken.Kind <> TokenKind.BadToken
                                && leftToken.Kind = rightToken.Kind
                                && ((a = b && not permissive)
                                    || (leftToken.Length = rightToken.Length
                                        && sameTokenText source &leftToken formatted &rightToken))
                        else
                            same <- false

                        index <- index + 1

                if same && permissive then
                    same <-
                        visited + skippedBefore.Count = before.TokenCount
                        && visited + skippedAfter.Count = after.TokenCount

                let mutable left = 0
                let mutable right = 0
                let mutable leftToken = 0
                let mutable rightToken = 0
                let mutable leftCount = 0
                let mutable rightCount = 0

                let inline tokenEnd (tree: SyntaxTree) index =
                    let token = tree.Token index
                    token.End

                let anySkippedBefore = skippedBefore.Count > 0
                let anySkippedAfter = skippedAfter.Count > 0

                while same && (left < beforeDirectives.Count || right < afterDirectives.Count) do
                    if left = beforeDirectives.Count || right = afterDirectives.Count then
                        same <- left = beforeDirectives.Count && right = afterDirectives.Count
                    else
                        let a = beforeDirectives[left]
                        let b = afterDirectives[right]

                        while leftToken < before.TokenCount && tokenEnd before leftToken <= a.Start do
                            leftCount <-
                                leftCount
                                + (if
                                       (tolerant && droppedCommas.Contains leftToken)
                                       || (placements && beforePlacement.Owns leftToken)
                                       || (anySkippedBefore && skippedBefore.Contains leftToken)
                                   then
                                       0
                                   else
                                       1)
                                + (if tolerant && commaClosings.Contains leftToken then
                                       1
                                   else
                                       0)

                            leftToken <- leftToken + 1

                        while rightToken < after.TokenCount && tokenEnd after rightToken <= b.Start do
                            rightCount <-
                                rightCount
                                + (if
                                       (placements && afterPlacement.Owns rightToken)
                                       || (anySkippedAfter && skippedAfter.Contains rightToken)
                                   then
                                       0
                                   else
                                       1)

                            rightToken <- rightToken + 1

                        same <-
                            a.Kind = b.Kind
                            && leftCount = rightCount
                            && ((a.Kind <> TriviaKind.DefineDirectiveTrivia
                                 && a.Kind <> TriviaKind.UndefDirectiveTrivia)
                                || (leftCount = 0 && (not placements || leftToken = 0)))
                            && (directiveComparand source a)
                                .SequenceEqual(directiveComparand formatted b)

                        left <- left + 1
                        right <- right + 1

                let identicalRecovery () =
                    recovered
                    && not tolerant
                    && not permissive
                    && before.RecoveredTokens = after.RecoveredTokens
                    && before.TokenCount = after.TokenCount
                    && before.RootIndex = after.RootIndex
                    && MemoryMarshal
                        .AsBytes(before.NodeSpan())
                        .SequenceEqual(MemoryMarshal.AsBytes(after.NodeSpan()))
                    && before.ChildSpan().SequenceEqual(after.ChildSpan())
                    && (let mutable index = 0
                        let mutable equal = true

                        while equal && index < before.TokenCount do
                            let a = before.Token index
                            let b = after.Token index

                            equal <-
                                a.Kind <> TokenKind.BadToken
                                && a.Kind = b.Kind
                                && a.Length = b.Length
                                && sameTokenText source &a formatted &b

                            index <- index + 1

                        equal)

                same
                && (not permissive || (before.IsComplete && after.IsComplete))
                && ((before.RecoveredTokens = 0 && after.RecoveredTokens = 0)
                    || identicalRecovery ())
                && disabledRunsAgree source formatted

        member this.Check
            (options: PrinterOptions, filePath: string, source: string, formatted: string)
            =
            this.CheckAndNormalize(options, filePath, source, formatted)
            |> Result.map ignore

        member internal this.ReleasePooledBuffers() =
            this.EndDisabledDeferral()
            this.ClearPinnedConditionalPair()
            inUsingPlacementCursor.Reset()
            outUsingPlacementCursor.Reset()
            inRunIgnoreCursor.Reset()
            outRunIgnoreCursor.Reset()
            afterLexedFor <- null
            beforeLexedFor <- null
            afterLexedSpanId <- -1
            sepDeclinedSpanId <- -1
            fullyProvenSource <- null
            fullyProvenFormatted <- null
            agreedSource <- null
            agreedFormatted <- null
            provenSource <- null
            provenFormatted <- null
            provenRewrite <- null
            sepDeclinedSource <- null
            sepDeclinedFormatted <- null
            lastLexicalSource <- null
            lastLexicalFormatted <- null

            if ownsBefore then
                ownedBefore.ReleasePooledBuffers()

            if ownsAfter then
                after.ReleasePooledBuffers()

            match probe with
            | ValueSome p ->
                p.ReleasePooledBuffers()
                probe <- ValueNone
            | ValueNone -> ()

            savedDefaultBeforeBuf.ReleasePooledBuffers()
            savedDefaultAfterBuf.ReleasePooledBuffers()
            interpLeft.ReleasePooledBuffers()
            interpRight.ReleasePooledBuffers()

            for buffers in
                [|
                    interpLeftDepthBuffers
                    interpRightDepthBuffers
                    interpScanDepthBuffers
                    interpHoleBuffers
                |] do
                for k = 0 to buffers.Count - 1 do
                    buffers[k].ReleasePooledBuffers()

            for k = 0 to interpHoleTreesLeft.Count - 1 do
                interpHoleTreesLeft[k].ReleasePooledBuffers()

            for k = 0 to interpHoleTreesRight.Count - 1 do
                interpHoleTreesRight[k].ReleasePooledBuffers()
