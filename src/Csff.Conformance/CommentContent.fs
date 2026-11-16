namespace Csff.Conformance

open System
open System.Globalization
open Csff.Lexer

module internal CommentContent =

    let inline private lineBreak ch =
        if ch <= '\r' then
            ch = '\n' || ch = '\r'
        else
            ch >= '\u0085' && (ch = '\u0085' || ch = '\u2028' || ch = '\u2029')

    let inline internal indent ch =
        ch = ' '
        || ch = '\t'
        || ch = '\v'
        || ch = '\f'
        || (ch > '\u007f' && Char.GetUnicodeCategory ch = UnicodeCategory.SpaceSeparator)

    let lineSpan (text: ReadOnlySpan<char>) (finish: int) (from: int) =
        let mutable start = from

        while start < finish && indent text[start] do
            start <- start + 1

        let mutable stop = start

        while stop < finish && not (lineBreak text[stop]) do
            stop <- stop + 1

        let terminator = stop
        let mutable content = stop

        while content > start && indent text[content - 1] do
            content <- content - 1

        let next =
            if terminator >= finish then
                finish
            elif
                text[terminator] = '\r'
                && terminator + 1 < finish
                && text[terminator + 1] = '\n'
            then
                terminator + 2
            else
                terminator + 1

        struct (start, content - start, next)

    let line (text: string) (finish: int) (from: int) = lineSpan (text.AsSpan()) finish from

    let equivalentSpan
        (left: ReadOnlySpan<char>)
        (leftItem: Trivia)
        (right: ReadOnlySpan<char>)
        (rightItem: Trivia)
        =
        if
            leftItem.Length = rightItem.Length
            && left
                .Slice(leftItem.Start, leftItem.Length)
                .SequenceEqual(right.Slice(rightItem.Start, rightItem.Length))
        then
            true
        else

            let leftEnd = leftItem.Start + leftItem.Length
            let rightEnd = rightItem.Start + rightItem.Length
            let mutable a = leftItem.Start
            let mutable b = rightItem.Start
            let mutable same = true
            let mutable more = true

            while same && more do
                let struct (aStart, aLength, aNext) = lineSpan left leftEnd a
                let struct (bStart, bLength, bNext) = lineSpan right rightEnd b

                same <-
                    aLength = bLength
                    && left.Slice(aStart, aLength).SequenceEqual(right.Slice(bStart, bLength))
                    && (aNext < leftEnd) = (bNext < rightEnd)

                more <- same && aNext < leftEnd
                a <- aNext
                b <- bNext

            same

    let equivalent (left: string) (leftItem: Trivia) (right: string) (rightItem: Trivia) =
        equivalentSpan (left.AsSpan()) leftItem (right.AsSpan()) rightItem
