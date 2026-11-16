namespace Csff.Conformance

open System.Text
open Csff.Lexer

module RoundTrip =
    let checkBuffer
        (filePath: string)
        (source: string)
        (buffer: TokenBuffer)
        : Result<unit, string> =
        let reconstructed = StringBuilder(source.Length)
        let mutable failure = None

        let append label start length =
            if failure.IsNone then
                if Diagnostics.validSpan source start length then
                    reconstructed.Append(source, start, length) |> ignore
                else
                    failure <-
                        Some
                            $"{filePath}: offset {reconstructed.Length}: round-trip invalid {label} span (start={start}, length={length})."

        let appendTrivia start count =
            if failure.IsNone then
                if
                    start < 0
                    || count < 0
                    || start > buffer.TriviaCount
                    || count > buffer.TriviaCount - start
                then
                    failure <-
                        Some
                            $"{filePath}: offset {reconstructed.Length}: round-trip invalid trivia range (start={start}, count={count}, available={buffer.TriviaCount})."
                else
                    for index in start .. start + count - 1 do
                        let trivia = buffer.Trivia index
                        append "trivia" trivia.Start trivia.Length

        for index in 0 .. buffer.TokenCount - 1 do
            let token = buffer.Token index
            appendTrivia token.TriviaStart token.LeadingCount
            append "token" token.Start token.Length
            appendTrivia (token.TriviaStart + token.LeadingCount) token.TrailingCount

        match failure with
        | Some message -> Error message
        | None ->
            let actual = reconstructed.ToString()
            let mutable offset = 0

            while offset < source.Length
                  && offset < actual.Length
                  && source[offset] = actual[offset] do
                offset <- offset + 1

            if offset = source.Length && offset = actual.Length then
                Ok()
            else
                Error
                    $"{filePath}: offset {offset}: round-trip mismatch (source length={source.Length}, reconstructed length={actual.Length}).\n  source: {Diagnostics.context source offset}\n  reconstructed: {Diagnostics.context actual offset}"

    let check (filePath: string) (source: string) (buffer: TokenBuffer) : Result<unit, string> =
        Lexer.lex source buffer
        checkBuffer filePath source buffer
