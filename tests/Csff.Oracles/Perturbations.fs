namespace Csff.Conformance

open System
open Csff.Lexer
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Text

type PerturbationKind =
    | Reindent
    | BlankLines
    | Comment
    | LineEnding
    | TrailingWhitespace

type Perturbation =
    {
        Kind: PerturbationKind
        Position: int
        Amount: int
    }

module Perturbations =
    let kinds = [ Reindent; BlankLines; Comment; LineEnding; TrailingWhitespace ]

    let private mergeSpans (spans: seq<TextSpan>) =
        let merged = ResizeArray<TextSpan>()

        for span in
            spans
            |> Seq.filter (fun span -> span.Length > 0)
            |> Seq.sortBy (fun span -> span.Start) do
            if merged.Count > 0 && span.Start <= merged[merged.Count - 1].End then
                let previous = merged[merged.Count - 1]

                merged[merged.Count - 1] <-
                    TextSpan.FromBounds(previous.Start, max previous.End span.End)
            else
                merged.Add span

        merged.ToArray()

    let private overlaps (areas: TextSpan[]) start length =
        let mutable low = 0
        let mutable high = areas.Length

        while low < high do
            let middle = (low + high) / 2

            if areas[middle].End <= start then
                low <- middle + 1
            else
                high <- middle

        low < areas.Length && areas[low].Start < start + length

    let private protectedSpans (root: SyntaxNode) =
        let spans = ResizeArray<TextSpan>()
        let ignoreSpans = ResizeArray<TextSpan>()

        for node in root.DescendantNodes() do
            if node :? InterpolatedStringExpressionSyntax then
                spans.Add node.Span

        for token in root.DescendantTokens() do
            spans.Add token.Span

        let marker (node: SyntaxNode) prefix =
            node.GetLeadingTrivia()
            |> Seq.exists (fun trivia ->
                trivia.IsKind(SyntaxKind.SingleLineCommentTrivia)
                && (let text = trivia.ToString().TrimEnd()
                    text = prefix || text.StartsWith(prefix + " -", StringComparison.Ordinal)))

        for parent in root.DescendantNodesAndSelf() do
            let mutable ignoredStart = None

            for child in parent.ChildNodes() do
                if marker child "// csff-ignore-end" then
                    match ignoredStart with
                    | Some start ->
                        ignoreSpans.Add(TextSpan.FromBounds(start, child.FullSpan.Start))
                    | None -> ()

                    ignoredStart <- None
                elif marker child "// csff-ignore-start" && ignoredStart.IsNone then
                    ignoredStart <- Some child.FullSpan.Start

                if marker child "// csff-ignore" then
                    ignoreSpans.Add child.FullSpan

            match ignoredStart with
            | Some start -> ignoreSpans.Add(TextSpan.FromBounds(start, parent.FullSpan.End))
            | None -> ()

        spans.AddRange ignoreSpans
        struct (mergeSpans spans, mergeSpans ignoreSpans)

    let private candidates kind (source: string) =
        let buffer = TokenBuffer()
        Lexer.lex source buffer

        let struct (protectedAreas, ignoredAreas) =
            protectedSpans (GeneratedOutput.parse source)

        let safe (trivia: Trivia) =
            not (overlaps protectedAreas trivia.Start trivia.Length)

        let lineStart start =
            start = 0 || source[start - 1] = '\n' || source[start - 1] = '\r'

        [|
            for i in 0 .. buffer.TriviaCount - 1 do
                let trivia = buffer.Trivia i

                if safe trivia then
                    let finish = trivia.Start + trivia.Length

                    match kind, trivia.Kind with
                    | Reindent, TriviaKind.WhitespaceTrivia when
                        lineStart trivia.Start && (finish = source.Length || source[finish] <> '#')
                        ->
                        yield trivia
                    | Reindent, TriviaKind.EndOfLineTrivia when
                        finish < source.Length
                        && source[finish] <> '#'
                        && source[finish] <> ' '
                        && source[finish] <> '\t'
                        && not (overlaps ignoredAreas finish 1)
                        ->
                        yield trivia
                    | BlankLines, TriviaKind.EndOfLineTrivia
                    | LineEnding, TriviaKind.EndOfLineTrivia
                    | TrailingWhitespace, TriviaKind.EndOfLineTrivia -> yield trivia
                    | Comment, TriviaKind.WhitespaceTrivia when
                        not (lineStart trivia.Start)
                        && finish < source.Length
                        && source[finish] <> '#'
                        ->
                        yield trivia
                    | _ -> ()
        |]

    let applyOne source edit =
        let positions = candidates edit.Kind source

        if positions.Length = 0 then
            source
        else
            let trivia = positions[int (uint32 edit.Position % uint32 positions.Length)]
            let amount = int (uint32 edit.Amount % 6u)
            let original = source.Substring(trivia.Start, trivia.Length)
            let mutable editStart = trivia.Start

            let replacement =
                match edit.Kind with
                | Reindent ->
                    let indentation =
                        if amount = 0 then
                            ""
                        else
                            String(' ', amount * 3) + (if amount % 2 = 0 then "\t" else "")

                    if trivia.Kind = TriviaKind.EndOfLineTrivia then
                        original + indentation
                    else
                        indentation
                | BlankLines ->
                    let mutable start = trivia.Start

                    while start > 0 && (source[start - 1] = ' ' || source[start - 1] = '\t') do
                        start <- start - 1

                    if
                        amount = 0
                        && (start = 0 || source[start - 1] = '\n' || source[start - 1] = '\r')
                    then
                        editStart <- start
                        ""
                    else
                        original + String.replicate (1 + amount % 3) original
                | Comment ->
                    let comments =
                        [|
                            "/*p*/"
                            "/* first\nsecond */"
                            "/* 日本語 */"
                            "/* */"
                            "/*a*/ /*b*/"
                            "// p\n"
                        |]

                    original + comments[amount] + " "
                | LineEnding -> if original = "\r\n" then "\n" else "\r\n"
                | TrailingWhitespace -> String.replicate (amount + 1) " \t" + original

            source
                .Remove(editStart, trivia.Start + trivia.Length - editStart)
                .Insert(editStart, replacement)

    let apply source edits = List.fold applyOne source edits

    let requireEquivalent before after =
        GeneratedOutput.requireValid after
        let original = GeneratedOutput.parse before
        let perturbed = GeneratedOutput.parse after

        let signature (root: SyntaxNode) =
            root.DescendantNodesAndTokens()
            |> Seq.map (fun item ->
                if item.IsToken then
                    item.RawKind, item.AsToken().Text
                else
                    item.RawKind, "")
            |> Seq.toArray

        if signature original <> signature perturbed then
            invalidOp
                $"Perturbation changed C# structure or token text:\nBEFORE:\n{before}\nAFTER:\n{after}"
