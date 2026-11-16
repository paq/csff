namespace Csff.Conformance

open System
open Csff.Parser
open Csff.Printer
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Microsoft.CodeAnalysis.Text

module GeneratedOutput =
    let parse (source: string) =
        CSharpSyntaxTree.ParseText(source, RoslynOptions.value).GetRoot()

    let requireValid source =
        let errors =
            (parse source).GetDiagnostics()
            |> Seq.filter (fun diagnostic -> diagnostic.Severity = DiagnosticSeverity.Error)
            |> Seq.toArray

        if errors.Length > 0 then
            let reported =
                errors
                |> Array.map (fun diagnostic -> diagnostic.ToString())
                |> String.concat "; "

            invalidOp $"Generator emitted invalid C#: {reported}\n{source}"

    let format options source =
        let tree = Csff.Parser.SyntaxTree()
        use document = new DocumentBuffer()
        use printer = new Printer()
        Parser.parse source tree
        SyntaxPrinter.build source tree document options
        printer.Print(source, document, options)
        printer.OutputText

    let checkSyntax source =
        requireValid source
        let tree = Csff.Parser.SyntaxTree()
        NodeOracle.check "generated.cs" source tree

    let removeSiblingSpans (source: string) (spans: TextSpan array) =
        let ordered = spans |> Array.sortBy (fun span -> span.Start)
        let mutable cursor = 0
        let mutable length = source.Length

        for span in ordered do
            if span.Start < cursor || span.End > source.Length then
                invalidArg
                    (nameof spans)
                    "Sibling spans must not overlap or extend beyond the source."

            cursor <- span.End
            length <- length - span.Length

        String.Create(
            length,
            struct (source, ordered),
            fun destination struct (source, spans) ->
                let mutable cursor = 0
                let mutable written = 0

                for span in spans do
                    let retained = span.Start - cursor
                    source.AsSpan(cursor, retained).CopyTo(destination.Slice(written))
                    written <- written + retained
                    cursor <- span.End

                source.AsSpan(cursor).CopyTo(destination.Slice(written))
        )

    let shrinkSource source =
        let root = parse source

        let removable (node: SyntaxNode) =
            let parent =
                if isNull node.Parent then
                    ""
                else
                    node.Parent.GetType().Name

            let kind = node.GetType().Name

            parent = "CompilationUnitSyntax"
            || parent = "BlockSyntax"
            || parent = "ClassDeclarationSyntax"
            || parent = "StructDeclarationSyntax"
            || parent = "NamespaceDeclarationSyntax"
            || kind = "UsingDirectiveSyntax"

        let nodes = root.DescendantNodes() |> Seq.filter removable |> Seq.toArray

        seq {
            for node in root.DescendantNodes() do
                match node with
                | :? BlockSyntax as block ->
                    let start = block.OpenBraceToken.Span.End
                    let finish = block.CloseBraceToken.Span.Start

                    if finish >= start then
                        yield source.Substring(start, finish - start)
                | :? AttributeListSyntax ->
                    yield source.Remove(node.FullSpan.Start, node.FullSpan.Length)
                | :? ParameterListSyntax as parameters when parameters.Parameters.Count > 0 ->
                    let start = parameters.OpenParenToken.Span.End
                    let finish = parameters.CloseParenToken.Span.Start
                    yield source.Remove(start, finish - start)
                | _ -> ()

            for node in
                root.DescendantNodes() |> Seq.sortByDescending (fun node -> node.Span.Length) do
                if node :? ExpressionSyntax && node.Span.Length > 1 then
                    yield
                        source
                            .Remove(node.Span.Start, node.Span.Length)
                            .Insert(node.Span.Start, "x")

            for trivia in root.DescendantTrivia() do
                if
                    trivia.IsKind(SyntaxKind.WhitespaceTrivia)
                    || trivia.IsKind(SyntaxKind.EndOfLineTrivia)
                then
                    yield source.Remove(trivia.Span.Start, trivia.Span.Length)

            for token in root.DescendantTokens() do
                if token.IsKind(SyntaxKind.IdentifierToken) && token.Text.Length > 1 then
                    yield
                        source
                            .Remove(token.Span.Start, token.Span.Length)
                            .Insert(token.Span.Start, "x")

            for parent in nodes |> Array.groupBy (fun n -> n.Parent) |> Array.map snd do
                for count in [ parent.Length / 2; 1 ] |> List.distinct do
                    if count > 0 then
                        for start in 0..count .. parent.Length - count do
                            let spans =
                                parent[start .. start + count - 1]
                                |> Array.map (fun n -> n.FullSpan)

                            yield removeSiblingSpans source spans
        }
        |> Seq.filter (fun candidate ->
            candidate.Length < source.Length
            && not (
                (parse candidate).GetDiagnostics()
                |> Seq.exists (fun d -> d.Severity = DiagnosticSeverity.Error)
            ))
        |> Seq.distinct
