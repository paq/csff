namespace Csff.Benchmarks

open System
open Csff.Conformance
open Csff.Lexer
open Csff.Parser
open Csff.Printer

type Stage =
    | Lex
    | Parse
    | Build
    | Print
    | Verify
    | Format

[<Sealed>]
type Pipeline(source: string) =
    let options = PrinterOptions.Default
    let tokens = TokenBuffer()
    let tree = SyntaxTree()
    let alternate = SyntaxTree()
    let document = new DocumentBuffer()
    let printer = new Printer()
    let builder = new SyntaxDocumentBuilder(printer, alternate)
    let checker = SyntaxPreservation.Checker(alternate, tree)
    let mutable formatted: string = null
    let mutable witness = Unchecked.defaultof<TransformationWitness>

    let outcome (verification: SyntaxPreservation.Verification) =
        match verification with
        | SyntaxPreservation.Verification.Proven -> 0
        | SyntaxPreservation.Verification.Violation message ->
            invalidOp ("The fixture's formatting violates its syntax: " + message)
        | SyntaxPreservation.Verification.Unprovable reason ->
            invalidOp ("The fixture's formatting cannot be proven: " + reason)

    member _.Source = source

    member _.Lex() =
        Lexer.lex source tokens
        tokens.TokenCount

    member _.Parse() =
        Parser.parse source tree
        tree.NodeCount

    member _.Build() =
        document.Reset()
        builder.Build(source, tree, document, options)
        document.Count

    member _.Print() =
        printer.Print(source, document, options)
        printer.OutputUtf16Length

    member _.Verify() =
        checker.Decide(options, "Fixture.cs", source, formatted, witness = witness)
        |> outcome

    member _.Format() =
        Parser.parse source tree
        document.Reset()
        builder.BuildAndPrint(source, tree, document, options)
        let printed = printer.OutputText

        if String.Equals(source, printed, StringComparison.Ordinal) then
            0
        else
            checker.Decide(options, "Fixture.cs", source, printed, tree, builder.Transformations)
            |> outcome

    member this.Run(stage: Stage) =
        match stage with
        | Lex -> this.Lex()
        | Parse -> this.Parse()
        | Build -> this.Build()
        | Print -> this.Print()
        | Verify -> this.Verify()
        | Format -> this.Format()

    member this.Prepare(stage: Stage) =
        Parser.parse source tree

        if not tree.IsComplete then
            invalidOp "The fixture does not parse completely."

        document.Reset()
        builder.Build(source, tree, document, options)
        printer.Print(source, document, options)
        formatted <- printer.OutputText
        witness <- builder.Transformations

        if String.Equals(source, formatted, StringComparison.Ordinal) then
            invalidOp "The fixture is already formatted, so nothing would verify it."

        this.Verify() |> ignore

        Parser.parse source tree
        document.Reset()
        builder.Build(source, tree, document, options)
        printer.Print(source, document, options)

        let first = this.Run stage
        let second = this.Run stage

        if first <> second then
            invalidOp $"{stage} returned {first} and then {second} on the same input."

    interface IDisposable with
        member _.Dispose() =
            (builder :> IDisposable).Dispose()
            (printer :> IDisposable).Dispose()
            (document :> IDisposable).Dispose()
            tokens.ReleasePooledBuffers()
            tree.ReleasePooledBuffers()
            alternate.ReleasePooledBuffers()
