namespace Csff.Conformance

open System
open System.Security.Cryptography
open System.Text
open Csff.Parser
open Csff.Printer

module FrozenOutput =
    let hash (bytes: byte array) =
        let digest = SHA256.HashData bytes
        Convert.ToHexString(digest.AsSpan(0, 8))

    let checkBytes path configuration expected actual =
        let actualHash = hash actual

        if actualHash = expected then
            Ok()
        else
            Error
                $"{path} / {configuration}: frozen output differs (manifest={expected}, actual={actualHash})."

    type Formatter(options: PrinterOptions) =
        let tree = SyntaxTree()
        let document = new DocumentBuffer()
        let printer = new Printer()

        member _.Format(source: string) =
            Parser.parse source tree
            document.Reset()
            SyntaxPrinter.build source tree document options
            printer.Print(source, document, options)
            printer.OutputBytes.ToArray()

        interface IDisposable with
            member _.Dispose() =
                (document :> IDisposable).Dispose()
                (printer :> IDisposable).Dispose()
