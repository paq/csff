module Csff.Tests.FrozenOutputTests

open System
open System.IO
open System.Text
open Csff.Cli
open Csff.Conformance
open Csff.Printer
open Expecto

let private expectOk result =
    match result with
    | Ok() -> ()
    | Error message -> failtest message

let private fixturePath () =
    Path.Combine(Checkout.root (), "tests", "generated-output-fixtures.yaml")

let private fixtures () =
    let path = fixturePath ()

    let documents = Yaml.parse path (File.ReadAllText path)

    let fail detail =
        failtestf "%s is not a sequence of fixture mappings: %s" path detail

    let field (entries: (YamlNode * YamlNode) array) name =
        let found =
            entries
            |> Array.tryPick (fun (key, value) ->
                match key with
                | YamlNode.Scalar(_, k, _) when k = name -> Some value
                | _ -> None)

        match found with
        | Some(YamlNode.Scalar(_, value, _)) -> value
        | Some _ -> fail ("the field " + name + " is not a scalar")
        | None -> fail ("a fixture has no " + name + " field")

    [
        for document in documents do
            match document with
            | YamlNode.Sequence(_, items) ->
                for item in items do
                    match item with
                    | YamlNode.Mapping(_, entries) ->
                        let options =
                            { PrinterOptions.Default with
                                Width = int (field entries "width")
                                EndOfLine =
                                    if field entries "crlf" = "true" then
                                        EndOfLine.CrLf
                                    else
                                        EndOfLine.Lf
                            }

                        yield
                            field entries "name",
                            field entries "source",
                            field entries "expected",
                            options
                    | _ -> fail "a sequence item is not a mapping"
            | _ -> fail "the document root is not a sequence"
    ]

let private frozen =
    testList
        "frozen output"
        [
            test "frozen output reports the file and configuration for changed bytes" {
                let expected = Encoding.UTF8.GetBytes "class C { }\n"
                let digest = FrozenOutput.hash expected

                FrozenOutput.checkBytes "src/C.cs" "width 40, spaces" digest expected
                |> expectOk

                for actual in [ "class C {}\n"; "class C { }\r\n"; "class C { }" ] do
                    let message =
                        FrozenOutput.checkBytes
                            "src/C.cs"
                            "width 40, spaces"
                            digest
                            (Encoding.UTF8.GetBytes actual)
                        |> fun result -> Expect.wantError result "Every byte participates."

                    Expect.stringContains
                        message
                        "src/C.cs / width 40, spaces"
                        "Locate the first differing file and configuration."
            }
            for name, source, expected, options in fixtures () do
                test ($"frozen generated output / {name}") {
                    use worker = new Worker()

                    let settings =
                        { Settings.Default with
                            AutoEndOfLine = false
                            Printer = options
                        }

                    worker.Print(source, settings)
                    let actual = worker.OutputBytes.ToArray()

                    Expect.equal
                        actual
                        (Encoding.UTF8.GetBytes expected)
                        "Exact output captured from CSharpier in "

                    worker.Print(expected, settings)

                    Expect.equal
                        (worker.OutputBytes.ToArray())
                        actual
                        "The approved output is idempotent."
                }

            test "every fixture source is a fixed point at every width" {
                let widths = [ 20; 30; 40; 60; 80; 100; 120 ]

                let unstable =
                    [
                        use worker = new Worker()

                        for name, source, _, options in fixtures () do
                            for width in widths do
                                let settings =
                                    { Settings.Default with
                                        AutoEndOfLine = false
                                        Printer = { options with Width = width }
                                    }

                                worker.Print(source, settings)
                                let once = worker.OutputText
                                worker.Print(once, settings)

                                if worker.OutputText <> once then
                                    $"{name} at width {width}"
                    ]

                Expect.equal unstable [] "Formatting an output again must not change it."
            }
        ]

let tests = TestList([ frozen ], Normal) |> testSequenced
