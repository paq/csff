module Csff.Tests.NativeCliTests

open System
open System.Diagnostics
open System.IO
open System.Text
open Expecto

let private invoke directory arguments =
    let executable =
        Path.Combine(
            Checkout.root (),
            "out",
            "csff",
            "bin",
            if OperatingSystem.IsWindows() then
                "Csff.Cli.exe"
            else
                "Csff.Cli"
        )

    let start = ProcessStartInfo(executable, WorkingDirectory = directory)

    for argument in arguments do
        start.ArgumentList.Add argument

    match Subprocess.run start with
    | Subprocess.Exited(code, output, errors) -> code, output, errors
    | Subprocess.Timeout(output, errors) ->
        failtestf "The published native CLI did not exit.\n%s%s" output errors

let tests =
    testList
        "native cli"
        [
            test "published native CLI preserves YAML, encoding, cache and error contracts" {
                let root =
                    Path.Combine(Path.GetTempPath(), "csff-native-" + Guid.NewGuid().ToString("N"))

                Directory.CreateDirectory root |> ignore

                try
                    File.WriteAllText(Path.Combine(root, ".git"), "gitdir: /fixture")

                    File.WriteAllText(
                        Path.Combine(root, ".csffrc.yaml"),
                        "printWidth: &width 0x50\nindentSize: !!int '02'\nuseTabs: !!bool OFF\nendOfLine: crlf\noverrides:\n  - files: '*.cs'\n    printWidth: *width\n    indentSize: 2\n    endOfLine: crlf\n"
                    )

                    let path = Path.Combine(root, "a.cs")
                    let encoding = UnicodeEncoding(false, true, true)
                    let original = "class C{int x;}\r\n"
                    File.WriteAllText(path, original, encoding)
                    let code, _, errors = invoke root [ "--check"; "--no-cache"; "a.cs" ]
                    Expect.equal code 1 errors

                    Expect.equal
                        (File.ReadAllText path)
                        original
                        "Check leaves the source unchanged."

                    Expect.isFalse
                        (Directory.Exists(Path.Combine(root, "out")))
                        "No-cache creates no cache."

                    let code, _, errors = invoke root [ "--no-cache"; "a.cs" ]
                    Expect.equal code 0 errors
                    let expected = "class C\r\n{\r\n  int x;\r\n}\r\n"

                    Expect.equal
                        (File.ReadAllBytes path)
                        (Array.append (encoding.GetPreamble()) (encoding.GetBytes expected))
                        "The native formatter retains the BOM and encoding and applies YAML options."

                    let code, stdout, errors = invoke root [ "--write-stdout"; "a.cs" ]
                    Expect.equal code 0 errors
                    Expect.equal stdout expected "Stdout contains only formatted text."
                    let code, _, errors = invoke root [ "--check"; "a.cs" ]
                    Expect.equal code 0 errors
                    let code, _, errors = invoke root [ "--check"; "a.cs" ]
                    Expect.equal code 0 errors

                    Expect.stringContains
                        errors
                        "(1 cached, 0 changed, 0 unverified)"
                        "The AOT build reads its cache."

                    File.WriteAllText(path, "class C { void M( }", encoding)
                    let invalid = File.ReadAllBytes path
                    let code, _, errors = invoke root [ "--no-cache"; "a.cs" ]
                    Expect.equal code 1 errors

                    Expect.stringContains
                        errors
                        "Incomplete C# syntax"
                        "Recovery is rejected in native code."

                    Expect.equal
                        (File.ReadAllBytes path)
                        invalid
                        "Invalid input is never overwritten."

                    File.WriteAllText(Path.Combine(root, ".csffrc.yaml"), "printWidth: |-\n  80\n")

                    let code, _, _ = invoke root [ "--check"; "--no-cache"; "a.cs" ]
                    Expect.equal code 2 "A YAML block scalar retains its string type."
                finally
                    Directory.Delete(root, true)
            }
            test "published native CLI preserves conditional using prefixes and ignore boundaries" {
                let root =
                    Path.Combine(Path.GetTempPath(), "csff-prefix-" + Guid.NewGuid().ToString("N"))

                Directory.CreateDirectory root |> ignore

                try
                    File.WriteAllText(Path.Combine(root, ".git"), "gitdir: /fixture")
                    let path = Path.Combine(root, "prefix.cs")

                    for name, source, expected in TokenPreservationTests.conditionalUsingLayouts do
                        for eol in [ "\n"; "\r\n" ] do
                            File.WriteAllText(path, source.Replace("\n", eol))

                            let code, actual, errors =
                                invoke root [ "--write-stdout"; "--no-cache"; "prefix.cs" ]

                            Expect.equal code 0 errors

                            Expect.equal
                                actual
                                (expected.Replace("\n", eol))
                                $"{name}: native bytes."

                            File.WriteAllText(path, actual)

                            let code, repeated, errors =
                                invoke root [ "--write-stdout"; "--no-cache"; "prefix.cs" ]

                            Expect.equal code 0 errors
                            Expect.equal repeated actual $"{name}: native idempotence."

                            let code, _, errors =
                                invoke root [ "--check"; "--no-cache"; "prefix.cs" ]

                            Expect.equal code 0 errors
                finally
                    Directory.Delete(root, true)
            }
            test "published native CLI preserves signed YAML radix options" {
                let root =
                    Path.Combine(
                        Path.GetTempPath(),
                        "csff-native-integer-" + Guid.NewGuid().ToString("N")
                    )

                Directory.CreateDirectory root |> ignore

                try
                    File.WriteAllText(Path.Combine(root, ".git"), "gitdir: /fixture")
                    let path = Path.Combine(root, "a.cs")
                    File.WriteAllText(path, "class C{int x;}\n")
                    let original = File.ReadAllBytes path
                    let configuration = Path.Combine(root, ".csffrc.yaml")

                    for scalar in
                        [
                            "!!int +010"
                            "!!int +0x8"
                            "!!int +0b1000"
                            "!!int +0_1_0"
                            "!!int '+010'"
                            "!!int 010"
                            "8"
                            "0x8"
                        ] do
                        File.WriteAllText(
                            configuration,
                            "printWidth: !!int +0x50\nindentSize: " + scalar + "\n"
                        )

                        let code, stdout, errors =
                            invoke root [ "--write-stdout"; "--no-cache"; "a.cs" ]

                        Expect.equal code 0 errors
                        Expect.equal stdout "class C\n{\n        int x;\n}\n" scalar

                    for scalar in [ "!!int -0x2"; "!!int -0b10"; "!!int -02"; "!!int -2" ] do
                        File.WriteAllText(configuration, "indentSize: " + scalar + "\n")
                        let code, _, errors = invoke root [ "--write-stdout"; "--no-cache"; "a.cs" ]
                        Expect.equal code 2 "Negative options fail configuration."

                        Expect.stringContains
                            errors
                            "indentSize must be positive."
                            "Validate the signed value after parsing its radix."

                    for scalar in [ "!!int +0x8000000000000000"; "!!int +0b102"; "'2'" ] do
                        File.WriteAllText(configuration, "indentSize: " + scalar + "\n")
                        let code, _, _ = invoke root [ "--write-stdout"; "--no-cache"; "a.cs" ]
                        Expect.equal code 2 "Invalid or overflowing values are never accepted."

                    Expect.equal
                        (File.ReadAllBytes path)
                        original
                        "Stdout never rewrites the source."

                    Expect.isFalse
                        (Directory.Exists(Path.Combine(root, "out")))
                        "No cache is created."
                finally
                    Directory.Delete(root, true)
            }
        ]
