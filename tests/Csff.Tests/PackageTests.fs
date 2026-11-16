module Csff.Tests.PackageTests

open System.IO
open System.Text.RegularExpressions
open Expecto

let tests =
    testList
        "package"
        [
            test "no project the CLI links references Roslyn" {
                let referenced (project: string) =
                    Regex.IsMatch(
                        File.ReadAllText project,
                        @"Include\s*=\s*[""']Microsoft\.CodeAnalysis"
                    )

                let offenders =
                    Directory.GetFiles(
                        Path.Combine(Checkout.root (), "src"),
                        "*.fsproj",
                        SearchOption.AllDirectories
                    )
                    |> Array.filter referenced
                    |> Array.map Path.GetFileName
                    |> Array.sort

                Expect.isEmpty
                    offenders
                    ("Roslyn is referenced under src/: " + System.String.Join(", ", offenders) + ".")

                let oracles =
                    Directory.GetFiles(
                        Path.Combine(Checkout.root (), "tests"),
                        "*.fsproj",
                        SearchOption.AllDirectories
                    )
                    |> Array.filter referenced
                    |> Array.map Path.GetFileName
                    |> Array.sort

                Expect.equal
                    oracles
                    [| "Csff.Gate.fsproj"; "Csff.Oracles.fsproj" |]
                    "The adjudicator and the suite's oracles are what reference Roslyn."
            }
        ]
