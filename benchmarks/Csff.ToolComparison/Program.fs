module Csff.ToolComparison.Program

open System
open System.Globalization
open System.IO
open System.Text.Json.Nodes
open Csff.ToolComparison.Shared

let private usage =
    "Usage: dotnet run -c Release --project benchmarks/Csff.ToolComparison -- [options]\n\
\n\
  Builds csff with Native AOT, times csff, CSharpier and dotnet format whitespace formatting\n\
  shallow clones of dotnet/* repositories in place, resetting each clone before every run,\n\
  and writes results.json and a light and a dark SVG bar chart. Then it puts the chart in\n\
  README.md, replacing whatever sits between these two lines:\n\
\n\
    <!-- tool-comparison:start -->\n\
    <!-- tool-comparison:end -->\n\
\n\
  --repos a,b,c            repository names under github.com/dotnet (default: runtime, roslyn,\n\
                           aspnetcore, efcore, maui, winforms, wpf, BenchmarkDotNet)\n\
  --runs N                 measured runs per tool and repository (default: 5)\n\
  --warmups N              unmeasured runs first (default: 1)\n\
  --work DIR               clones and tools (default: out/tool-comparison.noindex)\n\
  --output DIR             results and charts (default: results beside the project)\n\
  --csff PATH              time this csff executable instead of building one\n\
  --csharpier-version V    the CSharpier version to install (default: 1.4.0)\n\
  --readme PATH            a Markdown file with the markers; repeat for more files\n\
                           (default: README.md at the repository root)\n\
  --no-readme              leave Markdown files alone\n\
  --render-only            redraw the charts and README from results.json without measuring\n"

[<EntryPoint>]
let main argv =
    let root = repositoryRoot ()

    let mutable settings: Measure.Settings =
        {
            Repositories = Measure.defaultRepositories
            Runs = 5
            Warmups = 1
            Work = Path.Combine(root, "out", "tool-comparison.noindex")
            Output = Path.Combine(projectDirectory (), "results")
            Csff = None
            CSharpierVersion = "1.4.0"
        }

    let mutable renderOnly = false
    let mutable readmes: string list = []
    let mutable noReadme = false
    let mutable error = null
    let mutable index = 0

    let count (text: string) =
        match Int32.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture) with
        | true, value -> Some value
        | _ -> None

    let takesValue =
        set
            [
                "--repos"
                "--runs"
                "--warmups"
                "--work"
                "--output"
                "--csff"
                "--csharpier-version"
                "--readme"
            ]

    while isNull error && index < argv.Length do
        let flag = argv[index]

        if takesValue.Contains flag && index + 1 < argv.Length then
            let value = argv[index + 1]
            index <- index + 2

            match flag with
            | "--repos" ->
                settings <-
                    { settings with
                        Repositories =
                            value.Split(
                                ',',
                                StringSplitOptions.RemoveEmptyEntries
                                ||| StringSplitOptions.TrimEntries
                            )
                    }
            | "--runs" ->
                match count value with
                | Some runs when runs > 0 -> settings <- { settings with Runs = runs }
                | _ -> error <- "--runs takes a positive integer."
            | "--warmups" ->
                match count value with
                | Some warmups -> settings <- { settings with Warmups = warmups }
                | None -> error <- "--warmups takes a non-negative integer."
            | "--work" ->
                settings <-
                    { settings with
                        Work = Path.GetFullPath value
                    }
            | "--output" ->
                settings <-
                    { settings with
                        Output = Path.GetFullPath value
                    }
            | "--csff" ->
                settings <-
                    { settings with
                        Csff = Some(Path.GetFullPath value)
                    }
            | "--readme" -> readmes <- Path.GetFullPath value :: readmes
            | _ ->
                settings <-
                    { settings with
                        CSharpierVersion = value
                    }
        else
            index <- index + 1

            match flag with
            | "--render-only" -> renderOnly <- true
            | "--no-readme" -> noReadme <- true
            | "--help"
            | "-h" -> error <- ""
            | argument -> error <- "Unexpected argument " + argument + "."

    match error with
    | null ->
        let targets =
            if noReadme then
                []
            elif List.isEmpty readmes then
                [ Path.Combine(root, "README.md") ]
            else
                List.rev readmes

        try
            let results =
                if renderOnly then
                    JsonNode.Parse(File.ReadAllText(Path.Combine(settings.Output, "results.json")))
                else
                    Measure.run settings :> JsonNode

            Chart.write results settings.Output

            for readme in targets do
                Readme.update results settings.Output readme

            0
        with failure ->
            eprintfn "%s" failure.Message
            1
    | "" ->
        printf "%s" usage
        0
    | message ->
        eprintfn "%s\n\n%s" message usage
        2
