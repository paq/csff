module Csff.ToolComparison.Readme

open System
open System.IO
open System.Text
open System.Text.Json.Nodes
open System.Text.RegularExpressions
open Csff.ToolComparison.Shared

let startMarker = "<!-- tool-comparison:start -->"
let endMarker = "<!-- tool-comparison:end -->"

let private startPattern =
    Regex(@"<!--\s*tool-comparison:start\b.*?-->", RegexOptions.Singleline)

let private endPattern =
    Regex(@"<!--\s*tool-comparison:end\b.*?-->", RegexOptions.Singleline)

let private description (results: JsonNode) =
    let repositories = repositoriesBySize results
    let machine = results["machine"]

    let place =
        [ text machine "model"; text machine "cpu" ]
        |> List.filter (fun part -> part.Trim().Length > 0)
        |> fun parts -> String.Join(", ", parts)

    let opening =
        $"Bar chart of the median time to format every .cs file in {repositories.Length} dotnet/* repositories"
        + (if place = "" then "." else $", measured on {place}.")

    match Array.tryHead repositories with
    | None -> opening
    | Some largest ->
        let parts =
            tools
            |> Array.map (fun tool ->
                match medianSeconds largest tool with
                | Some value -> $"{tool.Label} {formatSeconds value}"
                | None -> $"{tool.Label} did not finish")

        $"""{opening} On {text largest "name"}: {String.Join(", ", parts)}."""

let private picture (results: JsonNode) (output: string) (readme: string) (newLine: string) =
    let relative (file: string) =
        Path
            .GetRelativePath(Path.GetDirectoryName readme, Path.Combine(output, file))
            .Replace('\\', '/')
        |> escape

    let light = relative Chart.lightFile
    let dark = relative Chart.darkFile

    String.Join(
        newLine,
        [
            "<picture>"
            $"  <source media=\"(prefers-color-scheme: dark)\" srcset=\"{dark}\">"
            $"  <source media=\"(prefers-color-scheme: light)\" srcset=\"{light}\">"
            $"  <img alt=\"{escape (description results)}\" src=\"{light}\" width=\"{Chart.width}\">"
            "</picture>"
        ]
    )

let update (results: JsonNode) (output: string) (readme: string) =
    let path = Path.GetFullPath readme
    let original = File.ReadAllText path
    let newLine = if original.Contains "\r\n" then "\r\n" else "\n"
    let block = picture results (Path.GetFullPath output) path newLine
    let updated = StringBuilder()
    let mutable position = 0
    let mutable count = 0
    let mutable start = startPattern.Match(original, 0)

    while start.Success do
        let finish = endPattern.Match(original, start.Index + start.Length)

        if not finish.Success then
            failwithf "%s has %s with no %s after it." path startMarker endMarker

        updated
            .Append(original, position, start.Index + start.Length - position)
            .Append(newLine)
            .Append(block)
            .Append(newLine)
        |> ignore

        position <- finish.Index
        count <- count + 1
        start <- startPattern.Match(original, finish.Index + finish.Length)

    if count = 0 then
        failwithf "%s has no %s and %s to put the chart between." path startMarker endMarker

    updated.Append(original, position, original.Length - position) |> ignore
    let content = updated.ToString()

    if content <> original then
        File.WriteAllText(path, content, UTF8Encoding false)
        printfn "Updated the chart in %s" path
    else
        printfn "The chart in %s is already up to date" path
