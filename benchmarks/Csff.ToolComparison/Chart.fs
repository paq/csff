module Csff.ToolComparison.Chart

open System
open System.Globalization
open System.IO
open System.Text
open System.Text.Json.Nodes
open System.Text.RegularExpressions
open Csff.ToolComparison.Shared

let width = 840
let lightFile = "chart-light.svg"
let darkFile = "chart-dark.svg"

[<NoComparison>]
type private Theme =
    {
        Series: string array
        Primary: string
        Secondary: string
        Muted: string
        Grid: string
        Baseline: string
    }

let private light =
    {
        Series = [| "#2a78d6"; "#eb6834"; "#1baf7a" |]
        Primary = "#1f2328"
        Secondary = "#52514e"
        Muted = "#6e6d68"
        Grid = "#e1e0d9"
        Baseline = "#c3c2b7"
    }

let private dark =
    {
        Series = [| "#3987e5"; "#d95926"; "#199e70" |]
        Primary = "#f0efec"
        Secondary = "#c3c2b7"
        Muted = "#9a9890"
        Grid = "#2c2c2a"
        Baseline = "#45443f"
    }

let private ratio (value: float) =
    if value < 10.0 then
        sprintf "%.1f×" value
    else
        sprintf "%.0f×" value

let private niceStep (maximum: float) =
    if maximum <= 0.0 then
        1.0
    else
        let raw = maximum / 5.0
        let magnitude = Math.Pow(10.0, Math.Floor(Math.Log10 raw))
        let residual = raw / magnitude

        let factor =
            if residual <= 1.0 then 1.0
            elif residual <= 2.0 then 2.0
            elif residual <= 5.0 then 5.0
            else 10.0

        factor * magnitude

let private tick (value: float) =
    if value = Math.Floor value then
        sprintf "%.0f s" value
    else
        sprintf "%g s" value

let private render (results: JsonNode) (theme: Theme) =
    let width = float width
    let margin = 24.0
    let plotLeft = 224.0
    let plotRight = width - 136.0
    let plotWidth = plotRight - plotLeft
    let barHeight = 12.0
    let barGap = 3.0
    let rowHeight = 64.0
    let plotTop = 104.0
    let repositories = repositoriesBySize results

    let maximum =
        repositories
        |> Seq.collect (fun repository -> tools |> Seq.choose (medianSeconds repository))
        |> Seq.fold max 0.0

    let step = niceStep maximum
    let axisMaximum = Math.Max(step, Math.Ceiling(maximum / step) * step)
    let plotBottom = plotTop + float repositories.Length * rowHeight
    let scale value = value / axisMaximum * plotWidth
    let svg = StringBuilder()
    let add (line: string) = svg.Append(line).Append('\n') |> ignore
    let machine = results["machine"]
    let versions = results["tools"]
    let settings = results["settings"]

    let cores = Regex.Replace(text machine "cores", @"^(\d+)\b(?!\s*cores)", "$1 cores")

    let machineLine =
        [
            text machine "model"
            text machine "cpu"
            cores
            text machine "memory" + " RAM"
            text machine "os"
        ]
        |> List.filter (fun part -> part.Trim().Length > 0 && part <> " RAM")
        |> fun parts -> "Machine: " + String.Join(", ", parts)

    let csffVersion = text versions "csff"
    let csharpierVersion = text versions "csharpier"
    let formatVersion = text versions "dotnet-format"
    let sdkVersion = text versions "dotnet-sdk"

    let toolLine =
        $"Tools: csff {csffVersion} (Native AOT), CSharpier {csharpierVersion}, "
        + $"dotnet format {formatVersion}, .NET SDK {sdkVersion}"

    let runs = settings["runs"].GetValue<int>()
    let warmups = settings["warmups"].GetValue<int>()
    let rounds = if warmups = 1 then "round" else "rounds"

    let methodLine =
        $"Write mode from a clean checkout every run, no cache, *.cs files only. Median of {runs} "
        + $"runs after {warmups} warm-up {rounds}."

    let stack =
        match settings["dotnetFormatThreadStackBytes"] with
        | null -> None
        | value -> Some(value.GetValue<int>() / (1024 * 1024))

    let skips =
        repositories
        |> Array.choose (fun repository ->
            match (toolResult repository "dotnet-format")["skipped"] with
            | null -> None
            | files ->
                let count = files.AsArray().Count
                let noun = if count = 1 then "file" else "files"
                Some $"""{count} {noun} in {text repository "name"}""")
        |> fun parts -> String.Join(" and ", parts)

    let noteLines =
        match stack, skips with
        | None, "" -> []
        | Some megabytes, "" ->
            [
                $"So that it finishes, dotnet format runs with a {megabytes} MB thread stack."
            ]
        | None, files -> [ $"dotnet format skips {files} that crash it." ]
        | Some megabytes, files ->
            [
                $"So that it finishes, dotnet format runs with a {megabytes} MB thread stack and skips "
                + $"{files} that crash it."
            ]

    let footerLines = [ machineLine; toolLine; methodLine ] @ noteLines
    let footerTop = plotBottom + 60.0
    let height = footerTop + float footerLines.Length * 18.0 + 16.0

    let summary =
        repositories
        |> Seq.map (fun repository ->
            let parts =
                tools
                |> Seq.map (fun tool ->
                    match medianSeconds repository tool with
                    | Some value -> $"{tool.Label} {formatSeconds value}"
                    | None -> $"{tool.Label} failed")

            text repository "name" + ": " + String.Join(", ", parts))
        |> fun lines -> String.Join("; ", lines)

    add (
        sprintf
            "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"%.0f\" height=\"%.0f\" viewBox=\"0 0 %.0f %.0f\" role=\"img\" aria-labelledby=\"title desc\" font-family=\"-apple-system, BlinkMacSystemFont, 'Segoe UI', 'Noto Sans', Helvetica, Arial, sans-serif\">"
            width
            height
            width
            height
    )

    add
        "<title id=\"title\">Time to format C# in dotnet repositories: csff, CSharpier and dotnet format whitespace</title>"

    add
        $"<desc id=\"desc\">Median wall-clock seconds to format, lower is better. {escape summary}. {escape machineLine}.</desc>"

    add (
        sprintf
            "<text x=\"%.0f\" y=\"30\" font-size=\"16\" font-weight=\"600\" fill=\"%s\">Time to format C# in dotnet/* repositories</text>"
            margin
            theme.Primary
    )

    add (
        sprintf
            "<text x=\"%.0f\" y=\"51\" font-size=\"12\" fill=\"%s\">Median wall-clock time to format every .cs file in place. Lower is better.</text>"
            margin
            theme.Secondary
    )

    let mutable legendX = margin

    for index, tool in Array.indexed tools do
        add (
            sprintf
                "<rect x=\"%.1f\" y=\"68\" width=\"10\" height=\"10\" rx=\"2\" fill=\"%s\"/>"
                legendX
                theme.Series[index]
        )

        add (
            sprintf
                "<text x=\"%.1f\" y=\"77\" font-size=\"12\" fill=\"%s\">%s</text>"
                (legendX + 16.0)
                theme.Secondary
                (escape tool.Label)
        )

        legendX <- legendX + 16.0 + float tool.Label.Length * 7.0 + 22.0

    for count in 0 .. int (Math.Round(axisMaximum / step)) do
        let value = float count * step
        let x = plotLeft + scale value

        add (
            sprintf
                "<line x1=\"%.1f\" y1=\"%.1f\" x2=\"%.1f\" y2=\"%.1f\" stroke=\"%s\" stroke-width=\"1\"/>"
                x
                plotTop
                x
                plotBottom
                (if value = 0.0 then theme.Baseline else theme.Grid)
        )

        add (
            sprintf
                "<text x=\"%.1f\" y=\"%.1f\" font-size=\"11\" fill=\"%s\" text-anchor=\"middle\">%s</text>"
                x
                (plotBottom + 18.0)
                theme.Muted
                (tick value)
        )

    add (
        sprintf
            "<text x=\"%.1f\" y=\"%.1f\" font-size=\"11\" fill=\"%s\" text-anchor=\"middle\">Wall-clock time in seconds</text>"
            (plotLeft + plotWidth / 2.0)
            (plotBottom + 38.0)
            theme.Muted
    )

    for row, repository in Array.indexed repositories do
        let rowTop = plotTop + float row * rowHeight
        let center = rowTop + rowHeight / 2.0
        let files = repository["files"].GetValue<int>()

        add (
            sprintf
                "<text x=\"%.1f\" y=\"%.1f\" font-size=\"13\" fill=\"%s\" text-anchor=\"end\">%s</text>"
                (plotLeft - 14.0)
                (center - 2.0)
                theme.Primary
                (escape (text repository "name"))
        )

        add (
            sprintf
                "<text x=\"%.1f\" y=\"%.1f\" font-size=\"11\" fill=\"%s\" text-anchor=\"end\">%s .cs files</text>"
                (plotLeft - 14.0)
                (center + 14.0)
                theme.Muted
                (files.ToString("N0", CultureInfo.InvariantCulture))
        )

        let groupTop = center - (3.0 * barHeight + 2.0 * barGap) / 2.0
        let baseline = medianSeconds repository tools[0]

        for index, tool in Array.indexed tools do
            let y = groupTop + float index * (barHeight + barGap)

            match medianSeconds repository tool with
            | Some measured ->
                let w = Math.Max(2.0, scale measured)
                let r = Math.Min(4.0, Math.Min(w / 2.0, barHeight / 2.0))

                add (
                    sprintf
                        "<path d=\"M%.1f %.1fH%.1fA%.1f %.1f 0 0 1 %.1f %.1fV%.1fA%.1f %.1f 0 0 1 %.1f %.1fH%.1fZ\" fill=\"%s\"/>"
                        plotLeft
                        y
                        (plotLeft + w - r)
                        r
                        r
                        (plotLeft + w)
                        (y + r)
                        (y + barHeight - r)
                        r
                        r
                        (plotLeft + w - r)
                        (y + barHeight)
                        plotLeft
                        theme.Series[index]
                )

                let label =
                    match baseline with
                    | Some reference when index > 0 && reference > 0.0 ->
                        $"{formatSeconds measured} · {ratio (measured / reference)} slower"
                    | _ -> formatSeconds measured

                add (
                    sprintf
                        "<text x=\"%.1f\" y=\"%.1f\" font-size=\"11\" fill=\"%s\">%s</text>"
                        (plotLeft + w + 6.0)
                        (y + barHeight - 2.0)
                        theme.Secondary
                        (escape label)
                )
            | None ->
                let result = toolResult repository tool.Key
                let failure = result["failure"].GetValue<string>()

                add (
                    sprintf
                        "<text x=\"%.1f\" y=\"%.1f\" font-size=\"11\" font-style=\"italic\" fill=\"%s\">%s did not finish (%s)</text>"
                        (plotLeft + 6.0)
                        (y + barHeight - 2.0)
                        theme.Muted
                        (escape tool.Label)
                        (escape failure)
                )

    add (
        sprintf
            "<line x1=\"%.1f\" y1=\"%.1f\" x2=\"%.1f\" y2=\"%.1f\" stroke=\"%s\" stroke-width=\"1\"/>"
            margin
            (footerTop - 16.0)
            (width - margin)
            (footerTop - 16.0)
            theme.Grid
    )

    for index, line in List.indexed footerLines do
        add (
            sprintf
                "<text x=\"%.1f\" y=\"%.1f\" font-size=\"11\" fill=\"%s\">%s</text>"
                margin
                (footerTop + float index * 18.0)
                theme.Secondary
                (escape line)
        )

    add "</svg>"
    svg.ToString()

let write (results: JsonNode) (output: string) =
    Directory.CreateDirectory output |> ignore

    for name, theme in [ lightFile, light; darkFile, dark ] do
        let path = Path.Combine(output, name)
        File.WriteAllText(path, render results theme, UTF8Encoding false)
        printfn "Wrote %s" path
