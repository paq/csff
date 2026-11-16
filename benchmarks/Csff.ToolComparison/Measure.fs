module Csff.ToolComparison.Measure

open System
open System.Collections.Generic
open System.Diagnostics
open System.Globalization
open System.IO
open System.Runtime.InteropServices
open System.Text.Json
open System.Text.Json.Nodes
open System.Text.RegularExpressions
open Csff.ToolComparison.Shared

let defaultRepositories =
    [|
        "runtime"
        "roslyn"
        "aspnetcore"
        "efcore"
        "maui"
        "winforms"
        "wpf"
        "BenchmarkDotNet"
    |]

let private dotnetFormatStackBytes = 64 * 1024 * 1024

let private dotnetFormatSkips =
    Map
        [
            "wpf",
            [
                "src/Microsoft.DotNet.Wpf/src/WpfGfx/codegen/mcg/generators/ManagedStruct.cs"
                "src/Microsoft.DotNet.Wpf/src/WpfGfx/codegen/mcg/helpers/CollectionHelper.cs"
            ]
        ]

[<NoComparison>]
type Settings =
    {
        Repositories: string array
        Runs: int
        Warmups: int
        Work: string
        Output: string
        Csff: string option
        CSharpierVersion: string
    }

let private dotnetHost () =
    match Environment.GetEnvironmentVariable "DOTNET_HOST_PATH" with
    | null
    | "" -> "dotnet"
    | path -> path

let private startInfo (file: string) (arguments: string seq) (directory: string) =
    let start =
        ProcessStartInfo(file, WorkingDirectory = directory, UseShellExecute = false)

    for argument in arguments do
        start.ArgumentList.Add argument

    start

let private describe (file: string) (arguments: string seq) =
    file + " " + String.Join(" ", arguments)

let private read (file: string) (arguments: string list) (directory: string) =
    let start = startInfo file arguments directory
    start.RedirectStandardOutput <- true
    use proc = Process.Start start
    let text = proc.StandardOutput.ReadToEnd()
    proc.WaitForExit()

    if proc.ExitCode <> 0 then
        failwithf "%s exited with %d." (describe file arguments) proc.ExitCode

    text

let private tryRead (file: string) (arguments: string list) =
    try
        Some((read file arguments Environment.CurrentDirectory).Trim())
    with _ ->
        None

let private passThrough (file: string) (arguments: string list) (directory: string) =
    use proc = Process.Start(startInfo file arguments directory)
    proc.WaitForExit()

    if proc.ExitCode <> 0 then
        failwithf "%s exited with %d." (describe file arguments) proc.ExitCode

[<NoComparison>]
type private Outcome =
    {
        ExitCode: int
        Seconds: float
        Tail: string list
    }

let private timed
    (file: string)
    (arguments: string list)
    (environment: (string * string) list)
    (directory: string)
    =
    let start = startInfo file arguments directory

    for name, value in environment do
        start.Environment[name] <- value

    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true
    let tail = Queue<string>()
    let gate = obj ()

    let receive (line: string) =
        if not (isNull line) then
            lock gate (fun () ->
                tail.Enqueue line

                if tail.Count > 200 then
                    tail.Dequeue() |> ignore)

    use proc = new Process(StartInfo = start)
    proc.OutputDataReceived.Add(fun event -> receive event.Data)
    proc.ErrorDataReceived.Add(fun event -> receive event.Data)
    let watch = Stopwatch.StartNew()
    proc.Start() |> ignore
    proc.BeginOutputReadLine()
    proc.BeginErrorReadLine()
    proc.WaitForExit()
    watch.Stop()

    {
        ExitCode = proc.ExitCode
        Seconds = watch.Elapsed.TotalSeconds
        Tail = lock gate (fun () -> List.ofSeq tail)
    }

let private median (values: float list) =
    let sorted = List.sort values |> Array.ofList
    let middle = sorted.Length / 2

    if sorted.Length % 2 = 1 then
        sorted[middle]
    else
        (sorted[middle - 1] + sorted[middle]) / 2.0

let private gigabytes (bytes: int64) =
    sprintf "%.0f GB" (float bytes / 1073741824.0)

let private machine () =
    let os = RuntimeInformation.OSDescription
    let memory = GC.GetGCMemoryInfo().TotalAvailableMemoryBytes |> gigabytes
    let processors = string Environment.ProcessorCount

    let model, cpu, cores, memory, os =
        if OperatingSystem.IsMacOS() then
            let profile =
                tryRead "system_profiler" [ "SPHardwareDataType" ] |> Option.defaultValue ""

            let field (name: string) =
                let matched =
                    Regex.Match(
                        profile,
                        @"^\s*" + Regex.Escape name + @":\s*(.+)$",
                        RegexOptions.Multiline
                    )

                if matched.Success then
                    matched.Groups[1].Value.Trim()
                else
                    ""

            let chip =
                match field "Chip" with
                | "" -> field "Processor Name"
                | chip -> chip

            let version = tryRead "sw_vers" [ "-productVersion" ] |> Option.defaultValue ""

            field "Model Name",
            chip,
            (match field "Total Number of Cores" with
             | "" -> processors
             | cores -> cores),
            (match field "Memory" with
             | "" -> memory
             | value -> value),
            "macOS " + version
        elif OperatingSystem.IsLinux() then
            let lines (path: string) =
                if File.Exists path then File.ReadAllLines path else [||]

            let cpu =
                lines "/proc/cpuinfo"
                |> Array.tryFind (fun line ->
                    line.StartsWith("model name", StringComparison.Ordinal))
                |> Option.map (fun line -> line.Substring(line.IndexOf(':') + 1).Trim())
                |> Option.defaultValue ""

            let release =
                lines "/etc/os-release"
                |> Array.tryFind (fun line ->
                    line.StartsWith("PRETTY_NAME=", StringComparison.Ordinal))
                |> Option.map (fun line -> line.Substring(12).Trim('"'))
                |> Option.defaultValue os

            let product =
                lines "/sys/devices/virtual/dmi/id/product_name"
                |> Array.tryHead
                |> Option.defaultValue ""

            product.Trim(), cpu, processors, memory, release
        else
            let cpu =
                if OperatingSystem.IsWindows() then
                    match
                        Microsoft.Win32.Registry.GetValue(
                            @"HKEY_LOCAL_MACHINE\HARDWARE\DESCRIPTION\System\CentralProcessor\0",
                            "ProcessorNameString",
                            (null: obj)
                        )
                    with
                    | :? string as name -> name.Trim()
                    | _ -> ""
                else
                    ""

            "", cpu, processors, memory, os

    let node = JsonObject()
    node["model"] <- JsonValue.Create model
    node["cpu"] <- JsonValue.Create cpu
    node["cores"] <- JsonValue.Create cores
    node["memory"] <- JsonValue.Create memory
    node["os"] <- JsonValue.Create os
    node["architecture"] <- JsonValue.Create(string RuntimeInformation.OSArchitecture)
    node

let private versionPrefix (text: string) =
    let matched = Regex.Match(text, @"\d+(\.\d+)+")
    if matched.Success then matched.Value else text.Trim()

let private csffVersion (root: string) =
    let project =
        File.ReadAllText(Path.Combine(root, "src", "Csff.Cli", "Csff.Cli.fsproj"))

    Regex.Match(project, "<CsffBaseVersion>(.*?)</CsffBaseVersion>").Groups[1].Value

let private csharpOnlyIgnore = "*\n!*/\n!*.cs\n"

let private buildCsff (root: string) =
    printfn "Building csff with Native AOT"

    passThrough
        (dotnetHost ())
        [ "build"; Path.Combine(root, "csff.slnx"); "-t:Native"; "--nologo"; "-v:q" ]
        root

    let executable =
        Path.Combine(
            root,
            "out",
            "csff",
            "bin",
            (if OperatingSystem.IsWindows() then
                 "Csff.Cli.exe"
             else
                 "Csff.Cli")
        )

    if not (File.Exists executable) then
        failwithf "Building csff left no executable at %s." executable

    executable

let private clone (work: string) (name: string) =
    let directory = Path.Combine(work, "repos", name)

    if not (Directory.Exists(Path.Combine(directory, ".git"))) then
        Directory.CreateDirectory(Path.Combine(work, "repos")) |> ignore
        printfn "Cloning dotnet/%s" name

        passThrough
            "git"
            [
                "clone"
                "--depth"
                "1"
                "--single-branch"
                "--no-tags"
                $"https://github.com/dotnet/{name}.git"
                directory
            ]
            work

    directory

let private csharpFiles (directory: string) =
    (read "git" [ "ls-files"; "-z"; "--"; "*.cs" ] directory)
        .Split('\000', StringSplitOptions.RemoveEmptyEntries)
        .Length

let private restore (directory: string) =
    read "git" [ "reset"; "--hard"; "--quiet" ] directory |> ignore
    read "git" [ "clean"; "-fdq" ] directory |> ignore

let private installCSharpier (root: string) (work: string) (version: string) =
    let directory = Path.Combine(work, "tools", "csharpier-" + version)

    let executable =
        Path.Combine(
            directory,
            (if OperatingSystem.IsWindows() then
                 "csharpier.exe"
             else
                 "csharpier")
        )

    if not (File.Exists executable) then
        passThrough
            (dotnetHost ())
            [
                "tool"
                "install"
                "csharpier"
                "--version"
                version
                "--tool-path"
                directory
            ]
            root

    executable

let run (settings: Settings) =
    let root = repositoryRoot ()
    let work = Path.GetFullPath settings.Work
    Directory.CreateDirectory work |> ignore

    let csff =
        match settings.Csff with
        | Some path when File.Exists path -> path
        | Some path -> failwithf "No csff executable at %s." path
        | None -> buildCsff root

    let csharpier = installCSharpier root work settings.CSharpierVersion
    let ignoreFile = Path.Combine(work, "csharpier-csharp-only.ignore")
    File.WriteAllText(ignoreFile, csharpOnlyIgnore)
    let dotnet = dotnetHost ()

    let dotnetFormatEnvironment =
        [
            "DOTNET_Thread_DefaultStackSize",
            dotnetFormatStackBytes.ToString("X", CultureInfo.InvariantCulture)
        ]

    let skipped (tool: Tool) (name: string) =
        if tool.Key = "dotnet-format" then
            Map.tryFind name dotnetFormatSkips |> Option.defaultValue []
        else
            []

    let command (tool: Tool) (name: string) (repository: string) =
        match tool.Key with
        | "csff" -> csff, [ "--no-cache"; repository ], []
        | "csharpier" ->
            csharpier,
            [ "format"; repository; "--no-msbuild-check"; "--ignore-path"; ignoreFile ],
            []
        | _ ->
            let exclude =
                match skipped tool name with
                | [] -> []
                | files -> "--exclude" :: files

            dotnet,
            [ "format"; "whitespace"; repository; "--folder"; "--include"; "**/*.cs" ]
            @ exclude,
            dotnetFormatEnvironment

    let toolVersions = JsonObject()
    toolVersions["csff"] <- JsonValue.Create(csffVersion root)

    toolVersions["csharpier"] <-
        JsonValue.Create((read csharpier [ "--version" ] work).Trim() |> versionPrefix)

    toolVersions["dotnet-format"] <-
        JsonValue.Create((read dotnet [ "format"; "--version" ] work) |> versionPrefix)

    toolVersions["dotnet-sdk"] <- JsonValue.Create((read dotnet [ "--version" ] work).Trim())

    let results = JsonObject()

    results["date"] <-
        JsonValue.Create(DateTime.UtcNow.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture))

    results["machine"] <- machine ()
    results["tools"] <- toolVersions
    let options = JsonObject()
    options["runs"] <- JsonValue.Create settings.Runs
    options["warmups"] <- JsonValue.Create settings.Warmups
    options["dotnetFormatThreadStackBytes"] <- JsonValue.Create dotnetFormatStackBytes
    results["settings"] <- options
    let repositories = JsonArray()
    results["repositories"] <- repositories

    let save () =
        Directory.CreateDirectory settings.Output |> ignore

        File.WriteAllText(
            Path.Combine(settings.Output, "results.json"),
            results.ToJsonString(JsonSerializerOptions(WriteIndented = true, NewLine = "\n"))
            + "\n"
        )

    for name in settings.Repositories do
        let directory = clone work name
        let files = csharpFiles directory
        let commit = (read "git" [ "rev-parse"; "HEAD" ] directory).Trim()
        printfn "dotnet/%s at %s: %d tracked .cs files" name commit[..9] files
        let seconds = Dictionary<string, ResizeArray<float>>()
        let exits = Dictionary<string, ResizeArray<int>>()
        let reported = Dictionary<string, string>()
        let failures = Dictionary<string, string>()

        for tool in tools do
            seconds[tool.Key] <- ResizeArray()
            exits[tool.Key] <- ResizeArray()

        let rounds = settings.Warmups + settings.Runs

        for round in 0 .. rounds - 1 do
            for offset in 0 .. tools.Length - 1 do
                let tool = tools[(round + offset) % tools.Length]

                if not (failures.ContainsKey tool.Key) then
                    restore directory
                    let file, arguments, environment = command tool name directory
                    let outcome = timed file arguments environment work

                    let label =
                        if round < settings.Warmups then
                            "warm-up"
                        else
                            $"run {round - settings.Warmups + 1}/{settings.Runs}"

                    printfn
                        "  %-26s %-10s %8.2f s  exit %d"
                        tool.Label
                        label
                        outcome.Seconds
                        outcome.ExitCode

                    if not (List.contains outcome.ExitCode tool.Accepted) then
                        failures[tool.Key] <- $"exit {outcome.ExitCode}"
                        eprintfn "  %s failed on dotnet/%s:" tool.Label name

                        for line in outcome.Tail |> List.rev |> List.truncate 20 |> List.rev do
                            eprintfn "    %s" line
                    else
                        outcome.Tail
                        |> List.tryPick (fun line ->
                            let matched = tool.Summary.Match line
                            if matched.Success then Some matched.Value else None)
                        |> Option.iter (fun summary -> reported[tool.Key] <- summary)

                        if round >= settings.Warmups then
                            seconds[tool.Key].Add outcome.Seconds
                            exits[tool.Key].Add outcome.ExitCode

        restore directory
        let entry = JsonObject()
        entry["name"] <- JsonValue.Create("dotnet/" + name)
        entry["commit"] <- JsonValue.Create commit
        entry["files"] <- JsonValue.Create files
        let measured = JsonObject()

        for tool in tools do
            let node = JsonObject()

            match failures.TryGetValue tool.Key with
            | true, failure -> node["failure"] <- JsonValue.Create failure
            | _ -> node["median"] <- JsonValue.Create(median (List.ofSeq seconds[tool.Key]))

            let runs = JsonArray()

            for value in seconds[tool.Key] do
                runs.Add(JsonValue.Create(Math.Round(value, 4)))

            node["seconds"] <- runs
            let codes = JsonArray()

            for code in exits[tool.Key] do
                codes.Add(JsonValue.Create code)

            node["exitCodes"] <- codes

            match reported.TryGetValue tool.Key with
            | true, summary -> node["summary"] <- JsonValue.Create summary
            | _ -> ()

            match skipped tool name with
            | [] -> ()
            | files ->
                let list = JsonArray()

                for path in files do
                    list.Add(JsonValue.Create path)

                node["skipped"] <- list

            measured[tool.Key] <- node

        entry["tools"] <- measured
        repositories.Add entry
        save ()

    results
