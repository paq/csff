namespace Csff.Cli

open System
open System.Diagnostics
open System.IO
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Threading

[<assembly: InternalsVisibleTo("Csff.Tests")>]
do ()

module Program =
    let private usage =
        """Usage: csff [--check | --write-stdout] [options] [files or directories...]
Formats C# only. With no paths, formats the current directory.
  --check               Report unformatted files without rewriting them
  --write-stdout        Print one file, or stdin when no path / '-' is supplied
  --config-path FILE    Use a JSON/YAML configuration file
  --ignore-path FILE    Use this ignore file instead of discovered ignores
  --include-generated   Include generated file names and leading comments
  --no-cache            Neither read nor write the formatting cache
  --cache-path DIR      Store bounded per-input-root caches in DIR
  --jobs N              Maximum parallel workers (default: processor count)
  --help                Show this help"""

    let unverifiedExitCode = 3

    let mutable private standardError: Stream = null

    let private writeReport (text: string) =
        if isNull standardError then
            Console.Error.Write text
        else
            let bytes = Console.Error.Encoding.GetBytes text
            Console.Error.Flush()
            standardError.Write(bytes, 0, bytes.Length)
            standardError.Flush()

    let run (argv: string array) =
        let timer = Stopwatch.StartNew()
        let mutable check = false
        let mutable stdout = false
        let mutable noCache = false
        let mutable includeGenerated = false
        let mutable help = false
        let mutable jobs = Environment.ProcessorCount
        let mutable configPath = None
        let mutable ignorePath = None
        let mutable cachePath = None
        let paths = ResizeArray<string>()
        let mutable stdin = false

        try
            let mutable index = 0
            let mutable positional = false

            let next name =
                index <- index + 1

                if index >= argv.Length then
                    invalidArg name (name + " requires a value.")

                argv[index]

            while index < argv.Length do
                let arg = argv[index]

                if positional then
                    paths.Add arg
                else
                    match arg with
                    | "--" -> positional <- true
                    | "--check" -> check <- true
                    | "--write-stdout" -> stdout <- true
                    | "--no-cache" -> noCache <- true
                    | "--include-generated" -> includeGenerated <- true
                    | "--help"
                    | "-h" -> help <- true
                    | "--config-path" -> configPath <- Some(Path.GetFullPath(next arg))
                    | "--ignore-path" -> ignorePath <- Some(Path.GetFullPath(next arg))
                    | "--cache-path" -> cachePath <- Some(Path.GetFullPath(next arg))
                    | "--jobs" ->
                        match Int32.TryParse(next arg) with
                        | true, number when number > 0 -> jobs <- number
                        | _ -> invalidArg arg "--jobs must be positive."
                    | "-" ->
                        stdin <- true
                        paths.Add arg
                    | arg when arg.StartsWith('-') ->
                        invalidArg "argv" ("Unknown option " + arg + ".")
                    | _ -> paths.Add arg

                index <- index + 1

            if help then
                Console.Out.WriteLine usage
                0
            elif check && stdout then
                invalidArg "argv" "--check and --write-stdout cannot be combined."
            elif stdout then
                if paths.Count > 1 then
                    invalidArg "argv" "--write-stdout accepts one file or stdin."

                use worker = new Worker()

                let mutable input: string = null
                let mutable notice: string = null

                let printChecked (path: string) (source: string) settings =
                    input <- source

                    try
                        worker.PrintChecked(path, source, settings)
                    with :? Csff.Printer.VerificationLimitException as error ->
                        notice <- error.Message + "; the file is unchanged."
                        null

                let unverified =
                    if paths.Count = 0 || stdin then
                        let source = Console.In.ReadToEnd()

                        let settings =
                            Discovery.settingsForFile
                                (Path.Combine(Environment.CurrentDirectory, "stdin.cs"))
                                configPath
                            |> Option.defaultWith (fun () ->
                                invalidArg "config" "Stdin is excluded by configuration.")

                        Worker.Run(fun () ->
                            if not includeGenerated && worker.IsGenerated source then
                                invalidArg
                                    "argv"
                                    "--write-stdout requires an included C# file; use --include-generated for generated source."

                            printChecked "stdin.cs" source settings)
                    else
                        let root = Path.GetFullPath paths[0]

                        if not (File.Exists root) then
                            invalidArg "argv" "--write-stdout requires a C# file."

                        let files =
                            Discovery.files [| root |] configPath ignorePath includeGenerated 1

                        if files.Length <> 1 then
                            invalidArg "argv" "--write-stdout requires one included C# file."

                        let source = SourceEncoding.read root

                        Worker.Run(fun () ->
                            if not includeGenerated && worker.IsGenerated source then
                                invalidArg
                                    "argv"
                                    "--write-stdout requires an included C# file; use --include-generated for generated source."

                            printChecked root source files[0].Settings)

                if not (isNull notice) then
                    Console.Error.WriteLine notice
                    Console.Out.Write input
                    0
                elif isNull unverified then
                    Console.Out.Write worker.OutputText
                    0
                else
                    Console.Error.WriteLine unverified
                    unverifiedExitCode
            else
                if stdin then
                    invalidArg "argv" "Stdin requires --write-stdout."

                if paths.Count = 0 then
                    paths.Add Environment.CurrentDirectory

                let roots =
                    let unique = ResizeArray<string>(paths.Count)

                    let seen =
                        Collections.Generic.HashSet<string>(paths.Count, StringComparer.Ordinal)

                    for path in paths do
                        let full = Path.GetFullPath path

                        if seen.Add full then
                            unique.Add full

                    unique.ToArray()

                let struct (files, discoveredLengths) =
                    Discovery.filesWithLengths roots configPath ignorePath includeGenerated jobs

                RunStats.mark "arguments + discovery"

                use cancellation = new CancellationTokenSource()

                let handler =
                    ConsoleCancelEventHandler(fun _ event ->
                        event.Cancel <- true
                        cancellation.Cancel())

                Console.CancelKeyPress.AddHandler handler

                try
                    let results =
                        Formatter.runWithLengths
                            roots
                            files
                            discoveredLengths
                            check
                            noCache
                            includeGenerated
                            jobs
                            cachePath
                            cancellation.Token

                    RunStats.mark "format all files"

                    if RunStats.digestEnabled then
                        let lines = ResizeArray<string>(files.Length)

                        for index = 0 to results.Length - 1 do
                            let result = results[index]

                            let status =
                                if not (isNull result.Error) then "error"
                                elif not (isNull result.Unverified) then "unverified"
                                elif result.Skipped then "skipped"
                                elif result.Changed then "changed"
                                elif result.Cached then "cached"
                                else "unchanged"

                            let digest =
                                if isNull RunStats.digests || isNull RunStats.digests[index] then
                                    "-"
                                else
                                    RunStats.digests[index]

                            lines.Add(files[index].Path + "\t" + status + "\t" + digest)

                        lines.Sort(StringComparer.Ordinal)
                        File.WriteAllLines(RunStats.digestPath, lines)

                    let mutable failed = false
                    let mutable changed = 0
                    let mutable cached = 0
                    let mutable unverified = 0
                    let errorBuffer = System.Text.StringBuilder(4096)
                    let newLine = Console.Error.NewLine

                    let inline flushErrorBuffer () =
                        if errorBuffer.Length >= 65536 then
                            writeReport (errorBuffer.ToString())
                            errorBuffer.Clear() |> ignore

                    for index = 0 to results.Length - 1 do
                        let result = results[index]

                        if not (isNull result.Error) then
                            errorBuffer.Append(result.Error).Append(newLine) |> ignore
                            flushErrorBuffer ()
                            failed <- true
                        elif not (isNull result.Unverified) then
                            errorBuffer.Append(result.Unverified).Append(newLine) |> ignore
                            flushErrorBuffer ()
                            unverified <- unverified + 1
                        elif not (isNull result.Notice) then
                            errorBuffer.Append(result.Notice).Append(newLine) |> ignore
                            flushErrorBuffer ()
                        elif result.Changed then
                            changed <- changed + 1

                            if check then
                                errorBuffer
                                    .Append("Unformatted: ")
                                    .Append(files[index].Path)
                                    .Append(newLine)
                                |> ignore

                                flushErrorBuffer ()
                        elif result.Cached then
                            cached <- cached + 1

                    let verb = if check then "Checked" else "Formatted"

                    errorBuffer
                        .Append(
                            String.Format(
                                "{0} {1} C# files in {2:F0}ms ({3} cached, {4} changed, {5} unverified).",
                                verb,
                                files.Length,
                                timer.Elapsed.TotalMilliseconds,
                                cached,
                                changed,
                                unverified
                            )
                        )
                        .Append(newLine)
                    |> ignore

                    if errorBuffer.Length > 0 then
                        writeReport (errorBuffer.ToString())

                    if failed || (check && changed > 0) then 1
                    elif unverified > 0 then unverifiedExitCode
                    else 0
                finally
                    Console.CancelKeyPress.RemoveHandler handler
        with
        | :? OperationCanceledException ->
            Console.Error.WriteLine "csff: cancelled."
            130
        | error ->
            Console.Error.WriteLine("csff: " + error.Message)
            2

    [<EntryPoint>]
    let main argv =
        RunStats.mark "main"

        let availBytes = GC.GetGCMemoryInfo().TotalAvailableMemoryBytes

        if availBytes >= 8L * 1024L * 1024L * 1024L then
            let maxReserveBytes = (availBytes >>> 4) * 9L
            let mutable started = false

            for struct (totalMB, lohMB) in
                [|
                    struct (12288L, 3072L)
                    struct (10240L, 3072L)
                    struct (8192L, 2560L)
                    struct (6144L, 2048L)
                    struct (4096L, 1536L)
                    struct (2048L, 768L)
                    struct (512L, 256L)
                |] do
                let totalBytes = totalMB * 1048576L

                if not started && totalBytes <= maxReserveBytes then
                    try
                        started <- GC.TryStartNoGCRegion(totalBytes, lohMB * 1048576L, true)
                    with _ ->
                        ()
        elif availBytes >= 4L * 1024L * 1024L * 1024L then
            try
                GC.TryStartNoGCRegion(512L * 1024L * 1024L, 256L * 1024L * 1024L, true)
                |> ignore
            with _ ->
                ()

        RunStats.mark "no-GC region start"
        standardError <- Console.OpenStandardError()
        let code = run argv
        RunStats.mark "run returned"
        RunStats.report ()

        if Csff.Conformance.DeclaredTransformations.Census.enabled then
            Console.Error.WriteLine(Csff.Conformance.DeclaredTransformations.Census.report ())

        code
