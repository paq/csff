module Csff.Tests.Performance

open System
open System.Collections.Generic
open System.Diagnostics
open System.Globalization
open System.IO
open System.Text
open System.Text.Json
open System.Threading
open Csff.Cli
open Csff.Lexer
open Csff.Parser
open Csff.Printer

[<Struct; NoEquality; NoComparison>]
type private Stage =
    {
        mutable Ticks: int64
        mutable Bytes: int64
    }

[<NoEquality; NoComparison>]
type private Sweep =
    {
        Lex: Stage
        Parse: Stage
        Build: Stage
        Print: Stage
    }

[<NoEquality; NoComparison>]
type private Settings =
    {
        Root: string
        Files: int
        Sweeps: int
        Warmups: int
        Width: int
        Json: string
    }

let private defaults =
    {
        Root = null
        Files = 2000
        Sweeps = 5
        Warmups = 2
        Width = 100
        Json = null
    }

let private usage =
    "Usage: --measure-performance <root> [--files N] [--sweeps N] [--warmups N] \
[--width N] [--json PATH]\n\
\n\
  <root>       directory to search for *.cs, excluding bin, obj, artifacts and .git\n\
  --files N    measure N files sampled at an even stride, in ordinal path order;\n\
               0 measures every discovered file (default 2000)\n\
  --sweeps N   measured sweeps; the reported figure per stage is their median (default 5)\n\
  --warmups N  whole-corpus sweeps before measuring (default 2)\n\
  --width N    printer width (default 100; indent 4 spaces, LF)\n\
  --json PATH  also write the result as JSON\n"

let private settings (argv: string array) =
    let mutable result = defaults
    let mutable index = 0
    let mutable error = null

    let number (name: string) =
        if index + 1 >= argv.Length then
            error <- name + " needs a value."
            0
        else
            index <- index + 1

            match Int32.TryParse(argv[index], NumberStyles.None, CultureInfo.InvariantCulture) with
            | true, value -> value
            | _ ->
                error <- name + " needs a non-negative integer, not " + argv[index] + "."
                0

    while isNull error && index < argv.Length do
        match argv[index] with
        | "--files" -> result <- { result with Files = number "--files" }
        | "--sweeps" ->
            result <-
                { result with
                    Sweeps = max 1 (number "--sweeps")
                }
        | "--warmups" ->
            result <-
                { result with
                    Warmups = number "--warmups"
                }
        | "--width" ->
            result <-
                { result with
                    Width = max 1 (number "--width")
                }
        | "--json" ->
            if index + 1 >= argv.Length then
                error <- "--json needs a path."
            else
                index <- index + 1
                result <- { result with Json = argv[index] }
        | argument when argument.StartsWith("--", StringComparison.Ordinal) ->
            error <- "Unknown argument " + argument + "."
        | argument when isNull result.Root -> result <- { result with Root = argument }
        | argument -> error <- "Unexpected second root " + argument + "."

        index <- index + 1

    if isNull error && isNull result.Root then
        error <- "A corpus root is required."

    struct (result, error)

let private skipped =
    HashSet<string>(
        [ "bin"; "obj"; "artifacts"; "packages"; "node_modules"; ".git"; ".nuget" ],
        StringComparer.Ordinal
    )

let private walk (root: string) =
    let files = ResizeArray<string>()

    let rec descend (directory: string) =
        for child in Directory.EnumerateDirectories directory do
            if not (skipped.Contains(Path.GetFileName child)) then
                descend child

        files.AddRange(Directory.EnumerateFiles(directory, "*.cs"))

    descend root
    files

let private tracked (root: string) =
    try
        let start = ProcessStartInfo("git", WorkingDirectory = root)

        for argument in [ "ls-files"; "-z"; "--cached"; "--exclude-standard"; "--"; "*.cs" ] do
            start.ArgumentList.Add argument

        match Subprocess.run start with
        | Subprocess.Exited(0, output, _) ->
            let files = ResizeArray<string>()

            for entry in output.Split('\000') do
                if entry.Length > 0 then
                    files.Add(Path.Combine(root, entry))

            Some files
        | Subprocess.Exited _ -> None
        | Subprocess.Timeout(_, errors) ->
            eprintfn "git ls-files did not exit; measuring the filesystem walk. %s" errors
            None
    with _ ->
        None

let private discover (root: string) =
    let files =
        match tracked root with
        | Some files when files.Count > 0 -> files
        | _ -> walk root

    files.Sort StringComparer.Ordinal
    files

let private sample (files: ResizeArray<string>) (limit: int) =
    if limit <= 0 || files.Count <= limit then
        files.ToArray()
    else
        let stride = float files.Count / float limit
        Array.init limit (fun index -> files[min (files.Count - 1) (int (float index * stride))])

let private complete (tree: SyntaxTree) =
    let mutable result = true
    let mutable index = 0

    while result && index < tree.TokenCount do
        let token = tree.Token index

        result <-
            token.Kind <> TokenKind.BadToken
            && (token.Length > 0
                || token.Kind = TokenKind.EndOfFileToken
                || token.Kind = TokenKind.OmittedArraySizeExpressionToken
                || token.Kind = TokenKind.OmittedTypeArgumentToken)

        index <- index + 1

    index <- 0

    while result && index < tree.NodeCount do
        result <- (tree.Node index).Kind <> NodeKind.IncompleteMember
        index <- index + 1

    result && tree.RecoveredTokens = 0

let private milliseconds (ticks: int64) =
    float ticks * 1000.0 / float Stopwatch.Frequency

let private median (values: float array) =
    Array.sortInPlace values
    values[values.Length / 2]

let private megabytes (bytes: int64) = float bytes / 1e6

let private measure (argv: string array) =
    let struct (options, error) = settings argv

    if not (isNull error) then
        eprintfn "%s" error
        eprintfn ""
        eprintf "%s" usage
        2
    elif not (Directory.Exists options.Root) then
        eprintfn "No directory at %s." options.Root
        2
    else
        let printerOptions =
            { PrinterOptions.Default with
                Width = options.Width
            }

        let discovered = discover options.Root
        let paths = sample discovered options.Files
        printfn "Corpus:     %s" options.Root
        printfn "Discovered: %d files" discovered.Count

        let sources = ResizeArray<string>(paths.Length)
        let mutable unreadable = 0

        for path in paths do
            try
                sources.Add(File.ReadAllText path)
            with _ ->
                unreadable <- unreadable + 1

        let buffer = TokenBuffer()
        let tree = SyntaxTree()
        use document = new DocumentBuffer()
        use printer = new Printer()
        use builder = new SyntaxDocumentBuilder()

        let pipeline (source: string) =
            Lexer.lex source buffer
            Parser.parse source tree
            document.Reset()
            builder.Build(source, tree, document, printerOptions)
            printer.Print(source, document, printerOptions)

        let measured = ResizeArray<string>(sources.Count)
        let mutable incomplete = 0
        let mutable failed = 0
        let mutable conditional = 0
        let mutable conditioned = 0
        let mutable pathDependent = 0
        let mutable characters = 0L
        let mutable elements = 0L
        let mutable groups = 0L

        for source in sources do
            let mutable usable = false

            try
                Parser.parse source tree

                if complete tree then
                    pipeline source
                    usable <- true
                else
                    incomplete <- incomplete + 1
            with _ ->
                failed <- failed + 1

            if usable then
                measured.Add source
                characters <- characters + int64 source.Length
                elements <- elements + int64 document.Count
                groups <- groups + int64 document.GroupCount

                if (Preprocessor.symbolSets source tree).Length > 0 then
                    conditional <- conditional + 1

                if Preprocessor.conditioned tree then
                    conditioned <- conditioned + 1

                    if Preprocessor.pathDependent source tree then
                        pathDependent <- pathDependent + 1

        printfn "Measured:   %d files, %d UTF-16 characters" measured.Count characters

        printfn
            "Excluded:   %d unreadable, %d incomplete parses, %d pipeline failures"
            unreadable
            incomplete
            failed

        printfn
            "Of the measured files, %d carry conditional compilation, so their build stage"
            conditional

        printfn "includes the preprocessor's reparse and print passes."

        printfn
            "An #if appears in %d of them, and %d of those make the preprocessor lex the"
            conditioned
            pathDependent

        printfn "file again to classify their directives."

        printfn ""

        if measured.Count = 0 then
            eprintfn "No file survived the pre-pass; nothing to measure."
            1
        else
            for _ = 1 to options.Warmups do
                for source in measured do
                    pipeline source

            let sweeps = Array.init options.Sweeps (fun _ -> Unchecked.defaultof<Sweep>)
            let mutable fitCalls = 0L
            let mutable fitWork = 0L
            let mutable preparation = 0L
            let mutable triviaRecords = 0L
            let mutable triviaQueries = 0L
            let mutable triviaComparisons = 0L
            let mutable lambdaVisits = 0L

            for sweep = 0 to options.Sweeps - 1 do
                let mutable lex = { Ticks = 0L; Bytes = 0L }
                let mutable parse = { Ticks = 0L; Bytes = 0L }
                let mutable build = { Ticks = 0L; Bytes = 0L }
                let mutable print = { Ticks = 0L; Bytes = 0L }
                fitCalls <- 0L
                fitWork <- 0L
                preparation <- 0L
                triviaRecords <- 0L
                triviaQueries <- 0L
                triviaComparisons <- 0L
                lambdaVisits <- 0L

                for source in measured do
                    let lexBytes = GC.GetAllocatedBytesForCurrentThread()
                    let lexStart = Stopwatch.GetTimestamp()
                    Lexer.lex source buffer
                    lex.Ticks <- lex.Ticks + Stopwatch.GetTimestamp() - lexStart
                    lex.Bytes <- lex.Bytes + GC.GetAllocatedBytesForCurrentThread() - lexBytes

                    let parseBytes = GC.GetAllocatedBytesForCurrentThread()
                    let parseStart = Stopwatch.GetTimestamp()
                    Parser.parse source tree
                    parse.Ticks <- parse.Ticks + Stopwatch.GetTimestamp() - parseStart
                    parse.Bytes <- parse.Bytes + GC.GetAllocatedBytesForCurrentThread() - parseBytes

                    document.Reset()
                    let buildBytes = GC.GetAllocatedBytesForCurrentThread()
                    let buildStart = Stopwatch.GetTimestamp()
                    builder.Build(source, tree, document, printerOptions)
                    build.Ticks <- build.Ticks + Stopwatch.GetTimestamp() - buildStart
                    build.Bytes <- build.Bytes + GC.GetAllocatedBytesForCurrentThread() - buildBytes

                    let printBytes = GC.GetAllocatedBytesForCurrentThread()
                    let printStart = Stopwatch.GetTimestamp()
                    printer.Print(source, document, printerOptions)
                    print.Ticks <- print.Ticks + Stopwatch.GetTimestamp() - printStart
                    print.Bytes <- print.Bytes + GC.GetAllocatedBytesForCurrentThread() - printBytes

                    fitCalls <- fitCalls + int64 printer.FitCalls
                    fitWork <- fitWork + int64 printer.FitWork
                    preparation <- preparation + int64 printer.SharedPreparationWork
                    let struct (records, queries, comparisons) = builder.HeadTriviaWorkTotal
                    triviaRecords <- triviaRecords + int64 records
                    triviaQueries <- triviaQueries + int64 queries
                    triviaComparisons <- triviaComparisons + int64 comparisons
                    lambdaVisits <- lambdaVisits + int64 builder.LambdaBodyVisitsTotal

                sweeps[sweep] <-
                    {
                        Lex = lex
                        Parse = parse
                        Build = build
                        Print = print
                    }

            let times (select: Sweep -> Stage) =
                median (sweeps |> Array.map (fun sweep -> milliseconds (select sweep).Ticks))

            let bytes (select: Sweep -> Stage) =
                median (sweeps |> Array.map (fun sweep -> float (select sweep).Bytes))

            let lexTime = times (fun sweep -> sweep.Lex)
            let parseTime = times (fun sweep -> sweep.Parse)
            let buildTime = times (fun sweep -> sweep.Build)
            let printTime = times (fun sweep -> sweep.Print)
            let parseOnly = parseTime - lexTime
            let total = lexTime + parseOnly + buildTime + printTime

            let share (value: float) =
                if total > 0.0 then value / total * 100.0 else 0.0

            printfn "%d warmups, %d measured sweeps, medians" options.Warmups options.Sweeps
            printfn ""
            printfn "| Stage             |    ms | share |      MB |"
            printfn "| ----------------- | ----: | ----: | ------: |"

            let row (name: string) (time: float) (allocated: float) =
                printfn
                    "| %-17s | %5.1f | %4.1f%% | %7.3f |"
                    name
                    time
                    (share time)
                    (allocated / 1e6)

            let lexBytes = bytes (fun sweep -> sweep.Lex)
            let parseBytes = bytes (fun sweep -> sweep.Parse) - lexBytes
            let buildBytes = bytes (fun sweep -> sweep.Build)
            let printBytes = bytes (fun sweep -> sweep.Print)
            row "Lex" lexTime lexBytes
            row "Parse excluding lex" parseOnly parseBytes
            row "Build document" buildTime buildBytes
            row "Print" printTime printBytes
            printfn "| %-17s | %5.1f | %4.1f%% | %7s |" "Total" total (share total) "-"
            printfn ""
            printfn "Work counters, totalled over the last sweep:"
            printfn ""
            printfn "  document elements       %d" elements
            printfn "  document groups         %d" groups
            printfn "  Fits calls              %d" fitCalls
            printfn "  Fits element visits     %d" fitWork
            printfn "  shared preparation      %d" preparation
            printfn "  head trivia records     %d" triviaRecords
            printfn "  head trivia queries     %d" triviaQueries
            printfn "  head trivia comparisons %d" triviaComparisons
            printfn "  lambda body visits      %d" lambdaVisits

            if not (isNull options.Json) then
                let text = StringBuilder()

                let add (format: string) (value: obj) =
                    text.AppendLine(String.Format(CultureInfo.InvariantCulture, format, value))
                    |> ignore

                text.AppendLine "{" |> ignore
                add "  \"root\": {0}," (JsonSerializer.Serialize options.Root :> obj)
                add "  \"discovered\": {0}," (discovered.Count :> obj)
                add "  \"measured\": {0}," (measured.Count :> obj)
                add "  \"characters\": {0}," (characters :> obj)
                add "  \"conditional\": {0}," (conditional :> obj)
                add "  \"conditioned\": {0}," (conditioned :> obj)
                add "  \"pathDependent\": {0}," (pathDependent :> obj)
                add "  \"incomplete\": {0}," (incomplete :> obj)
                add "  \"failed\": {0}," (failed :> obj)
                add "  \"sweeps\": {0}," (options.Sweeps :> obj)
                add "  \"warmups\": {0}," (options.Warmups :> obj)
                add "  \"width\": {0}," (options.Width :> obj)
                add "  \"lexMs\": {0:F3}," (lexTime :> obj)
                add "  \"parseExcludingLexMs\": {0:F3}," (parseOnly :> obj)
                add "  \"buildMs\": {0:F3}," (buildTime :> obj)
                add "  \"printMs\": {0:F3}," (printTime :> obj)
                add "  \"lexBytes\": {0:F0}," (lexBytes :> obj)
                add "  \"parseExcludingLexBytes\": {0:F0}," (parseBytes :> obj)
                add "  \"buildBytes\": {0:F0}," (buildBytes :> obj)
                add "  \"printBytes\": {0:F0}," (printBytes :> obj)
                add "  \"elements\": {0}," (elements :> obj)
                add "  \"groups\": {0}," (groups :> obj)
                add "  \"fitCalls\": {0}," (fitCalls :> obj)
                add "  \"fitWork\": {0}," (fitWork :> obj)
                add "  \"sharedPreparation\": {0}," (preparation :> obj)
                add "  \"headTriviaRecords\": {0}," (triviaRecords :> obj)
                add "  \"headTriviaQueries\": {0}," (triviaQueries :> obj)
                add "  \"headTriviaComparisons\": {0}," (triviaComparisons :> obj)
                add "  \"lambdaBodyVisits\": {0}" (lambdaVisits :> obj)
                text.AppendLine "}" |> ignore
                File.WriteAllText(options.Json, text.ToString())
                printfn ""
                printfn "Wrote %s" options.Json

            0

let run (argv: string array) =
    let mutable code = 1

    let thread = Thread(ThreadStart(fun () -> code <- measure argv), Worker.StackSize)

    thread.IsBackground <- true
    thread.Start()
    thread.Join()
    code
