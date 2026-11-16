module Csff.Benchmarks.Gate

open System
open System.Collections.Generic
open System.Diagnostics
open System.IO
open System.Reflection
open System.Text.Json
open System.Text.Json.Nodes

[<NoEquality; NoComparison>]
type private Case =
    {
        Name: string
        Source: unit -> string
        Stage: Stage
    }

let private stages = [| Lex; Parse; Build; Print; Verify; Format |]

let private cases =
    [|
        for fixture in Fixtures.names do
            for stage in stages do
                {
                    Name = $"Stages/{fixture}/{stage}"
                    Source = fun () -> Fixtures.load fixture
                    Stage = stage
                }
        for depth in [ 4; 8; 16; 32 ] do
            {
                Name = $"NestedLambdas/{depth}/Format"
                Source = fun () -> Fixtures.nestedLambdas depth
                Stage = Format
            }
    |]

let private slackBytes = 128L

let private tolerance = 0.02

let private measure (case: Case) =
    use pipeline = new Pipeline(case.Source())
    pipeline.Prepare case.Stage
    let watch = Stopwatch.StartNew()
    let mutable warmups = 0

    while warmups < 50 || watch.ElapsedMilliseconds < 500L do
        pipeline.Run case.Stage |> ignore
        warmups <- warmups + 1

    let runs = 16
    let mutable least = Int64.MaxValue

    for _ in 1..5 do
        let before = GC.GetAllocatedBytesForCurrentThread()

        for _ in 1..runs do
            pipeline.Run case.Stage |> ignore

        let after = GC.GetAllocatedBytesForCurrentThread()
        least <- min least ((after - before) / int64 runs)

    least

let private defaultBaseline () =
    let directory =
        Assembly.GetExecutingAssembly().GetCustomAttributes<AssemblyMetadataAttribute>()
        |> Seq.tryFind (fun attribute -> attribute.Key = "ProjectDirectory")
        |> Option.map (fun attribute -> attribute.Value)
        |> Option.defaultValue Environment.CurrentDirectory

    Path.Combine(directory, "allocations.json")

let private read (path: string) =
    let baseline = Dictionary<string, int64>(StringComparer.Ordinal)

    if File.Exists path then
        match JsonNode.Parse(File.ReadAllText path) with
        | :? JsonObject as entries ->
            for entry in entries do
                baseline[entry.Key] <- entry.Value.GetValue<int64>()
        | _ -> invalidOp (path + " is not a JSON object.")

    baseline

let private write (path: string) (measured: (string * int64) array) =
    let entries = JsonObject()

    for name, bytes in measured |> Array.sortBy fst do
        entries[name] <- JsonValue.Create bytes

    File.WriteAllText(
        path,
        entries.ToJsonString(JsonSerializerOptions(WriteIndented = true, NewLine = "\n"))
        + "\n"
    )

let private usage =
    "Usage: --gate [--update] [--baseline PATH]\n\
\n\
  Measures bytes allocated per operation for every benchmark case and fails when one\n\
  rises past its baseline by more than both 2% and 128 bytes.\n\
\n\
  --update         rewrite the baseline with the measured figures instead\n\
  --baseline PATH  the baseline file (default: allocations.json beside the project)\n"

let run (argv: string array) =
    let mutable update = false
    let mutable path = null
    let mutable error = null
    let mutable index = 0

    while isNull error && index < argv.Length do
        match argv[index] with
        | "--update" -> update <- true
        | "--baseline" when index + 1 < argv.Length ->
            index <- index + 1
            path <- argv[index]
        | argument -> error <- "Unexpected argument " + argument + "."

        index <- index + 1

    if not (isNull error) then
        eprintfn "%s" error
        eprintfn ""
        eprintf "%s" usage
        2
    else
        let path = if isNull path then defaultBaseline () else path
        let baseline = read path
        let measured = ResizeArray()
        let mutable risen = 0
        let mutable missing = 0

        for case in cases do
            let bytes = measure case
            measured.Add((case.Name, bytes))

            match baseline.TryGetValue case.Name with
            | true, expected ->
                let limit = expected + max slackBytes (int64 (float expected * tolerance))

                let verdict =
                    if bytes > limit then
                        risen <- risen + 1
                        "ROSE"
                    elif bytes + max slackBytes (int64 (float expected * tolerance)) < expected then
                        "fell"
                    else
                        "ok"

                printfn "%-36s %12d B  baseline %12d B  %s" case.Name bytes expected verdict
            | _ ->
                missing <- missing + 1
                printfn "%-36s %12d B  no baseline" case.Name bytes

        if update then
            write path (measured.ToArray())
            printfn "Wrote %s." path
            0
        elif risen > 0 then
            eprintfn "%d case(s) allocate more than their baseline in %s." risen path
            1
        elif missing > 0 then
            eprintfn "%d case(s) have no baseline in %s; run with --update." missing path
            2
        else
            printfn "Every case is within its baseline. A case marked fell can be locked in"
            printfn "with --update."
            0
