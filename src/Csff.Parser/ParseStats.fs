namespace Csff.Parser

open System
open System.Diagnostics
open System.Threading

module ParseStats =
    let enabled = Environment.GetEnvironmentVariable "CSFF_PARSE_STATS" = "1"

    let elapsed = Array.zeroCreate<int64> 12

    let allocated = Array.zeroCreate<int64> 12

    let counts = Array.zeroCreate<int64> 20

    let tParse = 0
    let tPrepare = 1
    let tDeclarations = 2
    let tProbe = 3

    let nParses = 0
    let nInputTokens = 1
    let nNodesKept = 2
    let nChildrenKept = 3
    let nTokensKept = 4
    let nArenaEntriesKept = 5
    let nArenaListsKept = 6
    let nNodesDropped = 7
    let nChildrenDropped = 8
    let nTokensDropped = 9
    let nArenaEntriesDropped = 10
    let nArenaListsDropped = 11
    let nProbes = 12
    let nExpressionMemoHits = 13
    let nExpressionMemoMisses = 14
    let nScanTypes = 15
    let nLambdaCursors = 16
    let nTypeScans = 17
    let nLambdaHeadScans = 18

    let private names =
        [| "parse, total"
           "  token preparation"
           "  declarations walk"
           "  speculation (outermost Probe)" |]

    let private eventNames =
        [| "parses"
           "input tokens"
           "nodes kept"
           "children kept"
           "tokens kept"
           "arena entries kept"
           "arena lists kept"
           "nodes dropped by speculation"
           "children dropped by speculation"
           "tokens dropped by speculation"
           "arena entries dropped"
           "arena lists dropped"
           "Probe calls"
           "expression memo hits"
           "expression memo misses"
           "type scans"
           "lambda cursor scans"
           "scanCore calls"
           "  of which lambda return-type heads" |]

    let inline enter () =
        if enabled then
            struct (Stopwatch.GetTimestamp(), GC.GetAllocatedBytesForCurrentThread())
        else
            struct (0L, 0L)

    let inline lapse (region: int) (start: struct (int64 * int64)) =
        if enabled then
            let struct (ticks, bytes) = start
            Interlocked.Add(&elapsed[region], Stopwatch.GetTimestamp() - ticks) |> ignore

            Interlocked.Add(&allocated[region], GC.GetAllocatedBytesForCurrentThread() - bytes)
            |> ignore

    let inline event (kind: int) =
        if enabled then
            Interlocked.Increment(&counts[kind]) |> ignore

    let inline bump (kind: int) (by: int) =
        if enabled then
            Interlocked.Add(&counts[kind], int64 by) |> ignore

    let private report () =
        let frequency = float Stopwatch.Frequency
        let out = Console.Error
        out.WriteLine "parse-stats regions (seconds, megabytes allocated)"

        for index in 0 .. names.Length - 1 do
            out.WriteLine(
                String.Format(
                    "parse-stats region {0,-32} {1,8:F4} {2,10:F1}",
                    names[index],
                    float elapsed[index] / frequency,
                    float allocated[index] / 1048576.0
                )
            )

        for index in 0 .. eventNames.Length - 1 do
            out.WriteLine(
                String.Format("parse-stats count {0,-34} {1}", eventNames[index], counts[index])
            )

    do
        if enabled then
            AppDomain.CurrentDomain.ProcessExit.Add(fun _ -> report ())
