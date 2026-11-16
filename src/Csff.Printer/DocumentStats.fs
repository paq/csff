namespace Csff.Printer

open System
open System.Diagnostics
open System.Threading

module DocumentStats =
    let enabled = Environment.GetEnvironmentVariable "CSFF_DOC_STATS" = "1"

    let private elapsed = Array.zeroCreate<int64> 12

    let private allocated = Array.zeroCreate<int64> 12

    let private counts = Array.zeroCreate<int64> 12

    let tBuild = 0
    let tDiscovery = 1
    let tWalk = 2
    let tPassWalk = 3
    let tPassParse = 4
    let tPassRender = 5
    let tOwnership = 6
    let tDirectives = 7

    let nFiles = 0
    let nConditionalFiles = 1
    let nWalks = 2
    let nNodes = 3
    let nTriviaRuns = 4
    let nTriviaEntered = 5
    let nElements = 6
    let nTextElements = 7

    let private names =
        [| "document build, total"
           "  symbol-set discovery"
           "  node walk, first pass"
           "  node walk, later passes"
           "  reparse, later passes"
           "  render, later passes"
           "  literal ownership"
           "  directive index" |]

    let private eventNames =
        [| "files built"
           "files with conditional regions"
           "node walks"
           "nodes printed"
           "trivia runs offered"
           "trivia runs entered"
           "document elements emitted"
           "  of which source text" |]

    let inline enter () =
        if enabled then
            struct (Stopwatch.GetTimestamp(), GC.GetAllocatedBytesForCurrentThread())
        else
            struct (0L, 0L)

    let lapse (region: int) (start: struct (int64 * int64)) =
        if enabled then
            let struct (ticks, bytes) = start
            Interlocked.Add(&elapsed[region], Stopwatch.GetTimestamp() - ticks) |> ignore

            Interlocked.Add(&allocated[region], GC.GetAllocatedBytesForCurrentThread() - bytes)
            |> ignore

    let event (kind: int) =
        if enabled then
            Interlocked.Increment(&counts[kind]) |> ignore

    let bump (kind: int) (by: int) =
        if enabled then
            Interlocked.Add(&counts[kind], int64 by) |> ignore

    let private report () =
        let frequency = float Stopwatch.Frequency
        let out = Console.Error
        out.WriteLine "doc-stats regions (seconds, megabytes allocated)"

        for index in 0 .. names.Length - 1 do
            out.WriteLine(
                String.Format(
                    "doc-stats region {0,-28} {1,8:F4} {2,10:F1}",
                    names[index],
                    float elapsed[index] / frequency,
                    float allocated[index] / 1048576.0
                )
            )

        for index in 0 .. eventNames.Length - 1 do
            out.WriteLine(
                String.Format("doc-stats count {0,-32} {1}", eventNames[index], counts[index])
            )

    do
        if enabled then
            AppDomain.CurrentDomain.ProcessExit.Add(fun _ -> report ())
