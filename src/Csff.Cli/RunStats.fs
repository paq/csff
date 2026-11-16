namespace Csff.Cli

open System
open System.Diagnostics
open System.Threading

type internal RunStatsThread =
    [<ThreadStatic; DefaultValue>]
    static val mutable private decodeBytes: int64

    static member DecodeBytes
        with get () = RunStatsThread.decodeBytes
        and set (value: int64) = RunStatsThread.decodeBytes <- value

module internal RunStats =
    let enabled = Environment.GetEnvironmentVariable "CSFF_RUN_STATS" = "1"

    let digestPath = Environment.GetEnvironmentVariable "CSFF_OUTPUT_DIGEST"
    let digestEnabled = not (String.IsNullOrEmpty digestPath)
    let mutable digests: string array = null

    let prepareDigests (count: int) =
        if digestEnabled then
            digests <- Array.zeroCreate count

    let noteDigest (index: int) (bytes: ReadOnlySpan<byte>) =
        if digestEnabled && not (isNull digests) && index < digests.Length then
            let hash = Security.Cryptography.SHA256.HashData bytes
            digests[index] <- Convert.ToHexString hash

    let elapsed = Array.zeroCreate<int64> 16
    let allocated = Array.zeroCreate<int64> 16
    let entries = Array.zeroCreate<int64> 16
    let allocating = Array.zeroCreate<int64> 16

    let tFile = 0
    let tRead = 1
    let tDecode = 2
    let tLex = 3
    let tParse = 4
    let tComplete = 5
    let tPrint = 6
    let tCompare = 7
    let tVerify = 8
    let tCommit = 9
    let tTake = 10
    let tLargeGate = 11

    let counts = Array.zeroCreate<int64> 8
    let cAdopted = 0
    let cSelfRead = 1
    let cOlderOccupant = 2
    let cReaderClaimed = 3
    let cReaderSkipped = 4
    let cReaderFailed = 5
    let cReaderPositions = 6
    let cLargeDeferred = 7

    let private countNames =
        [|
            "prefetched files adopted"
            "files the worker read itself"
            "take spins on an older occupant"
            "reader claims"
            "reader skips (worker took it)"
            "reader thread failures"
            "reader positions visited"
            "large files deferred (gate full)"
        |]

    let inline count (kind: int) =
        if enabled then
            Interlocked.Increment(&counts[kind]) |> ignore

    let names =
        [|
            "file, total (FormatInto)"
            "  read"
            "  decode"
            "  lex"
            "  parse"
            "  complete-parse check"
            "  build document + print"
            "  compare with source"
            "  verify"
            "  commit / result"
            "prefetch take (outside file)"
            "large-file gate wait, blocking"
        |]

    let bounds =
        [|
            0L
            64L
            1024L
            16L * 1024L
            256L * 1024L
            1024L * 1024L
            16L * 1024L * 1024L
            Int64.MaxValue
        |]

    let histogram = Array.zeroCreate<int64> 8
    let histogramBytes = Array.zeroCreate<int64> 8
    let histogramNoSource = Array.zeroCreate<int64> 8
    let histogramNoSourceBytes = Array.zeroCreate<int64> 8

    let inline enter () =
        if enabled then
            struct (Stopwatch.GetTimestamp(), GC.GetAllocatedBytesForCurrentThread())
        else
            struct (0L, 0L)

    let inline lapse (region: int) (start: struct (int64 * int64)) =
        if enabled then
            let struct (ticks, bytes) = start
            Interlocked.Add(&elapsed[region], Stopwatch.GetTimestamp() - ticks) |> ignore
            let delta = GC.GetAllocatedBytesForCurrentThread() - bytes
            Interlocked.Add(&allocated[region], delta) |> ignore
            Interlocked.Increment(&entries[region]) |> ignore

            if delta > 0L then
                Interlocked.Increment(&allocating[region]) |> ignore

            if region = tDecode then
                RunStatsThread.DecodeBytes <- delta

    let private bucketOf (delta: int64) =
        let mutable bucket = 0

        while delta > bounds[bucket] do
            bucket <- bucket + 1

        bucket

    let private slowestLock = obj ()
    let private slowestTicks = Array.zeroCreate<int64> 8
    let private slowestPaths = Array.zeroCreate<string> 8

    let private noteSlow (ticks: int64) (path: string) =
        if ticks > Volatile.Read(&slowestTicks[slowestTicks.Length - 1]) then
            lock slowestLock (fun () ->
                let mutable at = slowestTicks.Length - 1

                if ticks > slowestTicks[at] then
                    while at > 0 && ticks > slowestTicks[at - 1] do
                        slowestTicks[at] <- slowestTicks[at - 1]
                        slowestPaths[at] <- slowestPaths[at - 1]
                        at <- at - 1

                    slowestTicks[at] <- ticks
                    slowestPaths[at] <- path)

    let mutable private firstFileStart = Int64.MaxValue
    let mutable private lastFileEnd = 0L

    let private noteSpan (start: int64) (finish: int64) =
        let mutable seen = Volatile.Read(&firstFileStart)

        while start < seen
              && Interlocked.CompareExchange(&firstFileStart, start, seen) <> seen do
            seen <- Volatile.Read(&firstFileStart)

        let mutable last = Volatile.Read(&lastFileEnd)

        while finish > last && Interlocked.CompareExchange(&lastFileEnd, finish, last) <> last do
            last <- Volatile.Read(&lastFileEnd)

    let fileDone (start: struct (int64 * int64)) (path: string) =
        if enabled then
            let struct (ticks, bytes) = start
            let delta = GC.GetAllocatedBytesForCurrentThread() - bytes
            let finish = Stopwatch.GetTimestamp()
            let took = finish - ticks
            noteSpan ticks finish
            noteSlow took path
            Interlocked.Add(&elapsed[tFile], took) |> ignore
            Interlocked.Add(&allocated[tFile], delta) |> ignore
            Interlocked.Increment(&entries[tFile]) |> ignore

            if delta > 0L then
                Interlocked.Increment(&allocating[tFile]) |> ignore

            let bucket = bucketOf delta
            Interlocked.Increment(&histogram[bucket]) |> ignore
            Interlocked.Add(&histogramBytes[bucket], delta) |> ignore
            let rest = delta - RunStatsThread.DecodeBytes
            RunStatsThread.DecodeBytes <- 0L
            let restBucket = bucketOf rest
            Interlocked.Increment(&histogramNoSource[restBucket]) |> ignore
            Interlocked.Add(&histogramNoSourceBytes[restBucket], rest) |> ignore

    let private markNames = Array.zeroCreate<string> 16
    let private markTicks = Array.zeroCreate<int64> 16
    let private markCpu = Array.zeroCreate<TimeSpan> 16
    let mutable private markCount = 0
    let mutable private mainUtc = DateTime.MinValue

    let mark (name: string) =
        if enabled && markCount < markNames.Length then
            if markCount = 0 then
                mainUtc <- DateTime.UtcNow

            markNames[markCount] <- name
            markTicks[markCount] <- Stopwatch.GetTimestamp()
            markCpu[markCount] <- Environment.CpuUsage.TotalTime
            markCount <- markCount + 1

    let private writeHistogram
        (out: IO.TextWriter)
        (title: string)
        (files: int64 array)
        (bytes: int64 array)
        =
        out.WriteLine("run-stats " + title + " (files, MB)")

        for index in 0 .. bounds.Length - 1 do
            let label =
                if index = 0 then
                    "0 B"
                elif bounds[index] = Int64.MaxValue then
                    "> " + string bounds[index - 1] + " B"
                else
                    "<= " + string bounds[index] + " B"

            out.WriteLine(
                String.Format(
                    "run-stats alloc {0,-16} {1,8} {2,10:F1}",
                    label,
                    files[index],
                    float bytes[index] / 1048576.0
                )
            )

    let report () =
        if enabled then
            let frequency = float Stopwatch.Frequency
            let out = Console.Error

            if markCount > 0 then
                let started = Process.GetCurrentProcess().StartTime.ToUniversalTime()

                out.WriteLine(
                    String.Format(
                        "run-stats timeline {0,-28} {1,9:F1} ms",
                        "process start -> main",
                        (mainUtc - started).TotalMilliseconds
                    )
                )

                if lastFileEnd > 0L && markCount >= 4 then
                    out.WriteLine(
                        String.Format(
                            "run-stats timeline first file starts {0:F1} ms after discovery; last file ends {1:F1} ms before formatting returns",
                            float (firstFileStart - markTicks[2]) * 1000.0 / frequency,
                            float (markTicks[3] - lastFileEnd) * 1000.0 / frequency
                        )
                    )

                for index in 1 .. markCount - 1 do
                    let wall = float (markTicks[index] - markTicks[index - 1]) * 1000.0 / frequency
                    let cpu = (markCpu[index] - markCpu[index - 1]).TotalMilliseconds

                    out.WriteLine(
                        String.Format(
                            "run-stats timeline {0,-28} {1,9:F1} ms, {2,9:F1} ms CPU ({3:F1} cores)",
                            markNames[index],
                            wall,
                            cpu,
                            (if wall > 0.0 then cpu / wall else 0.0)
                        )
                    )

            out.WriteLine
                "run-stats regions (seconds summed over workers, MB allocated, entries, entries that allocated)"

            for index in 0 .. names.Length - 1 do
                out.WriteLine(
                    String.Format(
                        "run-stats region {0,-28} {1,9:F4} {2,10:F1} {3,8} {4,8}",
                        names[index],
                        float elapsed[index] / frequency,
                        float allocated[index] / 1048576.0,
                        entries[index],
                        allocating[index]
                    )
                )

            for index in 0 .. countNames.Length - 1 do
                out.WriteLine(
                    String.Format("run-stats count {0,-34} {1}", countNames[index], counts[index])
                )

            for index in 0 .. slowestTicks.Length - 1 do
                if not (isNull slowestPaths[index]) then
                    out.WriteLine(
                        String.Format(
                            "run-stats slowest {0,9:F1} ms {1}",
                            float slowestTicks[index] * 1000.0 / frequency,
                            slowestPaths[index]
                        )
                    )

            writeHistogram out "per-file allocation histogram" histogram histogramBytes

            writeHistogram
                out
                "per-file allocation histogram without the decoded source"
                histogramNoSource
                histogramNoSourceBytes

            out.WriteLine(
                String.Format(
                    "run-stats gc collections gen0={0} gen1={1} gen2={2} pause={3:F1}ms allocated={4:F1}MB latency={5}",
                    GC.CollectionCount 0,
                    GC.CollectionCount 1,
                    GC.CollectionCount 2,
                    GC.GetTotalPauseDuration().TotalMilliseconds,
                    float (GC.GetTotalAllocatedBytes false) / 1048576.0,
                    Runtime.GCSettings.LatencyMode
                )
            )
