namespace Csff.Gate

open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.Diagnostics
open System.IO
open System.Text
open System.Threading
open System.Threading.Tasks

type Decoding =
    | Utf8Bom
    | Utf32Le
    | Utf32Be
    | Utf16Le
    | Utf16Be
    | Utf8
    | Bytewise

module Program =

    let private usage =
        """Usage: Csff.Gate --before DIR --after DIR [options]
       Csff.Gate --pair BEFORE.cs AFTER.cs
  --label NAME        Name this run in the report header
  --jobs N            Maximum parallel workers (default: processor count)
  --symbol-budget N   Additional preprocessor configurations per file (default: 8)
  --report FILE       Write every finding, with detail, to FILE
  --pins FILE         Compare the finding set with this pinned one and fail on any
                      difference; without it, any finding fails the run"""

    let private strictUtf8 = UTF8Encoding(false, true)
    let private utf32Le = UTF32Encoding(false, true, true)
    let private utf32Be = UTF32Encoding(true, true, true)
    let private utf16Le = UnicodeEncoding(false, true, true)
    let private utf16Be = UnicodeEncoding(true, true, true)

    let private windows1252Upper =
        "€\u0081‚ƒ„…†‡ˆ‰Š‹Œ\u008DŽ\u008F\u0090‘’“”•–—˜™š›œ\u009DžŸ"

    let private decodeWindows1252 (bytes: byte array) =
        String.Create(
            bytes.Length,
            bytes,
            Buffers.SpanAction<char, byte array>(fun chars src ->
                for index = 0 to src.Length - 1 do
                    let value = src[index]

                    chars[index] <-
                        if value >= 0x80uy && value < 0xA0uy then
                            windows1252Upper[int value - 0x80]
                        else
                            char value)
        )

    let internal decode (bytes: byte array) =
        if
            bytes.Length >= 4
            && bytes[0] = 0xFFuy
            && bytes[1] = 0xFEuy
            && bytes[2] = 0x00uy
            && bytes[3] = 0x00uy
        then
            struct (Utf32Le, utf32Le.GetString(bytes, 4, bytes.Length - 4))
        elif
            bytes.Length >= 4
            && bytes[0] = 0x00uy
            && bytes[1] = 0x00uy
            && bytes[2] = 0xFEuy
            && bytes[3] = 0xFFuy
        then
            struct (Utf32Be, utf32Be.GetString(bytes, 4, bytes.Length - 4))
        elif bytes.Length >= 3 && bytes[0] = 0xEFuy && bytes[1] = 0xBBuy && bytes[2] = 0xBFuy then
            struct (Utf8Bom, strictUtf8.GetString(bytes, 3, bytes.Length - 3))
        elif bytes.Length >= 2 && bytes[0] = 0xFFuy && bytes[1] = 0xFEuy then
            struct (Utf16Le, utf16Le.GetString(bytes, 2, bytes.Length - 2))
        elif bytes.Length >= 2 && bytes[0] = 0xFEuy && bytes[1] = 0xFFuy then
            struct (Utf16Be, utf16Be.GetString(bytes, 2, bytes.Length - 2))
        else
            try
                struct (Utf8, strictUtf8.GetString bytes)
            with :? DecoderFallbackException ->
                struct (Bytewise, decodeWindows1252 bytes)

    let internal comparePair
        (beforeBytes: byte array)
        (afterBytes: byte array)
        (symbolBudget: int)
        =
        let struct (beforeMode, beforeText) = decode beforeBytes
        let struct (afterMode, afterText) = decode afterBytes

        if beforeMode <> afterMode then
            1, [ String.Format("encoding {0} vs {1}", beforeMode, afterMode) ]
        else
            let outcome = Adjudicator.adjudicate beforeText afterText symbolBudget
            let lines = ResizeArray<string>()

            lines.Add(
                String.Format(
                    "configurations={0} capped={1} source-already-invalid={2}",
                    outcome.Configurations,
                    outcome.SymbolsCapped,
                    outcome.SourceHadErrors
                )
            )

            for finding in outcome.Findings do
                lines.Add(
                    String.Format(
                        "{0}\t{1}\t{2}",
                        finding.Category.Name,
                        finding.Configuration,
                        finding.Detail
                    )
                )

            if List.isEmpty outcome.Findings then
                lines.Add "equivalent"
                0, List.ofSeq lines
            else
                1, List.ofSeq lines

    module private Count =
        let Unchanged = 0
        let Missing = 1
        let Adjudicated = 2
        let Configurations = 3
        let Capped = 4
        let EncodingChanged = 5
        let Prior = 6
        let Clean = 7
        let Crashed = 8
        let Slots = 9

    let private ordinal (left: string) (right: string) = String.CompareOrdinal(left, right)

    [<EntryPoint>]
    let main argv =
        let mutable before = ""
        let mutable after = ""
        let mutable label = "corpus"
        let mutable jobs = Environment.ProcessorCount
        let mutable budget = 8
        let mutable report = ""
        let mutable pins = ""
        let mutable pairBefore = ""
        let mutable pairAfter = ""
        let mutable bad = false
        let mutable index = 0

        let next name =
            index <- index + 1

            if index >= argv.Length then
                failwith (name + " requires a value.")

            argv[index]

        while index < argv.Length && not bad do
            match argv[index] with
            | "--before" -> before <- next "--before"
            | "--after" -> after <- next "--after"
            | "--label" -> label <- next "--label"
            | "--jobs" -> jobs <- Int32.Parse(next "--jobs")
            | "--symbol-budget" -> budget <- Int32.Parse(next "--symbol-budget")
            | "--report" -> report <- next "--report"
            | "--pins" -> pins <- next "--pins"
            | "--pair" ->
                pairBefore <- next "--pair"
                pairAfter <- next "--pair"
            | other ->
                Console.Error.WriteLine("Csff.Gate: unknown option " + other)
                bad <- true

            index <- index + 1

        if bad then
            Console.Error.WriteLine usage
            2
        elif pairBefore <> "" then
            let exitCode, lines =
                comparePair (File.ReadAllBytes pairBefore) (File.ReadAllBytes pairAfter) budget

            for line in lines do
                Console.Out.WriteLine line

            exitCode
        elif before = "" || after = "" then
            Console.Error.WriteLine usage
            2
        else

            let timer = Stopwatch.StartNew()
            let root = Path.GetFullPath before
            let output = Path.GetFullPath after

            let files =
                Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories)
                |> Seq.map (fun path -> Path.GetRelativePath(root, path))
                |> Seq.sortWith ordinal
                |> Seq.toArray

            let lines = ConcurrentBag<string>()
            let keys = ConcurrentBag<string>()
            let counts = Array.zeroCreate<int> Count.Slots

            let record (relative: string) (category: string) (detail: string) =
                lines.Add(String.Join('\t', relative, category, "-", "-", detail))
                keys.Add(relative + "\t" + category)

            let adjudicateOne (relative: string) =
                let sourceBytes = File.ReadAllBytes(Path.Combine(root, relative))
                let outputPath = Path.Combine(output, relative)

                if not (File.Exists outputPath) then
                    Interlocked.Increment(&counts[Count.Missing]) |> ignore
                    record relative "missing" "no output"
                else
                    let outputBytes = File.ReadAllBytes outputPath

                    if sourceBytes.AsSpan().SequenceEqual(ReadOnlySpan<byte>(outputBytes)) then
                        Interlocked.Increment(&counts[Count.Unchanged]) |> ignore
                    else
                        let struct (sourceMode, sourceText) = decode sourceBytes
                        let struct (outputMode, outputText) = decode outputBytes

                        if sourceMode <> outputMode then
                            Interlocked.Increment(&counts[Count.EncodingChanged]) |> ignore

                            record
                                relative
                                "encoding"
                                (String.Format("{0} vs {1}", sourceMode, outputMode))
                        else
                            let outcome = Adjudicator.adjudicate sourceText outputText budget
                            Interlocked.Increment(&counts[Count.Adjudicated]) |> ignore

                            Interlocked.Add(&counts[Count.Configurations], outcome.Configurations)
                            |> ignore

                            if outcome.SymbolsCapped then
                                Interlocked.Increment(&counts[Count.Capped]) |> ignore

                            if not (List.isEmpty outcome.Findings) then
                                if outcome.SourceHadErrors then
                                    Interlocked.Increment(&counts[Count.Prior]) |> ignore
                                else
                                    Interlocked.Increment(&counts[Count.Clean]) |> ignore

                            for finding in outcome.Findings do
                                lines.Add(
                                    String.Join(
                                        '\t',
                                        relative,
                                        finding.Category.Name,
                                        finding.Configuration,
                                        (if outcome.SourceHadErrors then
                                             "source-already-invalid"
                                         else
                                             "source-valid"),
                                        finding.Detail
                                    )
                                )

                                keys.Add(relative + "\t" + finding.Category.Name)

            let options = ParallelOptions(MaxDegreeOfParallelism = jobs)

            Parallel.ForEach(
                files,
                options,
                fun (relative: string) ->
                    try
                        adjudicateOne relative
                    with error ->
                        Interlocked.Increment(&counts[Count.Crashed]) |> ignore

                        record
                            relative
                            "adjudicator-error"
                            (error.GetType().Name + ": " + error.Message)
            )
            |> ignore

            let ordered = lines |> Seq.sortWith ordinal |> Seq.toArray
            let found = keys |> Seq.sortWith ordinal |> Seq.distinct |> Seq.toArray

            if report <> "" then
                File.WriteAllLines(report, ordered)

            Console.Out.WriteLine(
                String.Format(
                    "gate {0}: files={1} unchanged={2} adjudicated={3} missing-output={4} encoding-changed={5}",
                    label,
                    files.Length,
                    counts[Count.Unchanged],
                    counts[Count.Adjudicated],
                    counts[Count.Missing],
                    counts[Count.EncodingChanged]
                )
            )

            Console.Out.WriteLine(
                String.Format(
                    "  preprocessor configurations compared={0} symbol-budget-capped-files={1} adjudicator-errors={2}",
                    counts[Count.Configurations],
                    counts[Count.Capped],
                    counts[Count.Crashed]
                )
            )

            Console.Out.WriteLine(
                String.Format(
                    "  disagreeing files: source-valid={0} source-already-invalid={1} in {2:F0}s",
                    counts[Count.Clean],
                    counts[Count.Prior],
                    timer.Elapsed.TotalSeconds
                )
            )

            for line in ordered do
                Console.Out.WriteLine("  " + line)

            let expected =
                if pins <> "" && File.Exists pins then
                    File.ReadAllLines pins
                    |> Array.filter (fun line -> line.Trim() <> "" && not (line.StartsWith '#'))
                else
                    [||]

            let pinned = HashSet<string>(expected, StringComparer.Ordinal)
            let actual = HashSet<string>(found, StringComparer.Ordinal)
            let unpinned = found |> Array.filter (pinned.Contains >> not)
            let stale = expected |> Array.filter (actual.Contains >> not) |> Array.distinct

            for key in unpinned do
                Console.Error.WriteLine("gate: unpinned disagreement: " + key)

            for key in stale do
                Console.Error.WriteLine("gate: pinned disagreement no longer found: " + key)

            if unpinned.Length > 0 || stale.Length > 0 then 1 else 0
