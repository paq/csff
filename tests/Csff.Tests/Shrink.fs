module Csff.Tests.Shrink

open System
open System.Diagnostics
open System.IO
open System.Text

let usage =
    String.concat
        "\n"
        [
            "usage: --shrink <reference command> <candidate command> <file> [options]"
            ""
            "  --out <path>   write the reduced file here as well as to standard output"
            "  --rounds N     greedy passes to make (default 2)"
            ""
            "Each command is given the path of a temporary file as its last argument and"
            "must print its formatting of that file to standard output. For csff that is"
            "\"out/csff/bin/Csff.Cli --write-stdout\". A command is split on spaces, so"
            "neither it nor its arguments may contain one."
        ]

let private formatted (command: string) (path: string) =
    let parts = command.Split(' ', StringSplitOptions.RemoveEmptyEntries)
    let start = ProcessStartInfo(parts[0])

    for index in 1 .. parts.Length - 1 do
        start.ArgumentList.Add parts[index]

    start.ArgumentList.Add path

    try
        match Subprocess.run start with
        | Subprocess.Exited(0, output, _) -> Ok output
        | Subprocess.Exited(code, _, errors) -> Error $"{parts[0]} exited {code}: {errors.Trim()}"
        | Subprocess.Timeout _ -> Error $"{parts[0]} did not finish within {Subprocess.limit} ms"
    with error ->
        Error $"{parts[0]} could not be started: {error.Message}"

let private readBytes (path: string) =
    Encoding.Latin1.GetString(File.ReadAllBytes path)

let private writeBytes (path: string) (text: string) =
    File.WriteAllBytes(path, Encoding.Latin1.GetBytes text)

let markedEncoding (bytes: string) =
    let starts (mark: string) =
        bytes.StartsWith(mark, StringComparison.Ordinal)

    if starts "\u00ff\u00fe\u0000\u0000" then Some "UTF-32LE"
    elif starts "\u0000\u0000\u00fe\u00ff" then Some "UTF-32BE"
    elif starts "\u00ff\u00fe" then Some "UTF-16LE"
    elif starts "\u00fe\u00ff" then Some "UTF-16BE"
    else None

let display (bytes: string) =
    try
        UTF8Encoding(false, true).GetString(Encoding.Latin1.GetBytes bytes)
    with :? DecoderFallbackException ->
        bytes

let linesOf (text: string) = text.Split '\n'

let private disagree
    (reference: string)
    (candidate: string)
    (scratch: string)
    (lines: string array)
    =
    writeBytes scratch (String.Join('\n', lines))

    match formatted reference scratch, formatted candidate scratch with
    | Ok first, Ok second -> first <> second
    | _ -> false

let reduce (differs: string array -> bool) (lines: string array) =
    let mutable kept = lines
    let mutable chunk = max 1 (kept.Length / 2)

    while chunk >= 1 do
        let mutable index = 0

        while index < kept.Length do
            let trial = Array.append kept[.. index - 1] kept[index + chunk ..]

            if trial.Length > 0 && differs trial then
                kept <- trial
            else
                index <- index + chunk

        chunk <- chunk / 2

    kept

let private shrink (argv: string array) =
    if argv.Length < 3 then
        Console.Error.WriteLine usage
        2
    else

        let reference = argv[0]
        let candidate = argv[1]
        let path = argv[2]
        let mutable out = null
        let mutable rounds = 2
        let mutable index = 3
        let mutable bad = false

        while index < argv.Length && not bad do
            match
                argv[index],
                (if index + 1 < argv.Length then
                     Some argv[index + 1]
                 else
                     None)
            with
            | "--out", Some value ->
                out <- value
                index <- index + 2
            | "--rounds", Some value when Int32.TryParse(value, &rounds) -> index <- index + 2
            | other, _ ->
                Console.Error.WriteLine $"unrecognised option {other}"
                Console.Error.WriteLine usage
                bad <- true

        if bad then
            2
        elif not (File.Exists path) then
            Console.Error.WriteLine $"no file at {path}"
            2
        else
            let beside = Path.GetDirectoryName(Path.GetFullPath path)
            let nest = Path.Combine(beside, $"csff-shrink-{Guid.NewGuid():N}")
            let scratch = Path.Combine(nest, Path.GetFileName path)

            try
                Directory.CreateDirectory nest |> ignore
                let bytes = readBytes path
                let original = linesOf bytes
                writeBytes scratch (String.Join('\n', original))

                let first = formatted reference scratch
                let second = formatted candidate scratch

                match markedEncoding bytes, first, second with
                | Some name, _, _ ->
                    Console.Error.WriteLine $"{path} is {name}, whose newline is more than one byte"

                    Console.Error.WriteLine
                        "the reduction splits bytes at the newline, so it would corrupt this file"

                    2
                | _, Error reason, _
                | _, _, Error reason ->
                    Console.Error.WriteLine reason
                    Console.Error.WriteLine $"a command failed on {path}"

                    Console.Error.WriteLine
                        "nothing was reduced, and nothing is claimed about the two"

                    2
                | None, Ok _, Ok _ ->

                    let differs = disagree reference candidate scratch

                    if not (differs original) then
                        Console.Error.WriteLine "the two commands agree about this file already"
                        1
                    else

                        let mutable kept = original

                        for _ in 1 .. max 1 rounds do
                            kept <- reduce differs kept

                        printfn "%d lines, from %d" kept.Length original.Length
                        printfn "%s" (String.replicate 60 "-")
                        printfn "%s" (display (String.Join('\n', kept)))
                        printfn "%s" (String.replicate 60 "-")

                        writeBytes scratch (String.Join('\n', kept))

                        let status =
                            match formatted reference scratch, formatted candidate scratch with
                            | Ok before, Ok after ->
                                printfn "reference"
                                printfn "%s" before
                                printfn "candidate"
                                printfn "%s" after
                                0
                            | Error reason, _
                            | _, Error reason ->
                                Console.Error.WriteLine reason
                                Console.Error.WriteLine "a command failed on the reduced file"
                                2

                        if not (isNull out) then
                            writeBytes out (String.Join('\n', kept))
                            printfn "wrote %s" out

                        status
            finally
                if Directory.Exists nest then
                    Directory.Delete(nest, true)

let run (argv: string array) = shrink argv
