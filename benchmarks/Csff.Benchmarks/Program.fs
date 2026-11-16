module Csff.Benchmarks.Program

open BenchmarkDotNet.Running

[<EntryPoint>]
let main argv =
    if argv.Length > 0 && argv[0] = "--gate" then
        Gate.run argv[1..]
    else
        BenchmarkSwitcher.FromAssembly(typeof<Stages>.Assembly).Run argv |> ignore
        0
