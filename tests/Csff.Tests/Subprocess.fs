module Csff.Tests.Subprocess

open System.Diagnostics
open System.Threading.Tasks

let limit = 10000

type Outcome =
    | Exited of code: int * output: string * errors: string

    | Timeout of output: string * errors: string

let private captured (task: Task<string>) =
    if task.Wait limit then task.Result else ""

let runWith (bound: int) (start: ProcessStartInfo) =
    start.UseShellExecute <- false
    start.RedirectStandardOutput <- true
    start.RedirectStandardError <- true

    use child = new Process(StartInfo = start)
    child.Start() |> ignore
    let output = child.StandardOutput.ReadToEndAsync()
    let errors = child.StandardError.ReadToEndAsync()

    if child.WaitForExit bound then
        Exited(child.ExitCode, captured output, captured errors)
    else
        child.Kill true
        Timeout(captured output, captured errors)

let run (start: ProcessStartInfo) = runWith limit start
