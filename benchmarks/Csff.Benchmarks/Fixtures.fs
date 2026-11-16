module Csff.Benchmarks.Fixtures

open System
open System.IO
open System.Text

type private Marker = class end

let names =
    [|
        "Typical"
        "Large"
        "Directives"
        "Interpolation"
        "Trivia"
        "NestedLambdas"
    |]

let private embedded (name: string) =
    let assembly = typeof<Marker>.Assembly
    use stream = assembly.GetManifestResourceStream("Fixtures." + name + ".cs")

    if isNull stream then
        invalidArg (nameof name) ("No embedded fixture " + name + ".")

    use reader = new StreamReader(stream, Encoding.UTF8)
    reader.ReadToEnd().Replace("\r\n", "\n")

let private largeCopies = 40

let private large () =
    let typical = embedded "Typical"
    let body = typical.IndexOf("namespace ", StringComparison.Ordinal)
    let text = StringBuilder(typical.Length * largeCopies)
    text.Append(typical, 0, body) |> ignore

    for copy in 0 .. largeCopies - 1 do
        text
            .Append(
                typical
                    .Substring(body)
                    .Replace("namespace Sample.Orders", "namespace Sample.Orders" + string copy)
            )
            .Append('\n')
        |> ignore

    text.ToString()

let nestedLambdas (depth: int) =
    let text = StringBuilder()

    text.Append(
        "namespace Sample.Nested\n{\n    public static class Chain\n    {\n        \
private static int Apply(int value, System.Func<int, int> next) => next(value);\n\n        \
public static System.Func<int, int> Build() => x0 => "
    )
    |> ignore

    for level in 0 .. depth - 1 do
        let parameter = "x" + string level
        let next = "x" + string (level + 1)

        if level % 2 = 0 then
            text.Append("Apply(" + parameter + ", " + next + " => ") |> ignore
        else
            text.Append("{ return Apply(" + parameter + ", " + next + " => ") |> ignore

    text.Append("x" + string depth + " + 1") |> ignore

    for level in depth - 1 .. -1 .. 0 do
        if level % 2 = 0 then
            text.Append(")") |> ignore
        else
            text.Append("); }") |> ignore

    text.Append(";\n    }\n}\n").ToString()

let load (name: string) =
    match name with
    | "Large" -> large ()
    | "NestedLambdas" -> nestedLambdas 8
    | _ -> embedded name
