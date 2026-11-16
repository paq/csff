module Csff.Tests.JsonText

open System.Text

let quote (text: string) =
    let builder = StringBuilder()
    builder.Append '"' |> ignore

    for ch in text do
        match ch with
        | '"' -> builder.Append "\\\"" |> ignore
        | '\\' -> builder.Append "\\\\" |> ignore
        | '\n' -> builder.Append "\\n" |> ignore
        | '\r' -> builder.Append "\\r" |> ignore
        | '\t' -> builder.Append "\\t" |> ignore
        | c when c < ' ' -> builder.Append("\\u").Append((int c).ToString "x4") |> ignore
        | c -> builder.Append c |> ignore

    builder.Append('"').ToString()
