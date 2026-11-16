namespace Csff.Conformance

open System.Runtime.CompilerServices
open System.Text.Encodings.Web
open System.Text.Json

[<assembly: InternalsVisibleTo("Csff.Oracles")>]
[<assembly: InternalsVisibleTo("Csff.Tests")>]
do ()

module internal Diagnostics =

    let validSpan (source: string) start length =
        start >= 0
        && length >= 0
        && start <= source.Length
        && length <= source.Length - start

    let excerpt (source: string) start length =
        if validSpan source start length then
            let text = source.Substring(start, min 60 length)

            let encoded =
                JsonEncodedText.Encode(text, JavaScriptEncoder.UnsafeRelaxedJsonEscaping)

            "\"" + encoded.ToString() + "\"" + if length > 60 then "..." else ""
        else
            "<invalid span>"

    let context (source: string) offset =
        let start = max 0 (min source.Length offset - 30)
        excerpt source start (min 60 (source.Length - start))

    let describe (source: string) kind start length =
        $"{kind}, start={start}, length={length}, text={excerpt source start length}"
