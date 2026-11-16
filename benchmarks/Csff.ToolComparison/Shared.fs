module Csff.ToolComparison.Shared

open System
open System.IO
open System.Reflection
open System.Text.Json.Nodes
open System.Text.RegularExpressions

[<NoComparison; NoEquality>]
type Tool =
    {
        Key: string
        Label: string
        Accepted: int list
        Summary: Regex
    }

let tools =
    [|
        {
            Key = "csff"
            Label = "csff"
            Accepted = [ 0; 1; 3 ]
            Summary = Regex(@"Formatted (\d+) C# files")
        }
        {
            Key = "csharpier"
            Label = "CSharpier"
            Accepted = [ 0; 1 ]
            Summary = Regex(@"Formatted (\d+) files")
        }
        {
            Key = "dotnet-format"
            Label = "dotnet format whitespace"
            Accepted = [ 0 ]
            Summary = Regex(@"Formatted (\d+) of (\d+) files")
        }
    |]

let projectDirectory () =
    Assembly.GetExecutingAssembly().GetCustomAttributes<AssemblyMetadataAttribute>()
    |> Seq.tryFind (fun attribute -> attribute.Key = "ProjectDirectory")
    |> Option.map (fun attribute -> attribute.Value)
    |> Option.defaultValue Environment.CurrentDirectory

let repositoryRoot () =
    Path.GetFullPath(Path.Combine(projectDirectory (), "..", ".."))

let text (node: JsonNode) (name: string) =
    match node[name] with
    | null -> ""
    | value -> value.GetValue<string>()

let toolResult (repository: JsonNode) (key: string) : JsonNode =
    let measured = repository["tools"]
    measured[key]

let medianSeconds (repository: JsonNode) (tool: Tool) =
    match (toolResult repository tool.Key)["median"] with
    | null -> None
    | value -> Some(value.GetValue<float>())

let repositoriesBySize (results: JsonNode) =
    results["repositories"].AsArray()
    |> Seq.map (fun node -> node)
    |> Seq.sortByDescending (fun node -> node["files"].GetValue<int>())
    |> Array.ofSeq

let formatSeconds (value: float) =
    if value < 1.0 then sprintf "%.2f s" value
    elif value < 10.0 then sprintf "%.1f s" value
    else sprintf "%.0f s" value

let escape (text: string) =
    text.Replace("&", "&amp;").Replace("<", "&lt;").Replace(">", "&gt;").Replace("\"", "&quot;")
