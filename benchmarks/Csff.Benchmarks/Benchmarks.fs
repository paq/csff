namespace Csff.Benchmarks

open System
open BenchmarkDotNet.Attributes

[<MemoryDiagnoser>]
type Stages() =
    let mutable pipeline: Pipeline = Unchecked.defaultof<_>

    member _.Fixtures = Fixtures.names

    [<ParamsSource("Fixtures")>]
    member val Fixture = "" with get, set

    member private this.Setup(stage: Stage) =
        pipeline <- new Pipeline(Fixtures.load this.Fixture)
        pipeline.Prepare stage

    [<GlobalSetup(Target = "Lex")>]
    member this.SetupLex() = this.Setup Lex

    [<GlobalSetup(Target = "Parse")>]
    member this.SetupParse() = this.Setup Parse

    [<GlobalSetup(Target = "Build")>]
    member this.SetupBuild() = this.Setup Build

    [<GlobalSetup(Target = "Print")>]
    member this.SetupPrint() = this.Setup Print

    [<GlobalSetup(Target = "Verify")>]
    member this.SetupVerify() = this.Setup Verify

    [<GlobalSetup(Target = "Format")>]
    member this.SetupFormat() = this.Setup Format

    [<GlobalCleanup>]
    member _.Cleanup() = (pipeline :> IDisposable).Dispose()

    [<Benchmark>]
    member _.Lex() = pipeline.Lex()

    [<Benchmark>]
    member _.Parse() = pipeline.Parse()

    [<Benchmark>]
    member _.Build() = pipeline.Build()

    [<Benchmark>]
    member _.Print() = pipeline.Print()

    [<Benchmark>]
    member _.Verify() = pipeline.Verify()

    [<Benchmark>]
    member _.Format() = pipeline.Format()

[<MemoryDiagnoser>]
type NestedLambdas() =
    let mutable pipeline: Pipeline = Unchecked.defaultof<_>

    [<Params(4, 8, 16, 32)>]
    member val Depth = 0 with get, set

    [<GlobalSetup>]
    member this.Setup() =
        pipeline <- new Pipeline(Fixtures.nestedLambdas this.Depth)
        pipeline.Prepare Format

    [<GlobalCleanup>]
    member _.Cleanup() = (pipeline :> IDisposable).Dispose()

    [<Benchmark>]
    member _.Format() = pipeline.Format()
