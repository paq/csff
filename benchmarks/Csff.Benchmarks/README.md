# Csff.Benchmarks

In-process BenchmarkDotNet benchmarks for each formatting stage (`Lex`, `Parse`, `Build`, `Print`, `Verify`, `Format`) and an allocation regression gate.

## Benchmarks

Run all benchmarks:

```sh
dotnet run -c Release --project benchmarks/Csff.Benchmarks -- --filter '*'
```

Standard BenchmarkDotNet options apply (for example, `--filter '*Stages.Format*'` or `--job short`). Results are written to `BenchmarkDotNet.Artifacts`.

## Allocation gate

Check bytes allocated per operation against [`allocations.json`](allocations.json) (fails if any case rises by more than both 2% and 128 bytes):

```sh
dotnet run -c Release --project benchmarks/Csff.Benchmarks -- --gate
```

Update the baseline after an intentional allocation change:

```sh
dotnet run -c Release --project benchmarks/Csff.Benchmarks -- --gate --update
```

| Option | Description |
| -- | -- |
| `--update` | Rewrite the baseline file with the measured values. |
| `--baseline PATH` | Baseline JSON file to compare or update (default: `allocations.json`). |

Exit codes: `0` within baseline, `1` allocation regression, `2` missing baseline entry or invalid arguments.
