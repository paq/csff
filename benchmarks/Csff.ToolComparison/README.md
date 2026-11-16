# Csff.ToolComparison

Benchmarks `csff` against CSharpier and `dotnet format whitespace` across `dotnet/*` repositories, writes [`results/results.json`](results/results.json) and SVG charts, and updates the chart in [`README.md`](../../README.md).

## Usage

Run the full benchmark (builds `csff` with Native AOT, clones repositories, measures, renders charts, and updates `README.md`):

```sh
dotnet run -c Release --project benchmarks/Csff.ToolComparison
```

Redraw the charts and update `README.md` from existing `results.json` without re-measuring:

```sh
dotnet run -c Release --project benchmarks/Csff.ToolComparison -- --render-only
```

## Options

| Option | Description |
| -- | -- |
| `--render-only` | Redraw charts and update Markdown from `results.json` without measuring. |
| `--repos a,b,c` | Repository names under `github.com/dotnet` to measure (default: `runtime,roslyn,aspnetcore,efcore,maui,winforms,wpf,BenchmarkDotNet`). |
| `--runs N` | Measured runs per tool and repository (default: `5`). |
| `--warmups N` | Unmeasured warm-up runs before timing (default: `1`). |
| `--csharpier-version V` | CSharpier version to install (default: `1.4.0`). |
| `--csff PATH` | Use an existing `csff` executable instead of building one. |
| `--readme PATH` | Markdown file containing `<!-- tool-comparison:start -->` / `<!-- tool-comparison:end -->` markers. Repeatable (default: root `README.md`). |
| `--no-readme` | Do not modify any Markdown files. |
| `--work DIR` | Directory for cloned repositories and installed tools (default: `out/tool-comparison.noindex`). |
| `--output DIR` | Directory for `results.json` and SVG charts (default: `results`). |
