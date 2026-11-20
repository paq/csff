# csff

A fast C# formatter CLI written in F#.

Instead of building on Roslyn, `csff` implements its own C# lexer, parser, and document
printer in F#. It compiles to a single Native AOT executable, formats files in parallel
across available cores, and caches results per input root.

## Installation

### Native AOT .NET tool (recommended)

Requires the **.NET 10+ SDK** on supported Native AOT platforms (`linux-x64`, `linux-arm64`,
`linux-musl-x64`, `linux-musl-arm64`, `osx-arm64`, `win-x64`, `win-arm64`).
The .NET CLI automatically selects the matching native package for your OS and architecture:

```sh
dotnet tool install -g csff
```

Or run it once without installing:

```sh
dotnet tool exec csff -- --check .
```

On other platforms, the .NET CLI falls back to the portable managed package (`csff.any`),
which requires the **.NET 11 runtime**.

Standalone Native AOT archives (`.tar.gz` / `.zip`, no .NET installation required) are also
published on [GitHub Releases](https://github.com/paq/csff/releases).

## Usage

Format all C# files in the current directory:

```sh
csff .
```

Check formatting without writing files (for CI or pre-commit hooks):

```sh
csff --check .
```

Format a single file or stdin to stdout:

```sh
csff --write-stdout path/to/File.cs
cat path/to/File.cs | csff --write-stdout
```

### Options

| Option | Description |
| -- | -- |
| `--check` | Report unformatted files without rewriting them (exits `1` if any file needs formatting). |
| `--write-stdout` | Format a single file, or stdin when no path or `-` is given, and print to stdout. |
| `--config-path FILE` | Use the specified JSON or YAML configuration file instead of discovering configuration. |
| `--ignore-path FILE` | Use the specified ignore file instead of discovered `.csffignore` / `.gitignore` files. |
| `--include-generated` | Include files normally skipped as generated. |
| `--no-cache` | Neither read nor write the formatting cache. |
| `--cache-path DIR` | Store bounded per-input-root cache files in `DIR`. |
| `--jobs N` | Maximum number of parallel workers (positive integer; default: processor count). |
| `-h`, `--help` | Show CLI usage and exit. |

## Configuration

`csff` works with zero configuration by default. To customize formatting, add `.csffrc.json`,
`.csffrc.yaml`, `.csffrc.yml`, or `.editorconfig`.

See the [full documentation and benchmarks on GitHub](https://github.com/paq/csff#readme).

## License

MIT. See [LICENSE](https://github.com/paq/csff/blob/main/LICENSE) and
[THIRD-PARTY-NOTICES.txt](https://github.com/paq/csff/blob/main/THIRD-PARTY-NOTICES.txt).
