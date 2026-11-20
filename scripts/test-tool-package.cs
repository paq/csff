#!/usr/bin/env dotnet
using System.Diagnostics;
using System.Security;
using System.Text;
using System.Text.RegularExpressions;

string[] validRids =
[
    "linux-x64",
    "linux-arm64",
    "linux-musl-x64",
    "linux-musl-arm64",
    "osx-x64",
    "osx-arm64",
    "win-x64",
    "win-arm64",
    "any",
];

string? packageSource = null;
string? version = null;
string? expectedRid = null;
string packageId = "csff";
const string usage =
    "usage: dotnet run scripts/test-tool-package.cs -- --package-source <dir> --version <version> --expected-rid <rid> [--package-id <id>]";

for (int i = 0; i < args.Length; i++)
{
    switch (args[i])
    {
        case "-h" or "--help":
            Console.WriteLine(usage);
            Console.WriteLine();
            Console.WriteLine(
                "Install a locally packed csff .NET tool package into an isolated directory and smoke-test it."
            );
            Console.WriteLine($"  --expected-rid {{{string.Join(",", validRids)}}}");
            return 0;
        case "--package-source" when i + 1 < args.Length:
            packageSource = Path.GetFullPath(args[++i]);
            break;
        case "--version" when i + 1 < args.Length:
            version = args[++i];
            break;
        case "--expected-rid" when i + 1 < args.Length:
            expectedRid = args[++i];
            break;
        case "--package-id" when i + 1 < args.Length:
            packageId = args[++i];
            break;
        default:
            return Usage($"unrecognized argument: {args[i]}");
    }
}

if (packageSource is null || version is null || expectedRid is null)
{
    return Usage("--package-source, --version, and --expected-rid are required");
}

if (!Directory.Exists(packageSource))
{
    return Usage($"--package-source directory does not exist: {packageSource}");
}

if (!IsValidReleaseVersion(version))
{
    return Usage(
        "--version must be a canonical SemVer version without build metadata (e.g. 0.1.0 or 0.1.0-rc.1)"
    );
}

if (!validRids.Contains(expectedRid))
{
    return Usage($"--expected-rid must be one of {string.Join(", ", validRids)}");
}

if (packageId is not ("csff" or "csff.any"))
{
    return Usage("--package-id must be 'csff' or 'csff.any'");
}

if (packageId == "csff.any" && expectedRid != "any")
{
    return Usage("--package-id csff.any requires --expected-rid any");
}

try
{
    VerifyToolPackage(packageSource, packageId, version, expectedRid);
    Console.WriteLine(
        $"Verified .NET tool package '{packageId}' {version} (resolved RID: {expectedRid})."
    );
    return 0;
}
catch (Exception error)
{
    Console.Error.WriteLine($"test-tool-package: {error.Message}");
    return 1;
}

int Usage(string message)
{
    Console.Error.WriteLine(usage);
    Console.Error.WriteLine($"test-tool-package: {message}");
    return 2;
}

static bool IsValidReleaseVersion(string? value) =>
    value is not null
    && Regex.IsMatch(
        value,
        @"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-(?:0|[1-9][0-9]*|[0-9]*[A-Za-z-][0-9A-Za-z-]*)(\.(?:0|[1-9][0-9]*|[0-9]*[A-Za-z-][0-9A-Za-z-]*))*)?$"
    );

void VerifyToolPackage(string sourceDir, string id, string toolVersion, string rid)
{
    string temporary = Directory.CreateTempSubdirectory("csff-tool-smoke-").FullName;

    try
    {
        string toolPath = Path.Combine(temporary, "tool");
        string workspace = Path.Combine(temporary, "workspace");
        Directory.CreateDirectory(workspace);

        string nugetConfig = Path.Combine(temporary, "nuget.config");
        string escapedSource = SecurityElement.Escape(sourceDir) ?? sourceDir;
        WriteText(
            nugetConfig,
            $"""
            <?xml version="1.0" encoding="utf-8"?>
            <configuration>
              <packageSources>
                <clear />
                <add key="local" value="{escapedSource}" />
              </packageSources>
            </configuration>
            """
        );

        RunProcess(
            "dotnet",
            workspace,
            [
                "tool",
                "install",
                "--tool-path",
                toolPath,
                "--configfile",
                nugetConfig,
                "--version",
                toolVersion,
                id,
            ],
            stripDotnetRoot: false,
            stdin: null,
            expect: 0
        );

        VerifyInstalledStore(toolPath, id, toolVersion, rid);

        string shim = ResolveToolShim(toolPath);
        bool nativeAot = rid != "any";
        SmokeTestInstalledTool(shim, workspace, stripDotnetRoot: nativeAot);
    }
    finally
    {
        Directory.Delete(temporary, recursive: true);
    }
}

void VerifyInstalledStore(string toolPath, string id, string toolVersion, string rid)
{
    string lowerId = id.ToLowerInvariant();
    string lowerVersion = toolVersion.ToLowerInvariant();
    string storeVersionDir = Path.Combine(toolPath, ".store", lowerId, lowerVersion);

    if (!Directory.Exists(storeVersionDir))
    {
        throw new InvalidOperationException(
            $"Expected tool store directory not found: {storeVersionDir}"
        );
    }

    string expectedImplId = $"csff.{rid}".ToLowerInvariant();
    string[] installedPackages = Directory
        .GetDirectories(storeVersionDir)
        .Select(Path.GetFileName)
        .Where(name => name is not null)
        .Select(name => name!.ToLowerInvariant())
        .Order(StringComparer.Ordinal)
        .ToArray();

    string[] expectedPackages =
        id == "csff"
            ? new[] { "csff", expectedImplId }.Order(StringComparer.Ordinal).ToArray()
            : new[] { expectedImplId };

    if (!installedPackages.SequenceEqual(expectedPackages))
    {
        throw new InvalidOperationException(
            $"Unexpected packages installed in {storeVersionDir}: [{string.Join(", ", installedPackages)}], expected [{string.Join(", ", expectedPackages)}]"
        );
    }

    string implRoot = Path.Combine(storeVersionDir, expectedImplId, lowerVersion);

    if (rid == "any")
    {
        string managedDll = Path.Combine(implRoot, "tools", "net11.0", "any", "Csff.Cli.dll");

        if (!File.Exists(managedDll))
        {
            throw new FileNotFoundException(
                $"Expected portable managed assembly not found: {managedDll}"
            );
        }
    }
    else
    {
        string exeName = rid.StartsWith("win-", StringComparison.Ordinal)
            ? "Csff.Cli.exe"
            : "Csff.Cli";
        string nativeExe = Path.Combine(implRoot, "tools", "any", rid, exeName);

        if (!File.Exists(nativeExe))
        {
            throw new FileNotFoundException(
                $"Expected Native AOT executable not found: {nativeExe}"
            );
        }

        string notices = Path.Combine(
            implRoot,
            "tools",
            "any",
            rid,
            "DOTNET-THIRD-PARTY-NOTICES.TXT"
        );

        if (!File.Exists(notices))
        {
            throw new FileNotFoundException($"Expected runtime notices not found: {notices}");
        }
    }
}

string ResolveToolShim(string toolPath)
{
    if (OperatingSystem.IsWindows())
    {
        string cmd = Path.Combine(toolPath, "csff.cmd");

        if (File.Exists(cmd))
        {
            return cmd;
        }

        string exe = Path.Combine(toolPath, "csff.exe");

        if (File.Exists(exe))
        {
            return exe;
        }

        throw new FileNotFoundException($"Neither csff.cmd nor csff.exe was created in {toolPath}");
    }

    string unix = Path.Combine(toolPath, "csff");

    if (!File.Exists(unix))
    {
        throw new FileNotFoundException($"Expected tool shim not found: {unix}");
    }

    return unix;
}

void SmokeTestInstalledTool(string shim, string workspace, bool stripDotnetRoot)
{
    string configuration = Path.Combine(workspace, "settings.json");
    WriteText(configuration, "{\"endOfLine\":\"lf\"}");
    string source = Path.Combine(workspace, "Example.cs");
    WriteText(source, "#if A\nclass C{int M()=>1;}\n#else\nclass C{int M()=>2;}\n#endif\n");
    byte[] original = File.ReadAllBytes(source);
    string[] common = ["--no-cache", "--config-path", configuration];

    var helpResult = RunTool(shim, workspace, ["--help"], stripDotnetRoot, stdin: null, expect: 0);

    if (!helpResult.Stdout.Contains("Usage: csff", StringComparison.Ordinal))
    {
        throw new InvalidOperationException(
            "Tool --help output did not contain expected usage header"
        );
    }

    var stdinResult = RunTool(
        shim,
        workspace,
        [.. common, "--write-stdout"],
        stripDotnetRoot,
        stdin: "class S{int X()=>1;}\n",
        expect: 0
    );

    if (!stdinResult.Stdout.Contains("int X() => 1;", StringComparison.Ordinal))
    {
        throw new InvalidOperationException(
            $"Unexpected --write-stdout output: {stdinResult.Stdout}"
        );
    }

    RunTool(shim, workspace, [.. common, source], stripDotnetRoot, stdin: null, expect: 0);
    byte[] formatted = File.ReadAllBytes(source);

    if (formatted.AsSpan().SequenceEqual(original))
    {
        throw new InvalidOperationException("The installed tool did not format the fixture");
    }

    RunTool(
        shim,
        workspace,
        [.. common, "--check", source],
        stripDotnetRoot,
        stdin: null,
        expect: 0
    );
    RunTool(shim, workspace, [.. common, source], stripDotnetRoot, stdin: null, expect: 0);

    if (!File.ReadAllBytes(source).AsSpan().SequenceEqual(formatted))
    {
        throw new InvalidOperationException("The installed tool is not idempotent");
    }

    WriteText(source, "class C { int X = ; }");
    byte[] malformed = File.ReadAllBytes(source);
    var refused = RunTool(
        shim,
        workspace,
        [.. common, source],
        stripDotnetRoot,
        stdin: null,
        expect: null
    );

    if (refused.ExitCode != 1 || !File.ReadAllBytes(source).AsSpan().SequenceEqual(malformed))
    {
        throw new InvalidOperationException("Malformed input was not refused without a write");
    }
}

(int ExitCode, string Stdout, string Stderr) RunTool(
    string shim,
    string workingDirectory,
    string[] arguments,
    bool stripDotnetRoot,
    string? stdin,
    int? expect
)
{
    if (OperatingSystem.IsWindows() && shim.EndsWith(".cmd", StringComparison.OrdinalIgnoreCase))
    {
        string QuoteCmd(string value) => "\"" + value.Replace("\"", "\"\"") + "\"";
        string commandLine =
            "/d /s /c \""
            + QuoteCmd(shim)
            + " "
            + string.Join(" ", arguments.Select(QuoteCmd))
            + "\"";
        return RunProcessRaw(
            "cmd.exe",
            commandLine,
            workingDirectory,
            stripDotnetRoot,
            stdin,
            expect
        );
    }

    return RunProcess(shim, workingDirectory, arguments, stripDotnetRoot, stdin, expect);
}

(int ExitCode, string Stdout, string Stderr) RunProcess(
    string fileName,
    string workingDirectory,
    string[] arguments,
    bool stripDotnetRoot,
    string? stdin,
    int? expect
)
{
    var start = new ProcessStartInfo(fileName)
    {
        WorkingDirectory = workingDirectory,
        RedirectStandardInput = stdin is not null,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false,
    };

    foreach (string argument in arguments)
    {
        start.ArgumentList.Add(argument);
    }

    return Execute(
        start,
        stripDotnetRoot,
        stdin,
        expect,
        $"{Path.GetFileName(fileName)} {string.Join(" ", arguments)}"
    );
}

(int ExitCode, string Stdout, string Stderr) RunProcessRaw(
    string fileName,
    string rawArguments,
    string workingDirectory,
    bool stripDotnetRoot,
    string? stdin,
    int? expect
)
{
    var start = new ProcessStartInfo(fileName)
    {
        Arguments = rawArguments,
        WorkingDirectory = workingDirectory,
        RedirectStandardInput = stdin is not null,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        UseShellExecute = false,
    };
    return Execute(start, stripDotnetRoot, stdin, expect, $"{fileName} {rawArguments}");
}

(int ExitCode, string Stdout, string Stderr) Execute(
    ProcessStartInfo start,
    bool stripDotnetRoot,
    string? stdin,
    int? expect,
    string label
)
{
    if (stripDotnetRoot)
    {
        foreach (
            string key in start
                .Environment.Keys.Where(key =>
                    key.StartsWith("DOTNET_ROOT", StringComparison.OrdinalIgnoreCase)
                )
                .ToList()
        )
        {
            start.Environment.Remove(key);
        }
    }

    using var process = Process.Start(start)!;
    var stdoutTask = process.StandardOutput.ReadToEndAsync();
    var stderrTask = process.StandardError.ReadToEndAsync();

    if (stdin is not null)
    {
        process.StandardInput.Write(stdin);
        process.StandardInput.Close();
    }

    process.WaitForExit();
    string stdout = stdoutTask.GetAwaiter().GetResult();
    string stderr = stderrTask.GetAwaiter().GetResult();

    if (expect is int code && process.ExitCode != code)
    {
        throw new InvalidOperationException(
            $"{label} exited with {process.ExitCode}\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }

    return (process.ExitCode, stdout, stderr);
}

static void WriteText(string path, string text) =>
    File.WriteAllText(path, text.ReplaceLineEndings(Environment.NewLine), new UTF8Encoding(false));
