#!/usr/bin/env dotnet
using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using System.Xml.Linq;

string[] rids =
[
    "linux-x64",
    "linux-arm64",
    "linux-musl-x64",
    "linux-musl-arm64",
    "osx-arm64",
    "win-x64",
    "win-arm64",
];
string root = Path.GetFullPath(Path.Combine((string)AppContext.GetData("EntryPointFileDirectoryPath")!, ".."));

string? rid = null;
string? publishDirectory = null;
bool hasVersionOverride = false;
string? versionOverride = null;
string outputDirectory = Path.Combine(root, "out", "releases");
const string usage = "usage: dotnet run scripts/package-native.cs -- --rid <rid> --publish-directory <dir> [--output-directory <dir>] [--version <version>]";

for (int i = 0; i < args.Length; i++)
{
    switch (args[i])
    {
        case "-h" or "--help":
            Console.WriteLine(usage);
            Console.WriteLine();
            Console.WriteLine("Smoke-test and archive a published native CLI on its target host.");
            Console.WriteLine($"  --rid {{{string.Join(",", rids)}}}");
            return 0;
        case "--rid" when i + 1 < args.Length:
            rid = args[++i];
            break;
        case "--publish-directory" when i + 1 < args.Length:
            publishDirectory = Path.GetFullPath(args[++i]);
            break;
        case "--output-directory" when i + 1 < args.Length:
            outputDirectory = Path.GetFullPath(args[++i]);
            break;
        case "--version" when i + 1 < args.Length:
            hasVersionOverride = true;
            versionOverride = args[++i];
            break;
        default:
            return Usage($"unrecognized argument: {args[i]}");
    }
}

if (rid is null || publishDirectory is null)
{
    return Usage("--rid and --publish-directory are required");
}

if (!rids.Contains(rid))
{
    return Usage($"--rid must be one of {string.Join(", ", rids)}");
}

if (hasVersionOverride)
{
    if (!IsValidReleaseVersion(versionOverride))
    {
        return Usage("--version must be a canonical SemVer version without build metadata (e.g. 0.1.0 or 0.1.0-rc.1)");
    }
}

try
{
    Console.WriteLine(Package(rid, publishDirectory, outputDirectory, versionOverride));
    return 0;
}
catch (Exception error)
{
    Console.Error.WriteLine($"package-native: {error.Message}");
    return 1;
}

int Usage(string message)
{
    Console.Error.WriteLine(usage);
    Console.Error.WriteLine($"package-native: {message}");
    return 2;
}

static bool IsValidReleaseVersion(string? value) =>
    value is not null
    && Regex.IsMatch(
        value,
        @"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)(-(?:0|[1-9][0-9]*|[0-9]*[A-Za-z-][0-9A-Za-z-]*)(\.(?:0|[1-9][0-9]*|[0-9]*[A-Za-z-][0-9A-Za-z-]*))*)?$"
    );

string Package(string rid, string publishDirectory, string outputDirectory, string? versionOverride)
{
    bool windows = rid.StartsWith("win-", StringComparison.Ordinal);
    string source = Path.Combine(publishDirectory, windows ? "Csff.Cli.exe" : "Csff.Cli");
    string? actual = BinaryRid(source);
    if (actual != rid)
    {
        throw new InvalidOperationException($"Expected a {rid} executable, found {actual ?? "None"}: {source}");
    }

    string commit = Git("rev-parse", "HEAD");
    string shortCommit = Git("rev-parse", "--short", "HEAD");
    bool dirty = Git("status", "--porcelain").Length > 0;
    string baseVersion = XDocument.Load(Path.Combine(root, "src", "Csff.Cli", "Csff.Cli.fsproj"))
        .Descendants("CsffBaseVersion").First().Value;
    string version = versionOverride is null
        ? $"{baseVersion}-g{shortCommit}" + (dirty ? ".dirty" : "")
        : versionOverride;
    string name = $"csff-{version}-{rid}";
    Directory.CreateDirectory(outputDirectory);

    string temporary = Directory.CreateTempSubdirectory("csff-native-package-").FullName;
    try
    {
        string payload = Path.Combine(temporary, name);
        Directory.CreateDirectory(payload);
        string executable = Path.Combine(payload, windows ? "csff.exe" : "csff");
        File.Copy(source, executable);
        if (!OperatingSystem.IsWindows())
        {
            File.SetUnixFileMode(executable, (UnixFileMode)Convert.ToInt32("755", 8));
        }

        SmokeTest(executable);
        File.Copy(Path.Combine(root, "LICENSE"), Path.Combine(payload, "LICENSE"));
        File.Copy(Path.Combine(root, "THIRD-PARTY-NOTICES.txt"), Path.Combine(payload, "THIRD-PARTY-NOTICES.txt"));
        string runtimeNotices = Path.Combine(publishDirectory, "DOTNET-THIRD-PARTY-NOTICES.TXT");
        if (!File.Exists(runtimeNotices))
        {
            throw new FileNotFoundException($"The Native AOT publish wrote no runtime notices: {runtimeNotices}");
        }
        File.Copy(runtimeNotices, Path.Combine(payload, Path.GetFileName(runtimeNotices)));

        string sdk = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "global.json")))
            .RootElement.GetProperty("sdk").GetProperty("version").GetString()!;
        using (var manifest = new MemoryStream())
        {
            using (var writer = new Utf8JsonWriter(manifest, new JsonWriterOptions { Indented = true }))
            {
                writer.WriteStartObject();
                writer.WriteString("version", version);
                writer.WriteString("commit", commit);
                writer.WriteBoolean("dirty", dirty);
                writer.WriteString("rid", rid);
                writer.WriteString("sdk", sdk);
                writer.WriteString("executable", Path.GetFileName(executable));
                writer.WriteString("sha256", Digest(executable));
                writer.WriteEndObject();
            }
            string json = Encoding.UTF8.GetString(manifest.ToArray()).ReplaceLineEndings("\n");
            WriteText(Path.Combine(payload, "manifest.json"), json + "\n");
        }

        WriteText(
            Path.Combine(payload, "README.txt"),
            $"csff {version} ({rid})\nCommit: {commit}\n\n"
                + "No .NET installation is needed. Put this directory on PATH, then run:\n"
                + "  csff .\n  csff --check .\n  csff --help\n"
        );

        string archive;
        if (windows)
        {
            archive = Path.Combine(outputDirectory, name + ".zip");
            File.Delete(archive);
            using var bundle = ZipFile.Open(archive, ZipArchiveMode.Create);
            foreach (string item in Directory.GetFiles(payload).Order(StringComparer.OrdinalIgnoreCase))
            {
                bundle.CreateEntryFromFile(item, $"{name}/{Path.GetFileName(item)}", CompressionLevel.Optimal);
            }
        }
        else
        {
            archive = Path.Combine(outputDirectory, name + ".tar.gz");
            using var file = File.Create(archive);
            using var gzip = new GZipStream(file, CompressionLevel.Optimal);
            TarFile.CreateFromDirectory(payload, gzip, includeBaseDirectory: true);
        }

        File.WriteAllBytes(archive + ".sha256", Encoding.UTF8.GetBytes($"{Digest(archive)}  {Path.GetFileName(archive)}\n"));
        return archive;
    }
    finally
    {
        Directory.Delete(temporary, recursive: true);
    }
}

string? BinaryRid(string path)
{
    if (!File.Exists(path))
    {
        return null;
    }

    using var stream = File.OpenRead(path);
    var header = new byte[64];
    int length = stream.ReadAtLeast(header, header.Length, throwOnEndOfStream: false);
    ReadOnlySpan<byte> bytes = header.AsSpan(0, length);
    if (length >= 64 && bytes[..4].SequenceEqual("\u007fELF"u8) && bytes[4] == 2 && bytes[5] == 1)
    {
        string? architecture = BitConverter.ToUInt16(header, 18) switch { 62 => "x64", 183 => "arm64", _ => null };
        if (architecture is null)
        {
            return null;
        }
        string? interpreter = ReadElfInterpreter(stream, header);
        bool musl = interpreter is not null && interpreter.Contains("musl", StringComparison.OrdinalIgnoreCase);
        return (musl ? "linux-musl-" : "linux-") + architecture;
    }
    if (length >= 8 && bytes[..4].SequenceEqual(new byte[] { 0xcf, 0xfa, 0xed, 0xfe }))
    {
        string? architecture = BitConverter.ToUInt32(header, 4) switch { 0x1000007 => "x64", 0x100000C => "arm64", _ => null };
        return architecture is null ? null : "osx-" + architecture;
    }
    if (length == 64 && bytes[..2].SequenceEqual("MZ"u8))
    {
        stream.Seek(BitConverter.ToUInt32(header, 60), SeekOrigin.Begin);
        var pe = new byte[6];
        if (stream.ReadAtLeast(pe, pe.Length, throwOnEndOfStream: false) == pe.Length && pe.AsSpan(0, 4).SequenceEqual("PE\0\0"u8))
        {
            string? architecture = BitConverter.ToUInt16(pe, 4) switch { 0x8664 => "x64", 0xAA64 => "arm64", _ => null };
            return architecture is null ? null : "win-" + architecture;
        }
    }
    return null;
}

static string? ReadElfInterpreter(FileStream stream, byte[] header)
{
    ulong phoff = BitConverter.ToUInt64(header, 32);
    ushort phentsize = BitConverter.ToUInt16(header, 54);
    ushort phnum = BitConverter.ToUInt16(header, 56);
    if (phoff == 0 || phentsize < 56 || phnum == 0 || phoff > (ulong)stream.Length)
    {
        return null;
    }

    var entry = new byte[phentsize];
    for (int i = 0; i < phnum; i++)
    {
        ulong offset = phoff + (ulong)i * phentsize;
        if (offset + phentsize > (ulong)stream.Length)
        {
            return null;
        }
        stream.Seek((long)offset, SeekOrigin.Begin);
        if (stream.ReadAtLeast(entry, entry.Length, throwOnEndOfStream: false) != entry.Length)
        {
            return null;
        }
        uint pType = BitConverter.ToUInt32(entry, 0);
        if (pType != 3) // PT_INTERP
        {
            continue;
        }
        ulong pOffset = BitConverter.ToUInt64(entry, 8);
        ulong pFilesz = BitConverter.ToUInt64(entry, 32);
        if (pFilesz == 0 || pFilesz > 1024 || pOffset + pFilesz > (ulong)stream.Length)
        {
            return null;
        }
        var interpBytes = new byte[pFilesz];
        stream.Seek((long)pOffset, SeekOrigin.Begin);
        if (stream.ReadAtLeast(interpBytes, interpBytes.Length, throwOnEndOfStream: false) != interpBytes.Length)
        {
            return null;
        }
        return Encoding.UTF8.GetString(interpBytes).TrimEnd('\0');
    }
    return null;
}

string Digest(string path)
{
    using var stream = File.OpenRead(path);
    return Convert.ToHexStringLower(SHA256.HashData(stream));
}

void SmokeTest(string executable)
{
    string directory = Directory.CreateTempSubdirectory("csff-native-smoke-").FullName;
    try
    {
        string configuration = Path.Combine(directory, "settings.json");
        WriteText(configuration, "{\"endOfLine\":\"lf\"}");
        string source = Path.Combine(directory, "Example.cs");
        WriteText(source, "#if A\nclass C{int M()=>1;}\n#else\nclass C{int M()=>2;}\n#endif\n");
        byte[] original = File.ReadAllBytes(source);
        string[] common = ["--no-cache", "--config-path", configuration];

        Run(executable, directory, ["--help"], capture: true, expect: 0);
        Run(executable, directory, [.. common, source], capture: false, expect: 0);
        byte[] formatted = File.ReadAllBytes(source);
        if (formatted.AsSpan().SequenceEqual(original))
        {
            throw new InvalidOperationException("The isolated native payload did not format the fixture");
        }
        Run(executable, directory, [.. common, "--check", source], capture: false, expect: 0);
        Run(executable, directory, [.. common, source], capture: false, expect: 0);
        if (!File.ReadAllBytes(source).AsSpan().SequenceEqual(formatted))
        {
            throw new InvalidOperationException("The native payload is not idempotent");
        }

        WriteText(source, "class C { int X = ; }");
        byte[] malformed = File.ReadAllBytes(source);
        int refused = Run(executable, directory, [.. common, source], capture: true, expect: null);
        if (refused != 1 || !File.ReadAllBytes(source).AsSpan().SequenceEqual(malformed))
        {
            throw new InvalidOperationException("Malformed input was not refused without a write");
        }
    }
    finally
    {
        Directory.Delete(directory, recursive: true);
    }
}

int Run(string executable, string directory, string[] arguments, bool capture, int? expect)
{
    var start = new ProcessStartInfo(executable)
    {
        WorkingDirectory = directory,
        RedirectStandardOutput = capture,
        RedirectStandardError = capture,
        UseShellExecute = false,
    };
    foreach (string argument in arguments)
    {
        start.ArgumentList.Add(argument);
    }
    foreach (string key in start.Environment.Keys.Where(key => key.StartsWith("DOTNET_ROOT", StringComparison.Ordinal)).ToList())
    {
        start.Environment.Remove(key);
    }

    using var process = Process.Start(start)!;
    if (capture)
    {
        var output = process.StandardOutput.ReadToEndAsync();
        var error = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        output.Wait();
        error.Wait();
    }
    else
    {
        process.WaitForExit();
    }

    if (expect is int code && process.ExitCode != code)
    {
        throw new InvalidOperationException($"{Path.GetFileName(executable)} {string.Join(" ", arguments)} exited with {process.ExitCode}");
    }
    return process.ExitCode;
}

string Git(params string[] arguments)
{
    var start = new ProcessStartInfo("git")
    {
        WorkingDirectory = root,
        RedirectStandardOutput = true,
        UseShellExecute = false,
    };
    foreach (string argument in arguments)
    {
        start.ArgumentList.Add(argument);
    }
    using var process = Process.Start(start)!;
    string output = process.StandardOutput.ReadToEnd();
    process.WaitForExit();
    if (process.ExitCode != 0)
    {
        throw new InvalidOperationException($"git {string.Join(" ", arguments)} exited with {process.ExitCode}");
    }
    return output.Trim();
}

static void WriteText(string path, string text) =>
    File.WriteAllText(path, text.ReplaceLineEndings(Environment.NewLine), new UTF8Encoding(false));
