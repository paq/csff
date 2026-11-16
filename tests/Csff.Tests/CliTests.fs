module Csff.Tests.CliTests

open System
open System.Collections.Generic
open System.Collections.Concurrent
open System.Diagnostics
open System.IO
open System.Security.Cryptography
open System.Text
open System.Text.Json
open System.Threading
open System.Threading.Tasks
open Csff.Cli
open Csff.Printer
open Expecto

let rec private resolveLinks (path: string) =
    match Path.GetDirectoryName path with
    | null -> path
    | parent ->
        let combined = Path.Combine(resolveLinks parent, Path.GetFileName path)

        match Directory.ResolveLinkTarget(combined, true) with
        | null -> combined
        | target -> target.FullName

let private caseSensitiveTemporaryVolume =
    lazy
        (let directory =
            Path.Combine(Path.GetTempPath(), "csff-case-" + Guid.NewGuid().ToString("N"))

         Directory.CreateDirectory(Path.Combine(directory, "Probe")) |> ignore

         try
             not (Directory.Exists(Path.Combine(directory, "probe")))
         finally
             Directory.Delete(directory, true))

let private withDirectory action =
    let directory =
        Path.Combine(Path.GetTempPath(), "csff-cli-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory directory |> ignore
    let directory = resolveLinks directory
    File.WriteAllText(Path.Combine(directory, ".git"), "gitdir: /fixture")

    try
        action directory
    finally
        Directory.Delete(directory, true)

let private write directory relative (source: string) =
    let path = Path.Combine(directory, relative)
    Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
    File.WriteAllText(path, source)
    path

let private discover roots = Discovery.files roots None None false 1

let private sharedDiscovery roots ignorePath jobs =
    let comparer =
        if OperatingSystem.IsWindows() then
            StringComparer.OrdinalIgnoreCase
        else
            StringComparer.Ordinal

    let counts = ConcurrentDictionary<string, int>(comparer)

    let enumerate directory =
        seq {
            counts.AddOrUpdate(directory, 1, fun _ count -> count + 1) |> ignore
            yield! Discovery.enumerate directory
        }

    let spellings = Discovery.Spellings()

    let seen =
        HashSet<string>(
            { new IEqualityComparer<string> with
                member _.GetHashCode path =
                    StringComparer.OrdinalIgnoreCase.GetHashCode path

                member _.Equals(left, right) = spellings.SameEntry(left, right)
            }
        )

    let expected =
        roots
        |> Array.mapi (fun index root ->
            Discovery.files [| root |] None ignorePath false 1
            |> Array.map (fun file -> { file with Root = index }))
        |> Array.concat
        |> Array.filter (fun file -> seen.Add file.Path)
        |> Array.sortWith (fun a b -> StringComparer.Ordinal.Compare(a.Path, b.Path))

    let actual =
        Discovery.filesWithEnumeration enumerate roots None ignorePath false jobs

    Expect.equal
        actual
        expected
        "Shared walks retain paths, settings and first accepting root ownership."

    Expect.all counts.Values ((=) 1) "Each physical directory is enumerated once per request."
    actual, counts.Count

let private run roots check noCache generated jobs =
    let files = Discovery.files roots None None generated jobs
    files, Formatter.run roots files check noCache generated jobs None CancellationToken.None

let private check roots = run roots true false false 2 |> snd

let private cachePath root =
    Cache.path (Formatter.cacheDirectory root) root

let private includedSettings result =
    match result with
    | Some settings -> settings
    | None -> failtest "The virtual C# file must be included by its configuration."

let private allGood results =
    for result in results do
        Expect.isNull result.Error "Formatting must succeed."

        Expect.isNull result.Unverified "Formatting must be proven."

let private capture action =
    let stdout, stderr, stdin = Console.Out, Console.Error, Console.In
    use output = new StringWriter()
    use errors = new StringWriter()

    try
        Console.SetOut output
        Console.SetError errors
        let code = action ()
        code, output.ToString(), errors.ToString()
    finally
        Console.SetOut stdout
        Console.SetError stderr
        Console.SetIn stdin

let private key number =
    {
        A = uint64 number
        B = 0UL
        C = 0UL
        D = 0UL
        Width = 100
        Indent = 4
        Flags = 8
    }

let private fileTests =
    testList
        "cli"
        [
            test "cache identities share directory listings for sibling file roots" {
                withDirectory (fun root ->
                    let reads = Dictionary<string, int>(StringComparer.Ordinal)

                    let read directory =
                        reads[directory] <-
                            match reads.TryGetValue directory with
                            | true, count -> count + 1
                            | _ -> 1

                        Directory.EnumerateFileSystemEntries directory

                    let spellings = Discovery.Spellings(read)
                    let directory = Path.Combine(root, "cache")
                    let roots = Array.init 256 (fun i -> write root ($"source{i}.cs") "class C{}")

                    let paths =
                        roots
                        |> Array.map (fun root -> Cache.pathWithSpellings spellings directory root)

                    Expect.equal
                        (Array.distinct paths).Length
                        roots.Length
                        "Every file root has a slot."

                    Expect.equal reads[root] 1 "Sibling roots share the one parent listing."
                    Expect.all reads.Values ((=) 1) "Ancestor listings are also read only once.")
            }
            test "cache root identity follows the volume and removes trailing separators" {
                withDirectory (fun root ->
                    Directory.CreateDirectory(Path.Combine(root, "Mixed")) |> ignore
                    let child = Path.Combine(root, "Mixed")
                    let variant = Path.Combine(root, "mixed")
                    let directory = Path.Combine(child, "cache")
                    let normal = Cache.path directory child

                    Expect.equal
                        (Cache.path directory (child + string Path.DirectorySeparatorChar))
                        normal
                        "A trailing separator does not create another cache slot."

                    if not caseSensitiveTemporaryVolume.Value then
                        Expect.equal
                            (Cache.path (Path.Combine(variant, "cache")) variant)
                            normal
                            "Root and cache-directory aliases share one slot."
                    else
                        Directory.CreateDirectory variant |> ignore

                        Expect.notEqual
                            (Cache.path directory variant)
                            normal
                            "Case-distinct roots have distinct cache slots.")
            }
            test "discovery metadata retains case-distinct directory settings" {
                withDirectory (fun root ->
                    let parent = Path.Combine(root, "sensitive")
                    Directory.CreateDirectory parent |> ignore

                    if
                        not (OperatingSystem.IsWindows()) && not caseSensitiveTemporaryVolume.Value
                    then
                        skiptest "The temporary volume folds directory names;"

                    if OperatingSystem.IsWindows() then
                        let start = ProcessStartInfo "fsutil.exe"

                        for arg in [ "file"; "setCaseSensitiveInfo"; parent; "enable" ] do
                            start.ArgumentList.Add arg

                        match Subprocess.run start with
                        | Subprocess.Exited(0, _, _) -> ()
                        | Subprocess.Exited(_, output, errors)
                        | Subprocess.Timeout(output, errors) ->
                            skiptest ("Case-sensitive directories unavailable: " + output + errors)

                    write parent "Mixed/.csffrc.json" "{\"indentSize\":2}" |> ignore
                    write parent "mixed/.csffrc.json" "{\"indentSize\":6}" |> ignore
                    let upper = write parent "Mixed/a.cs" "class C{}"
                    let lower = write parent "mixed/a.cs" "class D{}"

                    Expect.notEqual
                        (Cache.path root upper)
                        (Cache.path root lower)
                        "Case-distinct physical roots cannot share a cache slot."

                    for jobs in [ 1; 4 ] do
                        for roots in
                            [
                                [| upper; lower |]
                                [| Path.GetDirectoryName upper; Path.GetDirectoryName lower |]
                            ] do
                            let files = Discovery.files roots None None false jobs
                            Expect.equal files.Length 2 "Both physical directories are discovered."

                            Expect.equal
                                (files
                                 |> Array.map (fun file -> file.Settings.Printer.IndentSize)
                                 |> Array.sort)
                                [| 2; 6 |]
                                "Each directory retains its own metadata.")
            }
            test "legacy cache versions without conformance identity are rejected" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "legacy.cache")
                    let entries = HashSet<CacheKey>()
                    entries.Add(key 1) |> ignore
                    Cache.save path (HashSet<CacheKey>()) entries
                    let bytes = File.ReadAllBytes path

                    let assemblyId (assembly: System.Reflection.Assembly) =
                        let id = assembly.ManifestModule.ModuleVersionId
                        id.ToString()

                    let legacy =
                        "csff-cache-v1\n"
                        + assemblyId typeof<CacheKey>.Assembly
                        + "\n"
                        + assemblyId typeof<Printer>.Assembly
                        + "\n"
                        + assemblyId typeof<Csff.Parser.SyntaxTree>.Assembly
                        + "\n"
                        + assemblyId typeof<Csff.Lexer.TokenBuffer>.Assembly
                        + "\n"

                    SHA256.HashData(Encoding.UTF8.GetBytes legacy).CopyTo(bytes, 0)
                    let checksum = SHA256.HashData(bytes.AsSpan(0, bytes.Length - 32))
                    checksum.CopyTo(bytes, bytes.Length - 32)
                    File.WriteAllBytes(path, bytes)

                    Expect.equal
                        (Cache.read path).Count
                        0
                        "Caches that omitted the syntax verifier's version cannot bypass validation.")
            }
            test "a binary chain deeper than a thread-pool stack formats" {
                withDirectory (fun root ->
                    let operands = String.Join(" + ", Array.init 20000 (fun i -> $"\"{i}\""))
                    let path = write root "Deep.cs" $"class C {{ string S = {operands}; }}"
                    let _, results = run [| root |] false true false 2
                    allGood results
                    let formatted = File.ReadAllText path
                    Expect.stringContains formatted "\"19999\";" "The last operand survives.")
            }
            test "a file nested past the stack fails alone and by name" {
                withDirectory (fun root ->
                    let depth = 20000

                    write
                        root
                        "Deep.cs"
                        ("class C { void M() { var x = "
                         + String.replicate depth "("
                         + "1"
                         + String.replicate depth ")"
                         + "; } }")
                    |> ignore

                    write root "Plain.cs" "class C{int x;}" |> ignore
                    let files = discover [| root |]
                    let mutable results = Array.empty<FileResult>

                    let worker =
                        Thread(
                            ThreadStart(fun () ->
                                use formatter = new Worker()

                                results <-
                                    files
                                    |> Array.map (fun file ->
                                        formatter.Format(file, HashSet<CacheKey>(), true, false))),
                            1024 * 1024
                        )

                    worker.Start()
                    worker.Join()

                    let resultFor name =
                        results[files
                                |> Array.findIndex (fun file -> Path.GetFileName file.Path = name)]

                    Expect.equal files.Length 2 "Both sources are discovered."

                    Expect.stringContains
                        (resultFor "Deep.cs").Error
                        "Deep.cs"
                        "The failed file names itself."

                    Expect.stringContains
                        (resultFor "Deep.cs").Error
                        "nested too deeply"
                        "The failure explains itself rather than quoting the runtime."

                    Expect.isNull
                        (resultFor "Plain.cs").Error
                        "A file that exhausts the stack must not end the run.")
            }
            test "a file needing symbols for a complete parse formats every branch" {
                withDirectory (fun root ->
                    let header =
                        write
                            root
                            "Header.cs"
                            "class C\n{\n#if NUNIT\n    [SetUp]\n    public void SetUp()\n#elif XUNIT\n    public C()\n#endif\n    {\n        x  =  1;\n    }\n}\n"

                    let errorSource =
                        "class C\n{\n    public static int Configuration =>\n#if DEBUG\n        F(  1  );\n#elif RELEASE\n        F(  2  );\n#else\n#error Unsupported Configuration\n#endif\n\n    public static bool IsWindows  =>  true;\n#if NET46\n    public static bool IsDesktop  =>  true;\n#endif\n}\n"

                    let error = write root "Error.cs" errorSource
                    let files, results = run [| root |] false true false 2

                    let resultFor name =
                        results[files
                                |> Array.findIndex (fun file -> Path.GetFileName file.Path = name)]

                    Expect.isNull (resultFor "Header.cs").Unverified "The header file is proven."

                    Expect.equal
                        (File.ReadAllText header)
                        "class C\n{\n#if NUNIT\n    [SetUp]\n    public void SetUp()\n#elif XUNIT\n    public C()\n#endif\n    {\n        x = 1;\n    }\n}\n"
                        "Both headers are kept and the shared body is formatted."

                    use worker = new Worker()
                    Worker.Run(fun () -> worker.Print(errorSource, Settings.Default))

                    Expect.equal
                        worker.OutputText
                        "class C\n{\n    public static int Configuration =>\n#if DEBUG\n        F(1);\n#elif RELEASE\n        F(2);\n#else\n#error Unsupported Configuration\n#endif\n\n    public static bool IsWindows => true;\n#if NET46\n    public static bool IsDesktop => true;\n#endif\n}\n"
                        "Every branch is printed and nothing is dropped."

                    Expect.stringContains
                        (resultFor "Error.cs").Unverified
                        "could not be proven to preserve the C# syntax"
                        "An unproven file is named rather than written."

                    Expect.equal
                        (File.ReadAllText error)
                        errorSource
                        "An unproven file keeps every byte of its own text.")
            }
            test "syntax the parser recovers from is reported, not dropped" {
                withDirectory (fun root ->
                    let source = "class C\n{\n    void M()\n    {\n        Write(a b);\n    }\n}\n"
                    let path = write root "Recovered.cs" source
                    let _, results = run [| root |] false true false 2

                    Expect.stringContains
                        results[0].Error
                        "Unparsed C# syntax"
                        "The file is reported."

                    Expect.equal (File.ReadAllText path) source "The file is left unchanged.")
            }
            test "a directive line inside a string in skipped text keeps its indentation" {
                withDirectory (fun root ->
                    let path =
                        write
                            root
                            "Raw.cs"
                            "class C\n{\n    void M()\n    {\n#if NET\n        string s = \"\"\"\n                    #pragma warning disable X\n            text\n            \"\"\";\n#endif\n    }\n}\n"

                    let _, results = run [| root |] false true false 2
                    allGood results

                    Expect.equal
                        (File.ReadAllText path)
                        "class C\n{\n    void M()\n    {\n#if NET\n        string s = \"\"\"\n                    #pragma warning disable X\n            text\n            \"\"\";\n#endif\n    }\n}\n"
                        "The raw string's content is unchanged.")
            }
            test "a symbol set that needs others waits for them" {
                withDirectory (fun root ->
                    let path =
                        write
                            root
                            "Borrow.cs"
                            "class C\n{\n#if B && !A\n    int  =  ;\n#endif\n#if C && !(A && B)\n    int  =  ;\n#endif\n#if A\n    int  a  =  1;\n#endif\n#if B\n    int  b  =  1;\n#endif\n#if C\n    int  c  =  1;\n#endif\n}\n"

                    let _, results = run [| root |] false true false 2
                    allGood results

                    Expect.equal
                        (File.ReadAllText path)
                        "class C\n{\n#if B && !A\n    int  =  ;\n#endif\n#if C && !(A && B)\n    int  =  ;\n#endif\n#if A\n    int a = 1;\n#endif\n#if B\n    int b = 1;\n#endif\n#if C\n    int c = 1;\n#endif\n}\n"
                        "Every reachable branch is formatted; broken ones stay as written.")
            }
            test "a Windows-1252 ellipsis stays inside its comment" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "Ellipsis.cs")

                    let bytes (text: string) =
                        text.Replace("...", "\u0085") |> Encoding.Latin1.GetBytes

                    File.WriteAllBytes(
                        path,
                        bytes "class C\n{\n    // Example...int X;\n    int  Y;\n}\n"
                    )

                    let _, results = run [| root |] false true false 2
                    allGood results

                    Expect.equal
                        (File.ReadAllBytes path)
                        (bytes "class C\n{\n    // Example...int X;\n    int Y;\n}\n")
                        "The comment keeps its text and its byte.")
            }
            test "bytes that are not UTF-8 survive formatting" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "Legacy.cs")
                    let latin = Encoding.Latin1

                    File.WriteAllBytes(
                        path,
                        latin.GetBytes(
                            "class C\n{\n    // Minimal \u0096 enabling\n    string S  =  \"ìì\";\n}\n"
                        )
                    )

                    let _, results = run [| root |] false true false 2
                    allGood results

                    Expect.equal
                        (File.ReadAllBytes path)
                        (latin.GetBytes(
                            "class C\n{\n    // Minimal \u0096 enabling\n    string S = \"ìì\";\n}\n"
                        ))
                        "Each non-UTF-8 byte is written back unchanged.")
            }
            test "overlapping discovery roots enumerate each directory once" {
                withDirectory (fun root ->
                    let directories = ResizeArray<string>()
                    let mutable directory = root

                    for _ in 1..8 do
                        directories.Add directory
                        directory <- Path.Combine(directory, "d")

                    for i in 0..127 do
                        write directories[7] $"leaf{i % 16}/f{i}.cs" "class C{}" |> ignore

                    for jobs in [ 1; 4 ] do
                        for roots in
                            [
                                directories.ToArray()
                                directories.ToArray() |> Array.rev
                                Array.create 8 root
                            ] do
                            let counts = ConcurrentDictionary<string, int>()

                            let enumerate directory =
                                seq {
                                    counts.AddOrUpdate(directory, 1, fun _ count -> count + 1)
                                    |> ignore

                                    yield! Discovery.enumerate directory
                                }

                            let files =
                                Discovery.filesWithEnumeration enumerate roots None None false jobs

                            let enumerations = counts.Values |> Seq.sum

                            printfn
                                "overlapping discovery: jobs=%d, %d enumerations"
                                jobs
                                enumerations

                            Expect.equal files.Length 128 "Deduplication retains every file."

                            Expect.equal
                                enumerations
                                24
                                "Root count must not multiply physical enumeration."

                            Expect.all
                                counts.Values
                                ((=) 1)
                                "Every shared directory is enumerated once."

                            Expect.all
                                files
                                (fun file -> file.Root = 0)
                                "The first input owns these files.")
            }
            test "shared discovery does not retain irrelevant file paths" {
                withDirectory (fun root ->
                    let direct = write root "direct.CS" "class A{}"
                    let nested = write root "assets/nested.cs" "class B{}" |> Path.GetFullPath
                    let child = Path.GetDirectoryName nested

                    for jobs in [ 1; 4 ] do
                        let references = ResizeArray<WeakReference>()
                        let counts = ConcurrentDictionary<string, int>()

                        let enumerate directory =
                            seq {
                                counts.AddOrUpdate(directory, 1, fun _ count -> count + 1)
                                |> ignore

                                if directory = root then
                                    for i in 1..10_000 do
                                        let path = Path.Combine(root, $"asset{i}.cs.txt")
                                        references.Add(WeakReference(path))
                                        yield struct (path, false)

                                    yield struct (direct, false)
                                    yield struct (child, true)
                                else
                                    GC.Collect()
                                    GC.WaitForPendingFinalizers()
                                    GC.Collect()

                                    Expect.equal
                                        references.Count
                                        10_000
                                        "The parent was enumerated."

                                    let retained =
                                        references
                                        |> Seq.sumBy (fun reference ->
                                            if reference.IsAlive then 1 else 0)

                                    Expect.equal retained 0 "Cached listings release non-C# paths."
                                    yield! Discovery.enumerate directory
                            }

                        let files =
                            Discovery.filesWithEnumeration
                                enumerate
                                [| root; root |]
                                None
                                None
                                false
                                jobs

                        Expect.equal
                            (files |> Array.map (fun file -> file.Path))
                            ([| direct; nested |] |> Array.sort)
                            "Directories and case-insensitive C# candidates remain discoverable."

                        Expect.all
                            files
                            (fun file -> file.Root = 0)
                            "The first root owns the files."

                        Expect.equal counts.Count 2 "Both directories are visited."
                        Expect.all counts.Values ((=) 1) "Duplicate roots share each listing.")
            }
            test "shared discovery caches generated names only when included" {
                withDirectory (fun root ->
                    let direct = write root "direct.CS" "class A{}"
                    let nested = write root "assets.g.cs/nested.cs" "class B{}" |> Path.GetFullPath
                    let child = Path.GetDirectoryName nested

                    for jobs in [ 1; 4 ] do
                        for includeGenerated in [ false; true ] do
                            let references = ResizeArray<WeakReference>()
                            let counts = ConcurrentDictionary<string, int>()

                            let enumerate directory =
                                seq {
                                    counts.AddOrUpdate(directory, 1, fun _ count -> count + 1)
                                    |> ignore

                                    if directory = root then
                                        for i in 1..10_000 do
                                            let name =
                                                match i % 5 with
                                                | 0 -> $"generated{i}.g.cs"
                                                | 1 -> $"generated{i}.G.I.CS"
                                                | 2 -> $"generated{i}.Designer.cs"
                                                | 3 -> $"generated{i}.Generated.cs"
                                                | _ -> $"TEMPORARYGENERATEDFILE_{i}.CS"

                                            let path = Path.Combine(root, name)
                                            references.Add(WeakReference(path))
                                            yield struct (path, false)

                                        yield struct (direct, false)
                                        yield struct (child, true)
                                    else
                                        GC.Collect()
                                        GC.WaitForPendingFinalizers()
                                        GC.Collect()

                                        Expect.equal
                                            references.Count
                                            10_000
                                            "The generated-heavy parent was enumerated."

                                        let retained =
                                            references
                                            |> Seq.sumBy (fun reference ->
                                                if reference.IsAlive then 1 else 0)

                                        Expect.equal
                                            retained
                                            (if includeGenerated then 10_000 else 0)
                                            "The cache retains generated paths only when enabled."

                                        yield! Discovery.enumerate directory
                                }

                            let files =
                                Discovery.filesWithEnumeration
                                    enumerate
                                    [| root; root |]
                                    None
                                    None
                                    includeGenerated
                                    jobs

                            Expect.equal
                                files.Length
                                (if includeGenerated then 10_002 else 2)
                                "Generated candidates follow the request-wide policy."

                            Expect.containsAll
                                (files |> Array.map (fun file -> file.Path))
                                [| direct; nested |]
                                "Ordinary C# files and generated-looking directories survive."

                            Expect.all
                                files
                                (fun file -> file.Root = 0)
                                "The first root owns the files."

                            Expect.equal counts.Count 2 "Both directories are visited."
                            Expect.all counts.Values ((=) 1) "Duplicate roots share each listing.")
            }
            test "shared discovery retains mixed roots and separately anchored custom ignores" {
                withDirectory (fun root ->
                    let direct = write root "a.cs" "class A{}"
                    let nested = write root "sub/a.cs" "class B{}"
                    write root "sub/deep/b.cs" "class C{}" |> ignore
                    write root "sub/.csffrc.json" "{\"printWidth\":80}" |> ignore
                    let child = Path.GetDirectoryName nested
                    let custom = write root "custom.ignore" "/sub/\n/a.cs\n"

                    for jobs in [ 1; 4 ] do
                        for ignorePath in [ None; Some custom ] do
                            for roots in
                                [
                                    [| direct; child; root; nested |]
                                    [| root; nested; child; direct |]
                                    [| child; root; child; direct |]
                                ] do
                                sharedDiscovery roots ignorePath jobs |> ignore

                        let files, count = sharedDiscovery [| root; child |] (Some custom) jobs

                        Expect.equal
                            count
                            3
                            "The child excluded at the parent anchor still gets its own walk."

                        Expect.equal files.Length 1 "The child's custom anchor excludes its a.cs."

                        Expect.equal
                            files[0].Root
                            1
                            "The separately accepted child owns its descendant.")
            }
            test "shared discovery keeps ignore barriers and nested worktree boundaries" {
                withDirectory (fun root ->
                    write root ".gitignore" "blocked/\n" |> ignore
                    write root "blocked/.git" "gitdir: /nested-fixture" |> ignore
                    let included = write root "blocked/a.cs" "class A{}" |> Path.GetFullPath
                    let generated = write root "blocked/b.g.cs" "class B{}" |> Path.GetFullPath
                    let builtIn = write root "bin/c.cs" "class C{}" |> Path.GetFullPath
                    write root ".csffignore" "excluded/\n" |> ignore
                    let excluded = write root "excluded/d.cs" "class D{}" |> Path.GetFullPath
                    let child = Path.GetDirectoryName included

                    for jobs in [ 1; 4 ] do
                        for roots in
                            [
                                [|
                                    root
                                    child
                                    included
                                    Path.GetDirectoryName excluded
                                    builtIn
                                    generated
                                |]
                                [| builtIn; excluded; included; child; root |]
                            ] do
                            let files, count = sharedDiscovery roots None jobs

                            Expect.equal
                                count
                                2
                                "Excluded and generated inputs do not introduce walks."

                            Expect.equal
                                files.Length
                                1
                                "A nested worktree resets its inherited Git ignore."

                            Expect.equal
                                files[0].Path
                                included
                                "The nested worktree input remains accepted.")
            }
            test "shared discovery normalizes aliases using platform path case rules" {
                withDirectory (fun root ->
                    write root "Mixed/a.cs" "class A{}" |> ignore
                    write root "Mixed/deep/b.cs" "class B{}" |> ignore
                    let child = Path.Combine(root, "Mixed")
                    let custom = write root "custom.ignore" "/a.cs\n"

                    for jobs in [ 1; 4 ] do
                        for ignorePath in [ None; Some custom ] do
                            for roots in
                                [
                                    [|
                                        root
                                        Path.Combine(child, ".")
                                        child + string Path.DirectorySeparatorChar
                                    |]
                                    [| Path.Combine(child, "."); root; child |]
                                ] do
                                let _, count = sharedDiscovery roots ignorePath jobs

                                Expect.equal
                                    count
                                    3
                                    "Dot and trailing-separator aliases share physical enumeration."

                            if OperatingSystem.IsWindows() then
                                for roots in
                                    [
                                        [|
                                            root
                                            child.ToUpperInvariant()
                                            root.ToUpperInvariant()
                                        |]
                                        [| child.ToUpperInvariant(); root; child |]
                                    ] do
                                    let _, count = sharedDiscovery roots ignorePath jobs

                                    Expect.equal
                                        count
                                        3
                                        "Windows casing aliases share physical enumeration."

                    if not (OperatingSystem.IsWindows()) then
                        write root "mixed/c.cs" "class C{}" |> ignore

                        let expected = if caseSensitiveTemporaryVolume.Value then 4 else 5

                        for jobs in [ 1; 4 ] do
                            let _, count =
                                sharedDiscovery
                                    [| root; Path.Combine(root, "mixed"); child |]
                                    None
                                    jobs

                            Expect.equal
                                count
                                expected
                                "Aliases fold exactly as far as the volume says they do.")
            }
            test "keying identities reads each directory once for a whole request" {
                withDirectory (fun root ->
                    let directory = Path.Combine(root, "many")
                    Directory.CreateDirectory directory |> ignore

                    let paths =
                        [ for index in 0..499 -> Path.Combine(directory, $"File{index:D4}.cs") ]

                    for path in paths do
                        File.WriteAllText(path, "class C {}")

                    let reads = ConcurrentDictionary<string, int>(StringComparer.Ordinal)

                    let counting parent =
                        reads.AddOrUpdate(parent, 1, fun _ count -> count + 1) |> ignore
                        Directory.EnumerateFileSystemEntries parent

                    let spellings = Discovery.Spellings counting

                    for path in paths do
                        Expect.equal
                            (spellings.Identity path)
                            (spellings.Identity path)
                            "An identity is stable."

                    Expect.equal
                        reads[directory]
                        1
                        $"Five hundred siblings read their directory once, not {reads[directory]} times."

                    for KeyValue(parent, count) in reads do
                        Expect.equal count 1 $"{parent} is read once for the whole request.")
            }
            test "a case-insensitive root folds where the platform folds it" {
                if not (OperatingSystem.IsWindows()) then
                    skiptest "Only a Windows root carries case."

                let spellings = Discovery.Spellings()
                let root = Path.GetPathRoot(Path.GetFullPath(Path.GetTempPath()))

                Expect.isTrue
                    (spellings.SameEntry(root.ToUpperInvariant(), root.ToLowerInvariant()))
                    "A root's case does not distinguish two roots."

                let under (prefix: string) = Path.Combine(prefix, "src")

                Expect.isTrue
                    (spellings.SameEntry(
                        under (root.ToUpperInvariant()),
                        under (root.ToLowerInvariant())
                    ))
                    "Nor does it distinguish what lies under them."

                Expect.isFalse
                    ((Discovery.Spellings(Directory.EnumerateFileSystemEntries, false))
                        .SameEntry(root.ToUpperInvariant(), root.ToLowerInvariant()))
                    "Where a platform does not fold a root's case, the identities stay apart."
            }
            test "a listing that did not finish matches no case variant" {
                withDirectory (fun root ->
                    Directory.CreateDirectory(Path.Combine(root, "Bar")) |> ignore
                    let requested = Path.Combine(root, "Bar")
                    let variant = Path.Combine(root, "BAR")

                    let reporting fail parent =
                        seq {
                            if StringComparer.Ordinal.Equals(parent, root) then
                                yield variant

                                if fail then
                                    raise (IOException "the read did not finish")
                            else
                                yield! Directory.EnumerateFileSystemEntries parent
                        }

                    Expect.isTrue
                        ((Discovery.Spellings(reporting false)).SameEntry(requested, variant))
                        "A read that finished matches the one spelling it found."

                    Expect.isFalse
                        ((Discovery.Spellings(reporting true)).SameEntry(requested, variant))
                        "A read that did not finish matches nothing it did not see.")
            }
            test "an argument is checked exactly as it was given" {
                withDirectory (fun root ->
                    let file = write root "Foo.cs" "class C{int x;}"
                    let separator = string Path.DirectorySeparatorChar

                    Expect.throwsT<FileNotFoundException>
                        (fun () ->
                            Discovery.files [| file + separator |] None None false 1 |> ignore)
                        "A regular file named with a trailing separator names nothing."

                    Expect.equal
                        (Discovery.files [| root + separator |] None None false 1).Length
                        1
                        "A directory named with a trailing separator is still a directory."

                    if not (OperatingSystem.IsWindows()) && File.Exists "/dev/null" then
                        Expect.throwsT<FileNotFoundException>
                            (fun () ->
                                Discovery.files [| "/dev/NULL" |] None None false 1 |> ignore)
                            "A spelling the volume does not resolve still names nothing."

                    let variant = Path.Combine(root, "foo.cs")

                    if not caseSensitiveTemporaryVolume.Value then
                        let files = Discovery.files [| variant |] None None false 1

                        Expect.equal
                            (files |> Array.map (fun each -> each.Path))
                            [| variant |]
                            "A file is reported as the argument spelled it, not as the volume stores it.")
            }
            test "case-variant arguments naming one directory discover it once" {
                withDirectory (fun root ->
                    let stored = write root "Mixed/a.cs" "class A{}" |> Path.GetFullPath
                    write root "Mixed/deep/b.cs" "class B{}" |> ignore
                    let child = Path.GetDirectoryName stored
                    let variant = Path.Combine(root, "mixed")

                    if caseSensitiveTemporaryVolume.Value then
                        Expect.isFalse
                            (Directory.Exists variant)
                            "The variant is a different name."
                    else
                        for jobs in [ 1; 4 ] do
                            for roots in
                                [
                                    [| child; variant |]
                                    [| variant; child |]
                                    [| root; variant |]
                                    [| variant; child; root; child.ToUpperInvariant() |]
                                ] do
                                let files = Discovery.files roots None None false jobs
                                let paths = files |> Array.map (fun file -> file.Path)

                                Expect.equal
                                    paths.Length
                                    2
                                    $"Two files, reached by {roots.Length} roots at {jobs} jobs."

                                Expect.equal
                                    (Array.distinct paths)
                                    paths
                                    $"No file is discovered twice at {jobs} jobs."

                                let owner = roots[0]

                                for path in paths do
                                    Expect.stringStarts
                                        path
                                        owner
                                        "A path keeps the spelling of the root that found it."

                            let _, count = sharedDiscovery [| child; variant |] None jobs

                            Expect.equal
                                count
                                (if OperatingSystem.IsWindows() then 2 else 4)
                                "Both spellings and both their children are read.")
            }
            test "a later root spelling keeps its own ignore rules" {
                withDirectory (fun root ->
                    write root ".csffignore" "/Mixed/a.cs\n" |> ignore
                    let stored = write root "Mixed/a.cs" "class C { }\n" |> Path.GetFullPath
                    let child = Path.GetDirectoryName stored
                    let variant = Path.Combine(root, "mixed")

                    if caseSensitiveTemporaryVolume.Value then
                        skiptest "The temporary volume is case-sensitive;"

                    let files = Discovery.files [| child; variant |] None None false 1

                    Expect.equal
                        (files |> Array.map (fun file -> file.Path))
                        [| Path.Combine(variant, "a.cs") |]
                        "A file excluded under the first spelling is still found under the second."

                    Expect.equal
                        (files |> Array.map (fun file -> file.Root))
                        [| 1 |]
                        "The root that accepted it owns it.")
            }
            test "roots that name one cache file share one slot" {
                withDirectory (fun root ->
                    write root "a.cs" "class C { }\n" |> ignore

                    let roots = [| root; root |]
                    let files, cold = run roots true false false 1
                    allGood cold
                    Expect.equal files.Length 1 "One file, however many roots reach it."
                    Expect.isFalse cold[0].Cached "The cold run has nothing to hit."

                    let _, warm = run roots true false false 1
                    allGood warm
                    Expect.isTrue warm[0].Cached "The warm run hits what the cold one wrote."

                    Expect.equal
                        (Cache.read (cachePath root)).Count
                        1
                        "A root that owns no files must not empty the slot it shares."

                    let _, third = run roots true false false 1
                    Expect.isTrue third[0].Cached "And the run after the warm one still hits.")
            }
            test "shared discovery retains case-distinct directory listings" {
                withDirectory (fun root ->
                    let parent = Path.Combine(root, "sensitive")
                    Directory.CreateDirectory parent |> ignore

                    if
                        not (OperatingSystem.IsWindows()) && not caseSensitiveTemporaryVolume.Value
                    then
                        skiptest "The temporary volume is case-insensitive;"

                    if OperatingSystem.IsWindows() then
                        let start = ProcessStartInfo "fsutil.exe"

                        for arg in [ "file"; "setCaseSensitiveInfo"; parent; "enable" ] do
                            start.ArgumentList.Add arg

                        match Subprocess.run start with
                        | Subprocess.Exited(0, _, _) -> ()
                        | Subprocess.Exited(_, output, errors) ->
                            skiptest (
                                "Case-sensitive Windows directories unavailable: "
                                + output
                                + errors
                            )
                        | Subprocess.Timeout(output, errors) ->
                            skiptest ("fsutil did not exit: " + output + errors)

                    let a = write parent "Foo/a.cs" "class A{}" |> Path.GetFullPath
                    let b = write parent "foo/b.cs" "class B{}" |> Path.GetFullPath
                    let upper = Path.GetDirectoryName a
                    let lower = Path.GetDirectoryName b

                    Expect.isFalse
                        (File.Exists(Path.Combine(upper, "b.cs")))
                        "The directories are physically distinct."

                    for jobs in [ 1; 4 ] do
                        for roots, owners in
                            [
                                [| parent |], [| 0; 0 |]
                                [| parent; upper; lower |], [| 0; 0 |]
                                [| lower; upper; parent |], [| 1; 0 |]
                                [| upper; lower; parent |], [| 0; 1 |]
                                [| a; parent; b |], [| 0; 1 |]
                            ] do
                            let counts = ConcurrentDictionary<string, int>(StringComparer.Ordinal)

                            let enumerate directory =
                                seq {
                                    counts.AddOrUpdate(directory, 1, fun _ count -> count + 1)
                                    |> ignore

                                    yield! Discovery.enumerate directory
                                }

                            let files =
                                Discovery.filesWithEnumeration enumerate roots None None false jobs

                            Expect.equal
                                (files |> Array.map (fun file -> file.Path))
                                [| a; b |]
                                "Both actual listings survive."

                            Expect.equal
                                (files |> Array.map (fun file -> file.Root))
                                owners
                                "Argument order retains ownership."

                            Expect.equal
                                counts.Count
                                3
                                "Each case-distinct directory gets its own listing."

                            Expect.all
                                counts.Values
                                ((=) 1)
                                "Overlapping roots still share enumeration.")
            }
            test "shared discovery skips reparse descendants but retains explicit link roots" {
                withDirectory (fun root ->
                    write root "target/a.cs" "class A{}" |> ignore
                    let target = Path.Combine(root, "target")
                    let link = Path.Combine(root, "link")

                    try
                        if OperatingSystem.IsWindows() then
                            let start = ProcessStartInfo "cmd.exe"

                            for arg in [ "/d"; "/c"; "mklink"; "/J"; link; target ] do
                                start.ArgumentList.Add arg

                            match Subprocess.run start with
                            | Subprocess.Exited(code, output, errors) ->
                                Expect.equal code 0 (output + errors)
                            | Subprocess.Timeout(output, errors) ->
                                failtest ("mklink did not exit: " + output + errors)
                        else
                            Directory.CreateSymbolicLink(link, target) |> ignore

                        for jobs in [ 1; 4 ] do
                            let files, count = sharedDiscovery [| root; target; root |] None jobs
                            Expect.equal files.Length 1 "Walking skips the link descendant."
                            Expect.equal count 2 "A reparse descendant is never enumerated."

                            for roots in [ [| root; link; target |]; [| link; root; target |] ] do
                                let files, count = sharedDiscovery roots None jobs

                                Expect.equal
                                    files.Length
                                    2
                                    "An explicit link root retains its original discovery semantics."

                                Expect.equal
                                    count
                                    3
                                    "Only explicit link arguments enumerate the reparse directory."
                    finally
                        if Directory.Exists link then
                            Directory.Delete link)
            }
            test "shared discovery preserves case-sensitive rules for Windows path aliases" {
                if OperatingSystem.IsWindows() then
                    withDirectory (fun root ->
                        write root "Mixed/a.cs" "class A{}" |> ignore
                        write root "Mixed/b.cs" "class B{}" |> ignore
                        write root ".csffignore" "/Mixed/a.cs\n" |> ignore

                        write
                            root
                            ".csffrc.json"
                            "{\"overrides\":[{\"files\":\"Mixed/b.cs\",\"printWidth\":80}]}"
                        |> ignore

                        let child = Path.Combine(root, "Mixed")
                        let alias = child.ToUpperInvariant()
                        let custom = write root "custom.ignore" "/Mixed/a.cs\n"

                        for jobs in [ 1; 4 ] do
                            for ignorePath in [ None; Some custom ] do
                                for roots in [ [| root; alias; child |]; [| alias; root; child |] ] do
                                    let _, count = sharedDiscovery roots ignorePath jobs

                                    Expect.equal
                                        count
                                        2
                                        "Case-sensitive rules share only physical enumeration.")
            }
            test "discovery shares deep metadata and sections within an allocation budget" {
                withDirectory (fun root ->
                    let mutable directory = root

                    for level in 1..16 do
                        write
                            directory
                            ".editorconfig"
                            ((if level = 1 then "root = true\n" else "")
                             + String.replicate 4 "[*.cs]\nindent_size = 2\n")
                        |> ignore

                        if level <> 16 then
                            directory <- Path.Combine(directory, "d")
                            Directory.CreateDirectory directory |> ignore

                    let roots = Array.init 64 (fun i -> write directory $"f{i}.cs" "class C{}")
                    discover roots |> ignore
                    let before = GC.GetAllocatedBytesForCurrentThread()
                    let files = discover roots
                    let allocated = GC.GetAllocatedBytesForCurrentThread() - before
                    printfn "deep discovery: %d files, %d bytes" files.Length allocated
                    Expect.equal files.Length roots.Length "Every explicit file is retained."

                    Expect.isLessThan allocated 8_000_000L "Metadata is shared within one request.")
            }
            test "discovery single-flights normalized directory states and shares parent groups" {
                withDirectory (fun root ->
                    write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 2\n" |> ignore
                    let path = write root "sub/a.cs" "class C{}"
                    let directory = Path.GetDirectoryName path
                    write directory ".editorconfig" "[a.cs]\nmax_line_length = 80\n" |> ignore
                    let context = Discovery.Context(true, true)
                    let states = Array.zeroCreate<DirectorySettings> 64
                    let caseVariants = not caseSensitiveTemporaryVolume.Value

                    Parallel.For(
                        0,
                        states.Length,
                        ParallelOptions(MaxDegreeOfParallelism = 4),
                        Action<int>(fun i ->
                            let alias =
                                if i % 2 = 0 then Path.Combine(directory, ".")
                                elif caseVariants then directory.ToUpperInvariant()
                                else directory + string Path.DirectorySeparatorChar

                            states[i] <- context.Inherited alias)
                    )
                    |> ignore

                    for i = 0 to states.Length - 1 do
                        let expected = if caseVariants then states[i % 2] else states[0]

                        Expect.isTrue
                            (obj.ReferenceEquals(states[i], expected))
                            "Contending calls with one normalized spelling share the published state."

                    if caseVariants then
                        Expect.isFalse
                            (obj.ReferenceEquals(states[0], states[1]))
                            "Casing aliases retain independently scoped metadata."

                    let group = states[0].Editor.Value
                    let parent = (context.Inherited root).Editor.Value

                    Expect.isTrue
                        (obj.ReferenceEquals(group.Parent.Value, parent))
                        "A child links to the parent's group without copying its sections."

                    write root ".editorconfig" "[[*.cs]\n" |> ignore
                    write root ".csffrc.json" "{" |> ignore
                    write root ".csffignore" "[\n" |> ignore
                    write root ".gitignore" "[\n" |> ignore
                    let child = Path.Combine(directory, "child")
                    Directory.CreateDirectory child |> ignore
                    let inherited = context.Inherited child

                    Expect.isTrue
                        (obj.ReferenceEquals(inherited.Editor.Value, group))
                        "Cached metadata, including absence, remains fixed within the request.")
            }
            test "a malformed editorconfig section matches nothing instead of ending the run" {
                for malformed in
                    [
                        "*.{slnx,csproj,vbproj"
                        "[*.cs"
                        "{a,b"
                        "*.{a,{b}"
                        "{1.." + String('9', 129) + "}"
                    ] do
                    for jobs in [ 1; 4 ] do
                        withDirectory (fun root ->
                            let file = write root "a.cs" "class A{}"

                            write
                                root
                                ".editorconfig"
                                $"root = true\n[*.cs]\nmax_line_length = 70\n[{malformed}]\nmax_line_length = 40\n"
                            |> ignore

                            let files = Discovery.files [| file |] None None false jobs

                            Expect.equal
                                files.Length
                                1
                                $"%s{malformed}: the run reaches the file at all."

                            Expect.equal
                                files[0].Settings.Printer.Width
                                70
                                $"%s{malformed}: a malformed section matches nothing.")
            }
            test "a malformed pattern in a csff-owned config is still rejected" {
                withDirectory (fun root ->
                    let file = write root "a.cs" "class A{}"

                    write
                        root
                        ".csffrc.json"
                        """{"overrides":[{"files":"*.{cs","printWidth":40}]}"""
                    |> ignore

                    Expect.throws
                        (fun () -> Discovery.files [| file |] None None false 1 |> ignore)
                        "A csff-owned config rejects a malformed pattern.")
            }
            test "discovery observes configuration and ignore edits on the next request" {
                for jobs in [ 1; 4 ] do
                    withDirectory (fun root ->
                        let a = write root "a.cs" "class A{}"
                        let b = write root "b.cs" "class B{}"
                        let roots = [| a; b |]

                        let files () =
                            Discovery.files roots None None false jobs

                        let widths () =
                            files () |> Array.map (fun file -> file.Settings.Printer.Width)

                        Expect.equal (widths ()) [| 100; 100 |] "Initial missing configuration."
                        let config = write root ".csffrc.json" "{\"printWidth\":80}"
                        Expect.equal (widths ()) [| 80; 80 |] "A formerly absent config is read."

                        write
                            root
                            ".csffrc.json"
                            "{\"printWidth\":60,\"overrides\":[{\"files\":\"b.cs\",\"printWidth\":40}]}"
                        |> ignore

                        Expect.equal
                            (widths ())
                            [| 60; 40 |]
                            "Overrides still match each filename."

                        File.Delete config

                        write
                            root
                            ".editorconfig"
                            "root = true\n[*.cs]\nmax_line_length = 70\n[b.cs]\nmax_line_length = unset\n"
                        |> ignore

                        Expect.equal
                            (widths ())
                            [| 70; 100 |]
                            "EditorConfig sections and unset apply."

                        write root ".editorconfig" "root = true\n[*.cs]\nmax_line_length = 90\n"
                        |> ignore

                        Expect.equal (widths ()) [| 90; 90 |] "EditorConfig edits are not stale."
                        let csff = write root ".csffignore" "a.cs\n"

                        Expect.equal
                            (files () |> Array.map (fun file -> file.Path))
                            [| b |]
                            "New ignore."

                        write root ".csffignore" "b.cs\n" |> ignore

                        Expect.equal
                            (files () |> Array.map (fun file -> file.Path))
                            [| a |]
                            "Edited ignore."

                        File.Delete csff
                        write root ".gitignore" "a.cs\n" |> ignore

                        Expect.equal
                            (files () |> Array.map (fun file -> file.Path))
                            [| b |]
                            "New Git ignore."

                        write root ".gitignore" "b.cs\n" |> ignore

                        Expect.equal
                            (files () |> Array.map (fun file -> file.Path))
                            [| a |]
                            "Edited Git ignore.")
            }
            test "parallel discovery anchors custom ignores separately for overlapping roots" {
                withDirectory (fun root ->
                    write root "a.cs" "class A{}" |> ignore
                    let nested = write root "sub/a.cs" "class B{}"
                    let custom = write root "custom.ignore" "/a.cs\n"
                    let roots = [| root; Path.GetDirectoryName nested |]

                    for jobs in [ 1; 4 ] do
                        let files = Discovery.files roots None (Some custom) false jobs

                        Expect.equal
                            (files |> Array.map (fun file -> file.Path))
                            [| Path.GetFullPath nested |]
                            "Each root anchors its custom ignore."

                        Expect.equal files[0].Root 0 "The first root owns overlapping inputs.")
            }
            test "parallel discovery preserves overlapping root ownership and error order" {
                withDirectory (fun root ->
                    write root "a.cs" "class A{}" |> ignore
                    write root "sub/b.cs" "class B{}" |> ignore
                    let roots = [| root; Path.Combine(root, "sub") |]
                    let sequential = Discovery.files roots None None false 1
                    let concurrent = Discovery.files roots None None false 4
                    Expect.equal concurrent sequential "Input order owns overlapping paths."

                    Expect.equal
                        (concurrent |> Array.map (fun file -> file.Root))
                        [| 0; 0 |]
                        "No duplicate roots."

                    let missing = [| Path.Combine(root, "first"); Path.Combine(root, "second") |]

                    try
                        Discovery.files missing None None false 4 |> ignore
                        failtest "Missing roots must fail discovery."
                    with :? FileNotFoundException as error ->
                        Expect.equal error.FileName missing[0] "Report the first input failure.")
            }
            test "parallel discovery reports configuration failures in root order" {
                withDirectory (fun root ->
                    let first = write root "first/a.cs" "class A{}"
                    let second = write root "second/b.cs" "class B{}"
                    write root "first/.csffrc.json" "{\"first\":1}" |> ignore
                    write root "second/.csffrc.json" "{\"second\":1}" |> ignore

                    for jobs in [ 1; 4 ] do
                        for roots, setting in
                            [ [| first; second |], "first"; [| second; first |], "second" ] do
                            try
                                Discovery.files roots None None false jobs |> ignore
                                failtest "Malformed configuration must fail discovery."
                            with :? ArgumentException as error ->
                                Expect.stringContains
                                    error.Message
                                    ("Unknown csff setting: " + setting)
                                    "The first argument owns the reported failure.")
            }
            test "parallel discovery bounds active workers across nested subdirectories" {
                withDirectory (fun root ->
                    for a in [ "0"; "1" ] do
                        for b in [ "0"; "1" ] do
                            for c in [ "0"; "1" ] do
                                for d in [ "0"; "1" ] do
                                    write root $"{a}/{b}/{c}/{d}/file.cs" "class C{}" |> ignore

                    for jobs in [ 1; 2; 3 ] do
                        let gate = obj ()
                        let mutable active = 0
                        let mutable peak = 0

                        let enumerate directory =
                            lock gate (fun () ->
                                active <- active + 1
                                peak <- max peak active)

                            try
                                Thread.Sleep 5
                                Discovery.enumerate directory |> Seq.toArray :> seq<_>
                            finally
                                lock gate (fun () -> active <- active - 1)

                        let files =
                            Discovery.filesWithEnumeration
                                enumerate
                                [| root |]
                                None
                                None
                                false
                                jobs

                        Expect.equal files.Length 16 "Every leaf file is discovered."

                        Expect.isLessThanOrEqual
                            peak
                            jobs
                            $"Peak active directory enumerations ({peak}) must not exceed jobs ({jobs}).")
            }
            test "parallel discovery does not re-enter overlapping roots when child walks block" {
                withDirectory (fun root ->
                    let x = write root "src/a/x.cs" "class X{}" |> Path.GetFullPath
                    let y = write root "src/b/y.cs" "class Y{}" |> Path.GetFullPath
                    let src = Path.Combine(root, "src")
                    let subA = Path.Combine(src, "a")

                    let enumerate directory =
                        if String.Equals(directory, subA, StringComparison.Ordinal) then
                            Thread.Sleep 20

                        Discovery.enumerate directory

                    for jobs in [ 2; 3; 4 ] do
                        let files =
                            Discovery.filesWithEnumeration
                                enumerate
                                [| src; root |]
                                None
                                None
                                false
                                jobs

                        Expect.equal
                            (files |> Array.map (fun file -> file.Path))
                            [| x; y |]
                            "Overlapping roots complete without re-entering cached Lazy walks."

                        Expect.equal
                            (files |> Array.map (fun file -> file.Root))
                            [| 0; 0 |]
                            "The first root retains ownership of overlapping descendants.")
            }
            test "discovery honors symlinked metadata files in walked child directories" {
                if not (OperatingSystem.IsWindows()) then
                    withDirectory (fun root ->
                        write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 4\n"
                        |> ignore

                        let sharedEditor =
                            write root "shared/editorconfig" "[*.cs]\nindent_size = 2\n"

                        let sharedIgnore = write root "shared/gitignore" "ignored.cs\n"
                        let kept = write root "sub/kept.cs" "class Kept{}" |> Path.GetFullPath
                        write root "sub/ignored.cs" "class Ignored{}" |> ignore
                        let sub = Path.Combine(root, "sub")

                        File.CreateSymbolicLink(Path.Combine(sub, ".editorconfig"), sharedEditor)
                        |> ignore

                        File.CreateSymbolicLink(Path.Combine(sub, ".gitignore"), sharedIgnore)
                        |> ignore

                        for jobs in [ 1; 4 ] do
                            let files = Discovery.files [| root |] None None false jobs

                            Expect.equal
                                (files |> Array.map (fun file -> file.Path))
                                [| kept |]
                                "Symlinked .gitignore in a walked child directory is applied."

                            Expect.equal
                                files[0].Settings.Printer.IndentSize
                                2
                                "Symlinked .editorconfig in a walked child directory is applied.")
            }
            test "CLI checks, writes, and then checks without changing file or cache timestamps" {
                withDirectory (fun root ->
                    let path = write root "src/a.cs" "class C{}"
                    let roots = [| root |]
                    let first = check roots
                    allGood first
                    Expect.isTrue first[0].Changed "Check reports the diff."
                    Expect.equal (File.ReadAllText path) "class C{}" "Check cannot rewrite source."
                    Expect.isFalse first[0].Cacheable "An unformatted input is never a cache hit."
                    let _, formatted = run roots false false false 2
                    allGood formatted

                    Expect.equal
                        (File.ReadAllText path)
                        "class C { }\n"
                        "Format writes the printer's output."

                    let stamp = DateTime(2001, 1, 1, 0, 0, 0, DateTimeKind.Utc)
                    let cache = cachePath root
                    File.SetLastWriteTimeUtc(path, stamp)
                    File.SetLastWriteTimeUtc(cache, stamp)
                    let warm = check roots
                    Expect.isTrue warm[0].Cached "Written output populates the cache."
                    Expect.equal (File.GetLastWriteTimeUtc path) stamp "No source rewrite."
                    Expect.equal (File.GetLastWriteTimeUtc cache) stamp "No no-op cache rewrite.")
            }
            test "CLI cache keys content across renames and duplicate files, and separates roots" {
                withDirectory (fun root ->
                    let one = Path.Combine(root, "one")
                    let two = Path.Combine(root, "two")
                    let path = write one "a.cs" "class C { }\n"
                    write two "b.cs" "class C { }\n" |> ignore
                    check [| one |] |> allGood
                    File.Move(path, Path.Combine(one, "renamed.cs"))
                    write one "duplicate.cs" "class C { }\n" |> ignore
                    let warm = check [| one |]
                    Expect.all warm (fun result -> result.Cached) "Content survives renames."

                    Expect.equal
                        (Cache.read (cachePath one)).Count
                        1
                        "Duplicate content has one entry."

                    let separate = check [| two |]
                    Expect.isFalse separate[0].Cached "Another input root has its own cache."
                    Expect.notEqual (cachePath one) (cachePath two) "Root scopes differ.")
            }
            test "CLI cache detects changed bytes despite unchanged size and timestamp" {
                withDirectory (fun root ->
                    let path = write root "a.cs" "class C { }\n"
                    check [| root |] |> allGood
                    let stamp = File.GetLastWriteTimeUtc path
                    File.WriteAllText(path, "class D { }\n")
                    File.SetLastWriteTimeUtc(path, stamp)
                    Expect.isFalse ((check [| root |]).[0].Cached) "Hash actual input bytes.")
            }
            test "CLI cache retains CR entries alongside other line endings" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "cache")
                    let entries = HashSet<CacheKey>()
                    let digest = Array.zeroCreate<byte> 32

                    for ending in [ EndOfLine.Lf; EndOfLine.CrLf; EndOfLine.Cr ] do
                        for auto in [ true; false ] do
                            for tabs in [ true; false ] do
                                for generated in [ true; false ] do
                                    let settings =
                                        { Settings.Default with
                                            AutoEndOfLine = auto
                                            Printer =
                                                { PrinterOptions.Default with
                                                    EndOfLine = ending
                                                    UseTabs = tabs
                                                }
                                        }

                                    entries.Add(
                                        Cache.key (ReadOnlySpan<byte> digest) settings generated
                                    )
                                    |> ignore

                    Cache.save path (HashSet<CacheKey>()) entries

                    Expect.isTrue
                        (entries.SetEquals(Cache.read path))
                        "Every supported flags combination survives reload.")
            }
            test "automatic EOL overrides use a canonical cache key" {
                withDirectory (fun root ->
                    for ending in [ "lf"; "crlf"; "cr" ] do
                        let content =
                            "{\"endOfLine\":\""
                            + ending
                            + "\",\"overrides\":[{\"files\":\"special.cs\",\"endOfLine\":\"auto\"}]}"

                        let config = Configuration.read (write root ".csffrc.json" content)

                        let settings =
                            Configuration.forFile (Some config) (Path.Combine(root, "special.cs"))

                        let digest = ReadOnlySpan<byte>(Array.zeroCreate<byte> 32)

                        Expect.equal
                            (Cache.key digest settings false)
                            (Cache.key digest Settings.Default false)
                            "Equivalent auto settings are independent of the inherited fixed EOL.")
            }
            test "CLI cache invalidates resolved configuration and generated policy" {
                withDirectory (fun root ->
                    write root "a.cs" "class C { }\n" |> ignore
                    check [| root |] |> allGood
                    write root ".csffrc.json" "{\"printWidth\":80}" |> ignore
                    Expect.isFalse ((check [| root |]).[0].Cached) "Width participates in the key."
                    let _, results = run [| root |] true false true 1
                    Expect.isFalse results[0].Cached "Generated inclusion participates in the key.")
            }
            test
                "CLI prunes stale cache entries, truncates shorter snapshots, and tolerates corruption" {
                withDirectory (fun root ->
                    write root "a.cs" "class A { }\n" |> ignore
                    let second = write root "b.cs" "class B { }\n"
                    check [| root |] |> allGood
                    let path = cachePath root
                    let length = FileInfo(path).Length
                    File.Delete second
                    check [| root |] |> allGood

                    Expect.isLessThan
                        (FileInfo(path).Length)
                        length
                        "Replace with a shorter snapshot."

                    Expect.equal (Cache.read path).Count 1 "No stale tail or removed content."
                    File.AppendAllText(path, "stale tail")
                    Expect.isFalse ((check [| root |]).[0].Cached) "Corrupted cache is rebuilt."
                    let bytes = File.ReadAllBytes path
                    bytes[36] <- bytes[36] ^^^ 1uy
                    File.WriteAllBytes(path, bytes)
                    Expect.equal (Cache.read path).Count 0 "Validate the payload checksum.")
            }
            test "a cancelled run banks the files it finished" {
                withDirectory (fun root ->
                    let count = 48

                    let body = String.replicate 400 "    void M(){int x=1;x++;if(x>0){x--;}}\n"

                    let paths =
                        Array.init count (fun index ->
                            let name = "f" + string index + ".cs"
                            write root name ("class C" + string index + "{\n" + body + "}\n"))

                    let lengths = paths |> Array.map (fun path -> FileInfo(path).Length)
                    let files = discover [| root |]
                    use cancellation = new CancellationTokenSource()
                    let mutable running = true

                    let watcher =
                        Thread(fun () ->
                            let timer = Stopwatch.StartNew()
                            let mutable waiting = true

                            while waiting && running && timer.Elapsed.TotalSeconds < 60.0 do
                                for index = 0 to paths.Length - 1 do
                                    if
                                        waiting && FileInfo(paths[index]).Length <> lengths[index]
                                    then
                                        waiting <- false

                            cancellation.Cancel())

                    watcher.IsBackground <- true
                    watcher.Start()
                    let mutable cancelled = false

                    try
                        try
                            Formatter.run
                                [| root |]
                                files
                                false
                                false
                                false
                                1
                                None
                                cancellation.Token
                            |> ignore
                        with :? OperationCanceledException ->
                            cancelled <- true
                    finally
                        running <- false
                        watcher.Join()

                    Expect.isTrue cancelled "The run stopped on cancellation."

                    let banked = (Cache.read (cachePath root)).Count
                    Expect.isGreaterThan banked 0 "Finished files reach the cache."
                    Expect.isLessThanOrEqual banked count "No entry is invented."

                    let rerun = check [| root |]

                    let credited =
                        rerun |> Array.filter (fun result -> result.Cached) |> Array.length

                    Expect.isGreaterThan credited 0 "The next run collects the credit.")
            }
            test "a cancelled run keeps the entries it never revisited" {
                withDirectory (fun root ->
                    write root "a.cs" "class A { }\n" |> ignore
                    write root "b.cs" "class B { }\n" |> ignore
                    check [| root |] |> allGood
                    let path = cachePath root
                    Expect.equal (Cache.read path).Count 2 "A complete run caches both."

                    use cancellation = new CancellationTokenSource()
                    cancellation.Cancel()
                    let files = discover [| root |]

                    Expect.throwsT<OperationCanceledException>
                        (fun () ->
                            Formatter.run
                                [| root |]
                                files
                                true
                                false
                                false
                                2
                                None
                                cancellation.Token
                            |> ignore)
                        "Cancellation still reaches the caller."

                    Expect.equal
                        (Cache.read path).Count
                        2
                        "A run that claimed nothing evicts nothing.")
            }
            test "CLI cache rejects oversized and stale version snapshots" {
                withDirectory (fun root ->
                    let path = Path.Combine(root, "cache")
                    let empty = HashSet<CacheKey>()

                    let full =
                        HashSet<CacheKey>(
                            [| for index in 1 .. Cache.MaximumEntries -> key index |]
                        )

                    Cache.save path empty full

                    Expect.equal
                        (Cache.read path).Count
                        Cache.MaximumEntries
                        "The bound is readable."

                    full.Add(key (Cache.MaximumEntries + 1)) |> ignore

                    Expect.throws
                        (fun () -> Cache.save path empty full)
                        "Never persist an unbounded cache."

                    let bytes = File.ReadAllBytes path
                    bytes[0] <- bytes[0] ^^^ 1uy
                    File.WriteAllBytes(path, bytes)

                    Expect.equal
                        (Cache.read path).Count
                        0
                        "Old formatter versions cannot produce hits.")
            }
            test "CLI no-cache neither reads nor writes" {
                withDirectory (fun root ->
                    write root "a.cs" "class C { }\n" |> ignore
                    let _, results = run [| root |] true true false 1
                    Expect.isFalse results[0].Cached "No hit without a cache."
                    Expect.isFalse (File.Exists(cachePath root)) "No cache created."
                    check [| root |] |> allGood
                    let cache = File.ReadAllBytes(cachePath root)
                    let _, results = run [| root |] true true false 1
                    Expect.isFalse results[0].Cached "An existing cache is bypassed."

                    Expect.equal
                        (File.ReadAllBytes(cachePath root))
                        cache
                        "Existing cache is untouched.")
            }
            test "CLI honors nested gitignore, csffignore priority, negation and anchored rules" {
                withDirectory (fun root ->
                    write root ".gitignore" "ignored/\n*.skip.cs\n/root.cs\n" |> ignore
                    write root ".csffignore" "!keep.skip.cs\n" |> ignore
                    write root "sub/.gitignore" "!nested.skip.cs\n" |> ignore

                    for name in
                        [
                            "a.cs"
                            "keep.skip.cs"
                            "drop.skip.cs"
                            "root.cs"
                            "sub/root.cs"
                            "sub/nested.skip.cs"
                            "ignored/keep.cs"
                            "bin/b.cs"
                            "obj/o.cs"
                            "node_modules/n.cs"
                            "third_party/v.cs"
                            "test.csproj"
                        ] do
                        write root name "class C{}" |> ignore

                    let names =
                        discover [| root |]
                        |> Array.map (fun file ->
                            Path.GetRelativePath(root, file.Path).Replace('\\', '/'))

                    Expect.equal
                        names
                        [|
                            "a.cs"
                            "keep.skip.cs"
                            "sub/nested.skip.cs"
                            "sub/root.cs"
                            "third_party/v.cs"
                        |]
                        "Rules resolve from the file's directory."

                    write root ".csffignore" "third_party/\n" |> ignore

                    Expect.isFalse
                        (discover [| root |]
                         |> Array.exists (fun file ->
                             file.Path.EndsWith("v.cs", StringComparison.Ordinal)))
                        "Respect the vendored barrier.")
            }
            test "CLI generated-directory names above the repository do not exclude it" {
                for name in [ ".git"; "bin"; "obj"; "node_modules"; ".cache" ] do
                    for worktree in [ false; true ] do
                        withDirectory (fun root ->
                            File.Delete(Path.Combine(root, ".git"))
                            let repository = Path.Combine(root, name, "repo")

                            if worktree then
                                write repository ".git" "gitdir: /fixture" |> ignore
                            else
                                Directory.CreateDirectory(Path.Combine(repository, ".git"))
                                |> ignore

                            let path = write repository "sub/a.cs" "class C{}" |> Path.GetFullPath
                            write repository "bin/b.cs" "class B{}" |> ignore

                            for input in [ repository; Path.GetDirectoryName path; path ] do
                                Expect.equal
                                    (discover [| input |] |> Array.map (fun file -> file.Path))
                                    [| path |]
                                    "Only ignored directory names inside this repository are barriers.")
            }
            test "CLI nested csffignore cannot bypass an excluded ancestor" {
                for local in [ ""; "!a.cs\n" ] do
                    withDirectory (fun root ->
                        write root ".csffignore" "blocked/\n" |> ignore
                        write root "blocked/.csffignore" local |> ignore
                        write root "blocked/sub/.csffignore" "" |> ignore
                        let direct = write root "blocked/a.cs" "class C{}"
                        let nested = write root "blocked/sub/b.cs" "class B{}"

                        for input in
                            [
                                root
                                Path.GetDirectoryName direct
                                direct
                                Path.GetDirectoryName nested
                                nested
                            ] do
                            Expect.isEmpty
                                (discover [| input |])
                                "An ignore file below an excluded directory cannot reinclude it.")
            }
            test "CLI ancestor barriers do not force overridden configuration" {
                withDirectory (fun root ->
                    write root ".csffrc.json" "{" |> ignore
                    write root "sub/.csffrc.json" "{\"indentSize\":2}" |> ignore
                    let path = write root "sub/nested/a.cs" "class C{}"

                    for input in [ path; Path.GetDirectoryName path ] do
                        let files = discover [| input |]
                        Expect.equal files.Length 1 "The source passes ancestor ignore barriers."

                        Expect.equal
                            files[0].Settings.Printer.IndentSize
                            2
                            "The nearer config wins.")
            }
            test "CLI csffignore barriers above a nested repository still apply" {
                for worktree in [ false; true ] do
                    withDirectory (fun root ->
                        write root ".csffignore" "blocked/\n" |> ignore
                        let repository = Path.Combine(root, "blocked", "repo")

                        if worktree then
                            write repository ".git" "gitdir: /fixture" |> ignore
                        else
                            Directory.CreateDirectory(Path.Combine(repository, ".git")) |> ignore

                        let path = write repository "sub/a.cs" "class C{}"

                        for input in [ root; repository; Path.GetDirectoryName path; path ] do
                            Expect.isEmpty
                                (discover [| input |])
                                "Applicable csffignore barriers survive Git-root boundaries.")
            }
            for name in [ "ignored"; "bin"; "obj"; "excluded" ] do
                test $"CLI directory roots obey ignore barriers for {name}" {
                    withDirectory (fun root ->
                        write root ".gitignore" "ignored/\n" |> ignore
                        write root ".csffignore" "excluded/\n" |> ignore
                        let direct = write root ($"{name}/a.cs") "class C{}"
                        let nested = write root ($"{name}/sub/b.cs") "class D{}"

                        Expect.isEmpty
                            (discover [| root |])
                            "Recursive discovery prunes the directory."

                        for path in [ direct; nested ] do
                            Expect.isEmpty (discover [| path |]) "Explicit files obey the barrier."

                            Expect.isEmpty
                                (discover [| Path.GetDirectoryName path |])
                                "A directory argument cannot bypass its own or an ancestor's barrier."

                        if name = "ignored" then
                            let worktree = Path.Combine(root, "nested")
                            write worktree ".git" "gitdir: /fixture" |> ignore
                            let included = write worktree "ignored/a.cs" "class C{}"

                            Expect.equal
                                (discover [| Path.GetDirectoryName included |]
                                 |> Array.map (fun file -> file.Path))
                                [| Path.GetFullPath included |]
                                "Directory roots stop Git ignores at the nearest worktree."

                            let custom = write root "custom.ignore" "b.cs\n"

                            Expect.equal
                                (Discovery.files
                                    [| Path.GetDirectoryName direct |]
                                    None
                                    (Some custom)
                                    false
                                    1
                                 |> Array.map (fun file -> file.Path))
                                [| Path.GetFullPath direct |]
                                "Explicit ignores replace discovered barriers and remain anchored at the input root.")
                }
            for name in [ ".gitignore"; ".csffignore" ] do
                test $"CLI dot-star ignores apply only to descendants for {name}" {
                    withDirectory (fun root ->
                        let direct = write root "a.cs" "class C{}" |> Path.GetFullPath
                        let nested = write root "sub/b.cs" "class D{}" |> Path.GetFullPath
                        let sub = Path.GetDirectoryName nested

                        for directory in [ root; sub ] do
                            write directory name ".*\n" |> ignore
                            write directory ".hidden.cs" "class Hidden{}" |> ignore
                            write directory ".hidden/c.cs" "class Hidden{}" |> ignore

                        for input, expected in
                            [
                                root, [| direct; nested |]
                                sub, [| nested |]
                                direct, [| direct |]
                                nested, [| nested |]
                            ] do
                            Expect.equal
                                (discover [| input |] |> Array.map (fun file -> file.Path))
                                expected
                                "An ignore file cannot exclude its own directory or ordinary descendants."

                        for directory in [ root; sub ] do
                            for relative in [ ".hidden.cs"; ".hidden"; ".hidden/c.cs" ] do
                                Expect.isEmpty
                                    (discover [| Path.Combine(directory, relative) |])
                                    "Hidden descendants still obey the ignore barrier.")
                }
            test "CLI explicit files obey ignored ancestors and worktree boundaries" {
                withDirectory (fun root ->
                    write root ".gitignore" "ignored/\n" |> ignore
                    let ignored = write root "ignored/a.cs" "class C{}"

                    Expect.isEmpty
                        (discover [| ignored |])
                        "An ignored directory cannot be reintroduced by a file argument."

                    let nested = Path.Combine(root, "nested")
                    write nested ".git" "gitdir: /fixture" |> ignore
                    let included = write nested "ignored/a.cs" "class C{}" |> Path.GetFullPath

                    Expect.equal
                        (discover [| included |]).Length
                        1
                        "Stop Git ignores at the nearest worktree."

                    Expect.isTrue
                        (discover [| root |] |> Array.exists (fun file -> file.Path = included))
                        "Nested worktrees also stop inherited Git ignores during walking.")
            }
            test "CLI custom ignore overrides discovered ignores throughout the walk" {
                withDirectory (fun root ->
                    write root ".gitignore" "*.cs\n" |> ignore
                    write root "sub/.gitignore" "*.cs\n" |> ignore
                    let custom = write root "custom.ignore" "drop.cs\n"
                    write root "sub/keep.cs" "class C{}" |> ignore
                    write root "sub/drop.cs" "class C{}" |> ignore
                    let files = Discovery.files [| root |] None (Some custom) false 1
                    Expect.equal files.Length 1 "Nested ignores cannot replace --ignore-path."

                    Expect.equal
                        (Path.GetFileName files[0].Path)
                        "keep.cs"
                        "Custom patterns are anchored at the input root.")
            }
            test "CLI globs include double stars, character classes and escaped special characters" {
                withDirectory (fun root ->
                    write root ".gitignore" "**/skip[0-9].cs\n\\#hash.cs\n\\!bang.cs\n" |> ignore

                    for path in [ "a/skip1.cs"; "skip2.cs"; "a/skipx.cs"; "#hash.cs"; "!bang.cs" ] do
                        write root path "class C{}" |> ignore

                    let files = discover [| root |]
                    Expect.equal files.Length 1 "Git-style glob rules apply."

                    Expect.equal
                        (Path.GetFileName files[0].Path)
                        "skipx.cs"
                        "Character class doesn't match x.")
            }
            test "configuration nulls and missing override patterns have explicit validation errors" {
                withDirectory (fun root ->
                    for content, expected in
                        [
                            "endOfLine:\n", "endOfLine must be a string"
                            "{\"endOfLine\":null}", "endOfLine must be a string"
                            "overrides:\n  - files:\n", "overrides.files must be a string"
                            "{\"overrides\":[{\"files\":null}]}",
                            "overrides.files must be a string"
                            "overrides:\n  - files: '*.cs'\n    formatter:\n",
                            "overrides.formatter must be a string"
                            "{\"overrides\":[{\"files\":\"*.cs\",\"formatter\":null}]}",
                            "overrides.formatter must be a string"
                            "overrides:\n  - printWidth: 40\n", "override requires a files pattern"
                            "{\"overrides\":[{\"printWidth\":40}]}",
                            "override requires a files pattern"
                            "overrides:\n", "overrides must be an array"
                            "{\"overrides\":[null]}", "overrides must contain objects"
                        ] do
                        let path = write root ".csffrc.yaml" content

                        try
                            Configuration.read path |> ignore
                            failtest "An invalid configuration must be rejected."
                        with :? ArgumentException as error ->
                            Expect.stringContains
                                error.Message
                                expected
                                "The error identifies the invalid setting.")
            }
            test "CLI treats an unreadable string setting as a usage error and writes nothing" {
                for content, expected in
                    [
                        "endOfLine:\n", "endOfLine must be a string"
                        "overrides:\n  - files:\n", "overrides.files must be a string"
                        "overrides:\n  - files: '*.cs'\n    formatter:\n",
                        "overrides.formatter must be a string"
                        "overrides:\n  - printWidth: 40\n", "override requires a files pattern"
                    ] do
                    withDirectory (fun root ->
                        let source = "class C{int x;}"
                        let path = write root "a.cs" source
                        write root ".csffrc.yaml" content |> ignore
                        write root ".git" "gitdir: /fixture" |> ignore

                        let code, _, errors = capture (fun () -> Program.run [| path |])

                        Expect.equal code 2 "An unreadable configuration is a usage error."
                        Expect.stringContains errors expected "The CLI names the invalid setting."

                        Expect.equal
                            (File.ReadAllText path)
                            source
                            "A configuration error formats nothing.")
            }
            test "CLI selects nearest JSON or YAML configuration and honors overrides" {
                withDirectory (fun root ->
                    write
                        root
                        ".csffrc.json"
                        "{\"printWidth\":80,\"overrides\":[{\"files\":\"**/special.cs\",\"formatter\":\"csharp\",\"printWidth\":40}]}"
                    |> ignore

                    write root "a.cs" "class C{}" |> ignore
                    write root "special.cs" "class C{}" |> ignore

                    write
                        root
                        "sub/.csffrc.yaml"
                        "printWidth: 60\nuseTabs: true\nindentSize: 2\nendOfLine: crlf\n"
                    |> ignore

                    write root "sub/b.cs" "class C{}" |> ignore
                    let files = discover [| root |]

                    Expect.equal
                        (files |> Array.map (fun file -> file.Settings.Printer.Width))
                        [| 80; 40; 60 |]
                        "Nearest config and last matching override win."

                    Expect.isTrue files[2].Settings.Printer.UseTabs "Read YAML booleans."
                    Expect.equal files[2].Settings.Printer.IndentSize 2 "Read YAML integers."

                    Expect.equal
                        files[2].Settings.Printer.EndOfLine
                        EndOfLine.CrLf
                        "Read YAML line endings."

                    Expect.throws
                        (fun () ->
                            Configuration.read (write root "invalid.json" "{\"printWidth\":0}")
                            |> ignore)
                        "Invalid options cannot enter formatting.")
            }
            test "CLI applies an override as a delta on the configuration it belongs to" {
                withDirectory (fun root ->
                    let configurations =
                        [
                            ".csffrc.json",
                            "{\"useTabs\":true,\"indentSize\":2,\"endOfLine\":\"crlf\","
                            + "\"overrides\":[{\"files\":\"special.cs\",\"printWidth\":40}]}"

                            ".csffrc.yaml",
                            "useTabs: true\nindentSize: 2\nendOfLine: crlf\n"
                            + "overrides:\n  - files: special.cs\n    printWidth: 40\n"
                        ]

                    for name, content in configurations do
                        let config = Configuration.read (write root name content)

                        let settings =
                            Configuration.forFile (Some config) (Path.Combine(root, "special.cs"))

                        Expect.equal settings.Printer.Width 40 (name + " applies the override.")

                        Expect.isTrue
                            settings.Printer.UseTabs
                            (name + " keeps the base useTabs under an override.")

                        Expect.equal
                            settings.Printer.IndentSize
                            2
                            (name + " keeps the base indentSize under an override.")

                        Expect.equal
                            settings.Printer.EndOfLine
                            EndOfLine.CrLf
                            (name + " keeps the base endOfLine under an override.")

                        Expect.isFalse
                            settings.AutoEndOfLine
                            (name + " keeps the base line-ending choice explicit.")

                        let plain =
                            Configuration.forFile (Some config) (Path.Combine(root, "a.cs"))

                        Expect.equal
                            plain.Printer.Width
                            PrinterOptions.Default.Width
                            (name + " leaves a non-matching file on the base width.")

                        Expect.isTrue
                            plain.Printer.UseTabs
                            (name + " leaves a non-matching file on the base settings.")

                        File.Delete(Path.Combine(root, name))

                    let config =
                        Configuration.read (
                            write
                                root
                                ".csffrc.json"
                                ("{\"useTabs\":true,\"indentSize\":2,\"endOfLine\":\"crlf\",\"overrides\":"
                                 + "[{\"files\":\"special.cs\",\"useTabs\":false,\"endOfLine\":\"auto\"}]}")
                        )

                    let settings =
                        Configuration.forFile (Some config) (Path.Combine(root, "special.cs"))

                    Expect.isFalse settings.Printer.UseTabs "An override replaces what it names."

                    Expect.isTrue
                        settings.AutoEndOfLine
                        "An override may restore automatic endings."

                    Expect.equal
                        settings.Printer.IndentSize
                        2
                        "An override keeps the settings it does not name.")
            }
            test "CLI reads tagged YAML numbers in every form and only one YAML document" {
                withDirectory (fun root ->
                    let width (content: string) =
                        (Configuration.read (write root ".csffrc.yaml" content))
                            .Settings.Printer.Width

                    for value in
                        [
                            "80"
                            "+80"
                            "0120"
                            "+0120"
                            "0x50"
                            "+0x50"
                            "0b1010000"
                            "+0b1010000"
                            "1:20"
                            "8_0"
                        ] do
                        Expect.equal (width ("printWidth: !!int " + value + "\n")) 80 value

                    Expect.throws
                        (fun () -> width "printWidth: !!int -0x50\n" |> ignore)
                        "A negative width is still rejected."

                    for content in
                        [
                            "printWidth: !!int -0xFFFFFFFFFFFFFFB0\n"
                            "printWidth: !!int 0xFFFFFFFFFFFFFFFF\n"
                            "indentSize: !!int -0xFFFFFFFFFFFFFFFF\n"
                            "printWidth: !!int 99999999999999999999\n"
                        ] do
                        Expect.throws (fun () -> width content |> ignore) content

                    for value in [ "80"; "8_0.0"; "8.0e1"; "+80." ] do
                        Expect.equal (width ("printWidth: !!float " + value + "\n")) 80 value

                    for content in
                        [
                            "printWidth: !!int ' 80 '\n"
                            "printWidth: !!int |\n  80\n"
                            "printWidth: !!int >\n  80\n"
                        ] do
                        Expect.equal (width content) 80 content

                    for content in [ "useTabs: !!bool |\n  true\n"; "useTabs: !!bool >\n  true\n" ] do
                        Expect.isTrue
                            (Configuration.read (write root ".csffrc.yaml" content))
                                .Settings.Printer.UseTabs
                            content

                    for content in
                        [
                            "printWidth: !custom 80\n"
                            "printWidth: !!binary AAAA\n"
                            "!custom\nprintWidth: 80\n"
                            "--- !custom\nprintWidth: 80\n"
                            "overrides: !custom []\n"
                            "!custom printWidth: 80\n"
                            "! printWidth: 80\n"
                            "useTabs: !!null true\n"
                            "printWidth: ! 80\n"
                            "endOfLine: ! crlf\n"
                            "overrides:\n  - !custom\n    files: '*.cs'\n    printWidth: 40\n"
                        ] do
                        Expect.throws (fun () -> width content |> ignore) content

                    Expect.equal (width "!!map\nprintWidth: 80\n") 80 "The standard mapping tag."

                    Expect.equal (width "---\nprintWidth: 80\n...\n") 80 "One explicit document."

                    Expect.throws
                        (fun () -> width "printWidth: 80\n---\nindentSize: 2\n" |> ignore)
                        "A second YAML document is rejected.")
            }
            test "YAML plain hexadecimal scalars keep unsigned magnitude and reject embedded spaces" {
                use document =
                    JsonDocument.Parse(
                        Configuration.yamlJson "test.yaml" "a: 0xFFFFFFFFFFFFFFB0\nb: 0x 50\n"
                    )

                Expect.equal
                    (document.RootElement.GetProperty("a").GetUInt64())
                    0xFFFFFFFFFFFFFFB0UL
                    "Unsigned hex does not wrap into a negative signed integer."

                Expect.equal
                    (document.RootElement.GetProperty("b").GetString())
                    "0x 50"
                    "Spaces are not accepted inside an untagged hexadecimal number."
            }
            test "JSON-compatible flow configurations still reject duplicate mapping keys" {
                withDirectory (fun root ->
                    for name in [ ".csffrc.yaml"; ".csffrc.json" ] do
                        for content in
                            [
                                "{\"printWidth\":80,\"printWidth\":90}"
                                "{\"overrides\":[{\"files\":\"*.cs\",\"files\":\"a.cs\"}]}"
                            ] do
                            let path = write root name content

                            try
                                Configuration.read path |> ignore
                                failtest "A duplicate configuration key is ambiguous."
                            with :? ArgumentException as error ->
                                Expect.stringContains
                                    error.Message
                                    "Duplicate configuration key"
                                    "JSON notation retains duplicate validation.")
            }
            test "CLI names the YAML configuration file, line and column of a syntax error" {
                withDirectory (fun root ->
                    let path = write root ".csffrc.yaml" "printWidth: 80\nuseTabs: [true\n"

                    try
                        Configuration.read path |> ignore
                        failtest "Invalid YAML is rejected."
                    with :? FormatException as error ->
                        Expect.equal
                            error.Message
                            (path + ":2:10: Unterminated YAML flow collection")
                            "The error locates the unterminated flow sequence.")
            }
            test "CLI stops YAML aliases from expanding a small file without bound" {
                withDirectory (fun root ->
                    let levels =
                        [
                            for level in 1..7 ->
                                let item = if level = 1 then "x" else "*l" + string (level - 1)

                                "l"
                                + string level
                                + ": &l"
                                + string level
                                + " ["
                                + String.Join(", ", Array.create 10 item)
                                + "]"
                        ]

                    let path = write root ".csffrc.yaml" (String.Join("\n", levels) + "\n")

                    Expect.throwsT<ArgumentException>
                        (fun () -> Configuration.read path |> ignore)
                        "Expansion stops at the node limit.")
            }
            test "CLI editorconfig indent_size tab resolves independently of indent_style" {
                withDirectory (fun root ->
                    for style, tabs in [ "", false; "space", false; "tab", true ] do
                        for indentSize, tabWidth, spaceSize, tabSize in
                            [
                                "tab", "tab_width = 3\n", 3, 3
                                "tab", "", 4, 4
                                "2", "", 2, 2
                                "2", "tab_width = 3\n", 2, 3
                            ] do
                            let styleLine = if style = "" then "" else $"indent_style = {style}\n"

                            write
                                root
                                ".editorconfig"
                                ($"root = true\n[*.cs]\nindent_size = {indentSize}\n"
                                 + styleLine
                                 + tabWidth)
                            |> ignore

                            let path = write root "a.cs" "class C{int x;}"
                            let files, results = run [| root |] false true false 1
                            allGood results
                            let size = if tabs then tabSize else spaceSize
                            let context = $"style={style}, indent_size={indentSize}, {tabWidth}"
                            Expect.equal files[0].Settings.Printer.IndentSize size context
                            Expect.equal files[0].Settings.Printer.UseTabs tabs context
                            let indent = if tabs then "\t" else String(' ', size)

                            Expect.equal
                                (File.ReadAllText path)
                                ($"class C\n{{\n{indent}int x;\n}}\n")
                                context

                            let _, verified = run [| root |] true true false 1
                            allGood verified
                            Expect.isFalse verified[0].Changed "Resolved indentation passes check.")
            }
            test "CLI editorconfig indent_size tab resolves widths across matching sections" {
                withDirectory (fun root ->
                    for parent, child in
                        [
                            "tab_width = 3\n", "indent_size = tab\n"
                            "indent_size = tab\ntab_width = 2\n", "tab_width = 3\n"
                        ] do
                        write
                            root
                            ".editorconfig"
                            ("root = true\n[*.cs]\n" + parent + "[a.cs]\n" + child)
                        |> ignore

                        let path = write root "a.cs" "class C{int x;}"
                        let files, results = run [| root |] false true false 1
                        allGood results

                        Expect.equal
                            files[0].Settings.Printer.IndentSize
                            3
                            "Merge before aliasing."

                        Expect.equal
                            (File.ReadAllText path)
                            "class C\n{\n   int x;\n}\n"
                            "A matching section supplies the width.")
            }
            test "CLI editorconfig indent_size tab resolves widths across parent files" {
                withDirectory (fun root ->
                    for parent, child in
                        [
                            "tab_width = 3\n", "indent_size = tab\n"
                            "indent_size = tab\ntab_width = 2\n", "tab_width = 3\n"
                        ] do
                        write
                            root
                            ".editorconfig"
                            ("root = true\n[*.cs]\nindent_style = space\n" + parent)
                        |> ignore

                        write root "sub/.editorconfig" ("[*.cs]\n" + child) |> ignore
                        let path = write root "sub/a.cs" "class C{int x;}"
                        let files, results = run [| root |] false true false 1
                        allGood results

                        Expect.equal
                            files[0].Settings.Printer.IndentSize
                            3
                            "Merge before aliasing."

                        let settings = Discovery.settingsForFile path None |> includedSettings
                        Expect.equal settings.Printer.IndentSize 3 "Stdin inherits the same width."
                        Expect.isFalse settings.Printer.UseTabs "Inherit space indentation."

                        Expect.equal
                            (File.ReadAllText path)
                            "class C\n{\n   int x;\n}\n"
                            "A parent file supplies the width.")
            }
            test "CLI resolves inherited editorconfig until root and gives csffrc priority" {
                withDirectory (fun root ->
                    write
                        root
                        ".editorconfig"
                        "root = true\n[*.cs]\nmax_line_length = 80\nindent_style = tab\nindent_size = tab\ntab_width = 2\nend_of_line = crlf\n"
                    |> ignore

                    write root "sub/.editorconfig" "[special.cs]\nmax_line_length = 40\n" |> ignore
                    write root "sub/a.cs" "class C{}" |> ignore
                    write root "sub/special.cs" "class C{}" |> ignore
                    let files = discover [| root |]

                    Expect.equal
                        (files |> Array.map (fun file -> file.Settings.Printer.Width))
                        [| 80; 40 |]
                        "Section inheritance and patterns."

                    Expect.equal files[0].Settings.Printer.IndentSize 2 "Tabs use tab_width."
                    write root ".csffrc.json" "{\"printWidth\":90}" |> ignore

                    Expect.all
                        (discover [| root |])
                        (fun file -> file.Settings.Printer.Width = 90)
                        "csffrc takes precedence.")
            }
            test "CLI inherits EditorConfig across Git roots for every input root" {
                for worktree in [ false; true ] do
                    withDirectory (fun root ->
                        write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 6\n"
                        |> ignore

                        let parent = Path.Combine(root, "work")
                        let repository = Path.Combine(parent, "repo")
                        let path = write repository "sub/a.cs" "class C{int x;}"

                        if worktree then
                            write repository ".git" "gitdir: /fixture" |> ignore
                        else
                            Directory.CreateDirectory(Path.Combine(repository, ".git")) |> ignore

                        write
                            parent
                            ".editorconfig"
                            "root = true\n[*.cs]\nindent_size = 2\nmax_line_length = 80\n"
                        |> ignore

                        let expected =
                            { Settings.Default with
                                Printer =
                                    { PrinterOptions.Default with
                                        IndentSize = 2
                                        Width = 80
                                    }
                            }

                        for input in [ path; repository; Path.GetDirectoryName path; parent ] do
                            let files = discover [| input |]
                            Expect.equal files.Length 1 "Every input finds the same source."

                            Expect.equal
                                files[0].Settings
                                expected
                                "Git does not bound EditorConfig."

                            use worker = new Worker()
                            worker.Print(File.ReadAllText path, files[0].Settings)

                            Expect.equal
                                worker.OutputText
                                "class C\n{\n  int x;\n}\n"
                                "The inherited two-space setting reaches formatting."

                        Expect.equal
                            (Discovery.settingsForFile path None |> includedSettings)
                            expected
                            "Virtual files use the same inherited settings."

                        write repository "sub/.editorconfig" "[a.cs]\nmax_line_length = 40\n"
                        |> ignore

                        Expect.equal
                            (discover [| repository |]).[0].Settings.Printer.IndentSize
                            2
                            "A nearer section retains inherited properties."

                        Expect.equal
                            (Discovery.settingsForFile path None |> includedSettings).Printer.Width
                            40
                            "A nearer section overrides only its specified properties."

                        write
                            repository
                            "sub/.editorconfig"
                            "root = true\n[*.cs]\nindent_size = 3\n"
                        |> ignore

                        for input in [ path; repository; Path.GetDirectoryName path; parent ] do
                            let settings = (discover [| input |]).[0].Settings

                            Expect.equal
                                settings.Printer.IndentSize
                                3
                                "EditorConfig root resets sections."

                            Expect.equal settings.Printer.Width 100 "Ancestor width is reset too.")
            }
            test "CLI selects the nearest csffrc across Git roots and EditorConfig roots" {
                withDirectory (fun root ->
                    write root ".csffrc.json" "{\"indentSize\":6,\"printWidth\":120}" |> ignore
                    let parent = Path.Combine(root, "work")
                    let repository = Path.Combine(parent, "repo")
                    let path = write repository "sub/a.cs" "class C{int x;}"
                    write repository ".git" "gitdir: /fixture" |> ignore

                    write repository ".editorconfig" "root = true\n[*.cs]\nindent_size = 3\n"
                    |> ignore

                    write parent ".csffrc.yaml" "indentSize: 2\nprintWidth: 80\n" |> ignore

                    let verify indent width =
                        for input in [ path; repository; Path.GetDirectoryName path; parent ] do
                            let settings = (discover [| input |]).[0].Settings

                            Expect.equal
                                settings.Printer.IndentSize
                                indent
                                "The nearest csffrc wins."

                            Expect.equal
                                settings.Printer.Width
                                width
                                "csffrc settings are not merged."

                        let settings = Discovery.settingsForFile path None |> includedSettings

                        Expect.equal
                            settings.Printer.IndentSize
                            indent
                            "Virtual files find the csffrc."

                        Expect.equal
                            settings.Printer.Width
                            width
                            "Virtual files use the same width."

                    verify 2 80
                    write repository ".csffrc.json" "{\"indentSize\":5}" |> ignore
                    verify 5 100)
            }
            test "CLI scopes Git ignores across Git roots while inheriting configuration" {
                withDirectory (fun root ->
                    write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 2\n" |> ignore
                    write root ".gitignore" "outer.cs\n" |> ignore
                    write root ".csffignore" "csff.cs\n" |> ignore
                    let repository = Path.Combine(root, "repo")
                    let path = write repository "sub/outer.cs" "class C{}"
                    write repository "sub/local.cs" "class C{}" |> ignore
                    write repository "sub/csff.cs" "class C{}" |> ignore
                    write repository ".gitignore" "local.cs\n" |> ignore
                    write repository ".git" "gitdir: /fixture" |> ignore

                    for input in [ path; repository; Path.GetDirectoryName path; root ] do
                        let files = discover [| input |]

                        Expect.equal
                            (files |> Array.map (fun file -> Path.GetFullPath file.Path))
                            [| Path.GetFullPath path |]
                            "Git ignores reset at the repository; csff ignores keep their own scope."

                        Expect.equal
                            files[0].Settings.Printer.IndentSize
                            2
                            "Configuration still comes from outside the Git root.")
            }
            for name, invalid, nearest, fatal in
                [
                    ".csffrc.json", "{", "{\"indentSize\":2,\"printWidth\":80}", true
                    ".csffrc.yaml", "indentSize: [", "indentSize: 2\nprintWidth: 80\n", true
                    ".editorconfig",
                    "[[*.cs]\nindent_size = 6\n",
                    "root = true\n[*.cs]\nindent_size = 2\nmax_line_length = 80\n",
                    false
                    ".csffignore", "[\n", "skip.cs\n", true
                ] do
                test $"CLI skips out-of-scope ancestor {name}" {
                    for worktree in [ false; true ] do
                        withDirectory (fun root ->
                            write
                                root
                                ".editorconfig"
                                "root = true\n[*.cs]\nindent_size = 2\nmax_line_length = 80\n"
                            |> ignore

                            write root name invalid |> ignore
                            let repository = Path.Combine(root, "repo")
                            let path = write repository "sub/a.cs" "class C{int x;}"
                            write repository name nearest |> ignore

                            if worktree then
                                write repository ".git" "gitdir: /fixture" |> ignore
                            else
                                Directory.CreateDirectory(Path.Combine(repository, ".git"))
                                |> ignore

                            for input in [ path; repository; Path.GetDirectoryName path ] do
                                let files = discover [| input |]
                                Expect.equal files.Length 1 "Scoped discovery includes the source."

                                Expect.equal
                                    (files[0].Settings.Printer.IndentSize,
                                     files[0].Settings.Printer.Width)
                                    (2, 80)
                                    "Applicable configuration still inherits across Git roots."

                            let settings = Discovery.settingsForFile path None |> includedSettings

                            Expect.equal
                                (settings.Printer.IndentSize, settings.Printer.Width)
                                (2, 80)
                                "Virtual files use the same scopes."

                            use worker = new Worker()
                            worker.Print(File.ReadAllText path, settings)

                            Expect.equal
                                worker.OutputText
                                "class C\n{\n  int x;\n}\n"
                                "Discarded ancestor files cannot abort formatting."

                            if fatal then
                                Expect.throws
                                    (fun () -> discover [| root |] |> ignore)
                                    "An invalid file still fails when it is in scope."
                            else
                                let files = discover [| root |]

                                Expect.equal
                                    files.Length
                                    1
                                    "A foreign dialect's malformed section does not end the run."

                                for file in files do
                                    Expect.notEqual
                                        file.Settings.Printer.IndentSize
                                        6
                                        "A dead section's settings reach no file.")
                }
            test "CLI reads only csff names, never the retired CSharpier ones" {
                withDirectory (fun root ->
                    write root ".csffrc" "{\"printWidth\":60}" |> ignore
                    write root ".csharpierrc.json" "{\"printWidth\":60}" |> ignore
                    write root ".csharpierignore" "skip.cs\n" |> ignore

                    write
                        root
                        ".editorconfig"
                        "root = true\n[*.cs]\nmax_line_length = 80\n[old.cs]\ncsharpier_formatter = xml\n[new.cs]\ncsff_formatter = xml\n"
                    |> ignore

                    for name in [ "a.cs"; "new.cs"; "old.cs"; "skip.cs" ] do
                        write root name "class C{}" |> ignore

                    Expect.equal
                        (discover [| root |]
                         |> Array.map (fun file ->
                             Path.GetFileName file.Path, file.Settings.Printer.Width))
                        [| "a.cs", 80; "old.cs", 80; "skip.cs", 80 |]
                        "Only .csffrc.*, .csffignore and csff_formatter take effect.")
            }
            test "CLI stdin settings resolve ancestor configs and editorconfig sections" {
                withDirectory (fun root ->
                    let path = write root "sub/nested/source.cs" "class C{}"

                    write root ".editorconfig" "root = true\n[*.cs]\nmax_line_length = 40\n"
                    |> ignore

                    let settings = Discovery.settingsForFile path None |> includedSettings

                    Expect.equal
                        settings.Printer.Width
                        40
                        "Virtual stdin files inherit EditorConfig."

                    write root ".csffrc.json" "{\"printWidth\":60}" |> ignore
                    let settings = Discovery.settingsForFile path None |> includedSettings
                    Expect.equal settings.Printer.Width 60 "Ancestor csffrc wins."
                    let explicit = write root "config.json" "{\"printWidth\":80}"

                    let settings =
                        Discovery.settingsForFile path (Some explicit) |> includedSettings

                    Expect.equal settings.Printer.Width 80 "Explicit configuration wins.")
            }
            test "CLI editorconfig numeric ranges select two-space indentation" {
                withDirectory (fun root ->
                    write root ".editorconfig" "root = true\n[File{1..3}.cs]\nindent_size = 2\n"
                    |> ignore

                    for name, indent in
                        [
                            "File2.cs", 2
                            "File1.cs", 2
                            "File3.cs", 2
                            "sub/File2.cs", 2
                            "File0.cs", 4
                            "File4.cs", 4
                            "File02.cs", 4
                            "File-2.cs", 4
                            "Filex.cs", 4
                            "File2x.cs", 4
                            "File1..3.cs", 4
                        ] do
                        let path = write root name "class C{int x;}"

                        let _, results = run [| path |] false true false 1
                        allGood results

                        Expect.equal
                            (File.ReadAllText path)
                            ("class C\n{\n" + String(' ', indent) + "int x;\n}\n")
                            name)
            }
            test "CLI numeric ranges support signed, reversed and zero-padded bounds" {
                for pattern, matching, excluded in
                    [
                        "File{-3..-1}.cs",
                        [ "File-3.cs"; "File-2.cs"; "File-1.cs" ],
                        [ "File-4.cs"; "File0.cs"; "File2.cs"; "File-02.cs" ]
                        "File{-2..2}.cs",
                        [ "File-2.cs"; "File-1.cs"; "File0.cs"; "File2.cs" ],
                        [ "File-3.cs"; "File3.cs"; "File-0.cs"; "File+1.cs" ]
                        "File{3..1}.cs",
                        [ "File1.cs"; "File2.cs"; "File3.cs" ],
                        [ "File0.cs"; "File4.cs"; "File02.cs" ]
                        "File{-1..-3}.cs",
                        [ "File-3.cs"; "File-2.cs"; "File-1.cs" ],
                        [ "File-4.cs"; "File0.cs" ]
                        "File{2..-2}.cs",
                        [ "File-2.cs"; "File0.cs"; "File2.cs" ],
                        [ "File-3.cs"; "File3.cs" ]
                        "File{002..004}.cs",
                        [ "File2.cs"; "File3.cs"; "File4.cs" ],
                        [ "File1.cs"; "File5.cs"; "File003.cs" ]
                        "File{-003..-001}.cs",
                        [ "File-3.cs"; "File-2.cs"; "File-1.cs" ],
                        [ "File-003.cs"; "File0.cs" ]
                        "File{2..2}.cs", [ "File2.cs" ], [ "File1.cs"; "File3.cs" ]
                        "File{-0..0}.cs", [ "File0.cs" ], [ "File-0.cs"; "File00.cs" ]
                    ] do
                    let glob = Glob.compile pattern

                    for name in matching do
                        Expect.isTrue (glob.IsMatch name) (pattern + " matches " + name)

                    for name in excluded do
                        Expect.isFalse (glob.IsMatch name) (pattern + " excludes " + name)
            }
            test "CLI numeric ranges compose with brace alternatives and other glob tokens" {
                let glob = Glob.filePattern "File{a,{1..3}}-{x,{-2..0}}[ab]?.cs"

                for name in [ "File2--1az.cs"; "Filea-xb1.cs"; "sub/File3-0a2.cs" ] do
                    Expect.isTrue (glob.IsMatch name) name

                for name in [ "File4--1az.cs"; "File2--3az.cs"; "File02-0a2.cs" ] do
                    Expect.isFalse (glob.IsMatch name) name

                let adjacent = Glob.compile "File{1..12}{1..3}.cs"
                Expect.isTrue (adjacent.IsMatch "File123.cs") "Both ranges can consume digits."
                Expect.isFalse (adjacent.IsMatch "File124.cs") "Each range enforces its bounds."

                let escaped = Glob.compile "File\\{1..3\\}.cs"
                Expect.isTrue (escaped.IsMatch "File{1..3}.cs") "Escaped braces remain literal."
                Expect.isFalse (escaped.IsMatch "File2.cs") "Escaping disables the range."
            }
            test "glob character classes never consume path separators" {
                for compile in [ Glob.compile; Glob.compileIgnore; Glob.compileGitIgnore ] do
                    for pattern in [ "*[!b]a.cs"; "*[--9]a.cs"; "*[a/]a.cs" ] do
                        let glob = compile pattern

                        Expect.isFalse
                            (glob.IsMatch "sub/a.cs")
                            "A character class cannot cross a directory boundary."

                    Expect.isTrue
                        ((compile "[!b]a.cs").IsMatch "ca.cs")
                        "Negated classes still match non-separators."

                    Expect.isTrue
                        ((compile "[--9]a.cs").IsMatch ".a.cs")
                        "Ranges retain their non-separator members."
            }
            test "glob numeric bounds have a bounded digit count" {
                for first, last in [ "0", String('9', 10_000); String('1', 10_000), "0" ] do
                    Expect.throwsT<ArgumentException>
                        (fun () -> Glob.compile ("{" + first + ".." + last + "}") |> ignore)
                        "Oversized numeric bounds fail before building a quadratic-size regex."

                let largest = String('9', 128)

                Expect.isTrue
                    ((Glob.compile ("{0.." + largest + "}")).IsMatch largest)
                    "The supported boundary still compiles."

                Expect.throwsT<ArgumentException>
                    (fun () -> Glob.compile ("{-" + String('9', 129) + "..0}") |> ignore)
                    "The sign does not count toward the digit limit."
            }
            test "a glob character class compiles the way Git reads it" {
                for pattern, matching, excluded in
                    [
                        "[]*]file.txt", [ "]file.txt"; "*file.txt" ], [ "afile.txt"; "file.txt" ]
                        "[!]a]x", [ "bx" ], [ "]x"; "ax" ]
                        "[^]a]x", [ "bx" ], [ "]x"; "ax" ]
                        "[]]x", [ "]x" ], [ "x"; "ax" ]
                        "[a^]x", [ "ax"; "^x" ], [ "bx" ]
                        "[\\]]x", [ "]x" ], [ "\\x"; "x" ]
                        "[\\\\]x", [ "\\x" ], [ "ax" ]
                        "[\\d]x", [ "dx" ], [ "1x"; "\\x" ]
                        "[a-z]x", [ "bx" ], [ "1x"; "-x" ]
                        "[!0-9]x", [ "ax" ], [ "5x" ]
                        "[-a]x", [ "-x"; "ax" ], [ "bx" ]
                        "[a-]x", [ "-x"; "ax" ], [ "bx" ]
                        "[]-a]x", [ "]x"; "^x"; "_x"; "ax" ], [ "bx" ]
                        "[a-z-0]x", [ "bx"; "-x"; "0x" ], [ "1x" ]
                        "[\\a]x", [ "ax" ], [ "\\x"; "\ax" ]
                        "[--9]x", [ "-x"; ".x"; "0x"; "9x" ], [ "+x"; "ax" ]
                        "[z-a]x", [ "zx" ], [ "ax"; "bx"; "-x" ]
                        "[a--b]x", [ "ax"; "bx" ], [ "-x"; "cx" ]
                        "[a-*]x", [ "ax" ], [ "*x"; "bx" ]
                        "[a-z-A-Z]x", [ "ax"; "-x"; "Bx" ], [ "0x" ]
                        "[a-z-[aeiou]]x", [ "a]x"; "-]x"; "[]x" ], [ "ax"; "bx"; "dx" ]
                    ] do
                    let glob = Glob.compile pattern

                    for name in matching do
                        Expect.isTrue (glob.IsMatch name) (pattern + " matches " + name)

                    for name in excluded do
                        Expect.isFalse (glob.IsMatch name) (pattern + " excludes " + name)

                for pattern, names in
                    [
                        "[]x", [ "]x"; "x"; "[]x" ]
                        "[!]x", [ "ax"; "]x"; "[!]x" ]
                        "[a\\]x", [ "ax"; "]x"; "a]x" ]
                    ] do
                    let glob = Glob.compileGitIgnore pattern

                    for name in names do
                        Expect.isFalse
                            (glob.IsMatch name)
                            (pattern + " matches nothing in .gitignore, including " + name)

                    Expect.throws
                        (fun () -> Glob.compileIgnore pattern |> ignore)
                        (pattern + " is rejected outside .gitignore")
            }
            test "CLI numeric ranges match large intervals without enumerating integers" {
                for pattern, matching, excluded in
                    [
                        "File{3..120}.cs",
                        [ "File3.cs"; "File9.cs"; "File10.cs"; "File99.cs"; "File120.cs" ],
                        [ "File2.cs"; "File121.cs"; "File060.cs" ]
                        "File{-2147483648..2147483647}.cs",
                        [ "File-2147483648.cs"; "File0.cs"; "File2147483647.cs" ],
                        [ "File-2147483649.cs"; "File2147483648.cs" ]
                        "File{9223372036854775807..9223372036854775810}.cs",
                        [
                            "File9223372036854775807.cs"
                            "File9223372036854775809.cs"
                            "File9223372036854775810.cs"
                        ],
                        [ "File9223372036854775806.cs"; "File9223372036854775811.cs" ]
                    ] do
                    let glob = Glob.compile pattern

                    for name in matching do
                        Expect.isTrue (glob.IsMatch name) (pattern + " matches " + name)

                    for name in excluded do
                        Expect.isFalse (glob.IsMatch name) (pattern + " excludes " + name)
            }
            test "CLI ignore globs retain literal braces and commas" {
                withDirectory (fun root ->
                    write root ".gitignore" "a{b,c}.cs\na,b.cs\nFile{1..3}.cs\n" |> ignore

                    for name in
                        [ "a{b,c}.cs"; "a,b.cs"; "ab.cs"; "ac.cs"; "File{1..3}.cs"; "File2.cs" ] do
                        write root name "class C{}" |> ignore

                    let names =
                        discover [| root |] |> Array.map (fun file -> Path.GetFileName file.Path)

                    Expect.equal
                        names
                        [| "File2.cs"; "ab.cs"; "ac.cs" |]
                        "Git ignores do not expand braces.")
            }
            test "CLI preserves BOM, encoding, automatic line endings and empty files" {
                withDirectory (fun root ->
                    let encodings: Encoding array =
                        [|
                            UTF8Encoding(true, true)
                            UnicodeEncoding(false, true, true)
                            UnicodeEncoding(true, true, true)
                            UTF32Encoding(false, true, true)
                            UTF32Encoding(true, true, true)
                        |]

                    for index = 0 to encodings.Length - 1 do
                        let path = write root ($"{index}.cs") ""
                        File.WriteAllText(path, "class C{\r\n}\r\n", encodings[index])

                    let empty = write root "empty.cs" ""
                    let _, results = run [| root |] false false false 2
                    allGood results

                    for index = 0 to encodings.Length - 1 do
                        let expected =
                            Array.append
                                (encodings[index].GetPreamble())
                                (encodings[index].GetBytes "class C { }\r\n")

                        Expect.equal
                            (File.ReadAllBytes(Path.Combine(root, $"{index}.cs")))
                            expected
                            "Preserve byte encoding and CRLF."

                    Expect.equal (File.ReadAllBytes empty) [||] "Empty stays empty."

                    Expect.all
                        (check [| root |])
                        (fun result -> result.Cached)
                        "Encoded output is cached.")
            }
            test "an already formatted file keeps its bytes in every encoding" {
                withDirectory (fun root ->
                    let encodings: Encoding array =
                        [|
                            UTF8Encoding(false, true)
                            UTF8Encoding(true, true)
                            UnicodeEncoding(false, true, true)
                            UnicodeEncoding(true, true, true)
                            UTF32Encoding(false, true, true)
                            UTF32Encoding(true, true, true)
                        |]

                    let formatted = "class C { }\r\n"

                    let expected =
                        encodings
                        |> Array.map (fun encoding ->
                            Array.append (encoding.GetPreamble()) (encoding.GetBytes formatted))

                    for index = 0 to encodings.Length - 1 do
                        let path = write root ($"{index}.cs") ""
                        File.WriteAllBytes(path, expected[index])

                    let _, results = run [| root |] false false false 2
                    allGood results

                    Expect.all
                        results
                        (fun result -> not result.Changed)
                        "A formatted file is not reported as changed."

                    for index = 0 to encodings.Length - 1 do
                        Expect.equal
                            (File.ReadAllBytes(Path.Combine(root, $"{index}.cs")))
                            expected[index]
                            "The file keeps the bytes it had.")
            }
            test "CLI skips generated names and comments unless explicitly included" {
                withDirectory (fun root ->
                    let named = write root "a.g.cs" "class A{}"
                    let comment = write root "b.cs" "// <auto-generated />\nclass B{}"
                    let _, results = run [| root |] false false false 1
                    Expect.equal results.Length 1 "Generated file name is pruned."
                    Expect.isTrue results[0].Skipped "Generated comment is skipped."

                    Expect.equal
                        (File.ReadAllText comment)
                        "// <auto-generated />\nclass B{}"
                        "Skipped bytes are untouched."

                    let _, included = run [| root |] false false true 1
                    allGood included

                    Expect.all
                        included
                        (fun result -> result.Changed)
                        "Include both generated forms."

                    Expect.equal
                        (File.ReadAllText named)
                        "class A { }\n"
                        "Generated output is formatted.")
            }
            test
                "CLI sequential and parallel workers produce identical bytes without cross-file state" {
                withDirectory (fun root ->
                    let sequential = Path.Combine(root, "sequential")
                    let concurrent = Path.Combine(root, "parallel")

                    for index in 0..23 do
                        let source =
                            if index % 3 = 0 then
                                "#if DEBUG\nclass C{void M(){Call(a,b,c);}}\n#else\nclass C{}\n#endif\n"
                            else
                                $"class C{index}{{int P=>{index};}}"

                        write sequential ($"{index}.cs") source |> ignore
                        write concurrent ($"{index}.cs") source |> ignore

                    run [| sequential |] false true false 1 |> snd |> allGood
                    run [| concurrent |] false true false 4 |> snd |> allGood

                    for index in 0..23 do
                        Expect.equal
                            (File.ReadAllBytes(Path.Combine(concurrent, $"{index}.cs")))
                            (File.ReadAllBytes(Path.Combine(sequential, $"{index}.cs")))
                            "Worker buffers reset fully.")
            }
            test "CLI reports I/O failures while still processing other files" {
                withDirectory (fun root ->
                    let good = write root "good.cs" "class C{}"
                    let missing = write root "missing.cs" "class D{}"
                    let files = discover [| root |]
                    File.Delete missing

                    let results =
                        Formatter.run
                            [| root |]
                            files
                            false
                            true
                            false
                            2
                            None
                            CancellationToken.None

                    Expect.isNull results[0].Error "The other file formats."
                    Expect.stringContains results[1].Error "missing.cs" "Locate the failure."
                    Expect.equal (File.ReadAllText good) "class C { }\n" "Independent progress.")
            }
            test "CLI rejects syntax recovery before writing or caching" {
                withDirectory (fun root ->
                    let path = write root "broken.cs" "class C {"
                    let _, results = run [| root |] false false false 1

                    Expect.stringContains
                        results[0].Error
                        "Incomplete C#"
                        "Missing syntax is a formatting failure."

                    Expect.equal
                        (File.ReadAllText path)
                        "class C {"
                        "Do not publish a recovered tree."

                    Expect.isFalse results[0].Cacheable "Syntax failures cannot enter the cache.")
            }
        ]

let private commandTests =
    testList
        "cli"
        [
            test "CLI names a file over the verification limit, leaves it as it was, and exits 0" {
                withDirectory (fun root ->
                    let depth = 4000

                    let huge =
                        "class C { int M() => "
                        + String.replicate depth "F(1, "
                        + "1"
                        + String.replicate depth ")"
                        + "; }\n"

                    let hugePath = write root "Huge.cs" huge
                    let small = "class C{int x;}"
                    let smallPath = write root "Small.cs" small

                    let code, _, errors = capture (fun () -> Program.run [| "--no-cache"; root |])

                    Expect.equal code 0 errors

                    Expect.stringContains
                        errors
                        (Path.GetFullPath hugePath
                         + ": source or formatted output exceeds the 64 MiB syntax verification limit; the file is unchanged."
                         + Environment.NewLine)
                        "The file over the limit is named."

                    Expect.stringContains
                        errors
                        "0 unverified"
                        "Skipping it is not an unproven file."

                    Expect.equal
                        (File.ReadAllText hugePath)
                        huge
                        "The file over the limit is left as it was."

                    Expect.notEqual
                        (File.ReadAllText smallPath)
                        small
                        "The rest of the run is formatted."

                    let code, output, errors =
                        capture (fun () -> Program.run [| "--write-stdout"; hugePath |])

                    Expect.equal code 0 errors

                    Expect.equal
                        output
                        huge
                        "--write-stdout writes a file over the limit back as it was read."

                    Expect.stringContains
                        errors
                        ": source or formatted output exceeds the 64 MiB syntax verification limit; the file is unchanged."
                        "--write-stdout names it too."

                    for oversized in
                        [
                            "class C {\n" + String.replicate VerificationLimit.Characters " "
                            "class C { }\n//"
                            + String.replicate VerificationLimit.Characters "x"
                            + "\n"
                        ] do
                        let path = write root "Oversized.cs" oversized

                        let code, output, errors =
                            capture (fun () -> Program.run [| "--write-stdout"; path |])

                        Expect.equal code 0 errors

                        Expect.isTrue
                            (output = oversized)
                            "An oversized source is written back as it was read."

                        Expect.stringContains
                            errors
                            ": source or formatted output exceeds the 64 MiB syntax verification limit; the file is unchanged."
                            "An oversized source is named.")
            }
            test
                "CLI prints a file unproven where a configuration is not C# again with every token as it went in" {
                withDirectory (fun root ->
                    let cases =
                        [
                            "Usings.cs",
                            "using System.Text;\nusing System;\n#if NEVER\nclass {\n#endif\nclass C {   }\n",
                            "using System.Text;\nusing System;\n#if NEVER\nclass {\n#endif\nclass C { }\n",
                            "Usings stay in their order."
                            "Modifiers.cs",
                            "class C {\n#if NEVER\n  )\n#endif\n  public static void M() { }\n  static public void N() { }\n}\n",
                            "class C\n{\n#if NEVER\n  )\n#endif\n    public static void M() { }\n\n    static public void N() { }\n}\n",
                            "Modifiers stay in their order."
                            "Enum.cs",
                            "enum E { A, B }\n#if NEVER\nclass {\n#endif\nclass   D { }\n",
                            "enum E\n{\n    A,\n    B\n}\n#if NEVER\nclass {\n#endif\nclass D { }\n",
                            "No trailing comma is added to an enum."
                            "FlatComma.cs",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C { int[] a = { 1, 2, }; }\n",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C\n{\n    int[] a = { 1, 2, };\n}\n",
                            "A trailing comma on a flat list is kept."
                            "BrokenComma.cs",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C { int[] a = { 1111111111, 2222222222, 3333333333, 4444444444, 5555555555, 6666666666, 7777777777 }; }\n",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C\n{\n    int[] a =\n    {\n        1111111111,\n        2222222222,\n        3333333333,\n        4444444444,\n        5555555555,\n        6666666666,\n        7777777777\n    };\n}\n",
                            "None is added to a broken one."
                            "Raw.cs",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C { void M() { var s = \"\"\"\n  x\n  \"\"\"; } }\n",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C\n{\n    void M()\n    {\n        var s = \"\"\"\n  x\n  \"\"\";\n    }\n}\n",
                            "A raw string keeps its indentation."
                            "InterpolatedRaw.cs",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C { void M() { var s = $\"\"\"\n  {1}\n  \"\"\"; } }\n",
                            "using B;\nusing A;\n#if NEVER\nclass {\n#endif\nclass C\n{\n    void M()\n    {\n        var s = $\"\"\"\n  {1}\n  \"\"\";\n    }\n}\n",
                            "An interpolated raw string keeps its indentation."
                            "Closers.cs",
                            "using System.Text;\nusing System;\n#if NEVER\nvoid M() {\n#endif\nclass C\n{\n    System.Collections.Generic.Dictionary<string, System.Collections.Generic.List<System.Collections.Generic.KeyValuePair<string, int>>> field;\n    int  y;\n}\n",
                            "using System.Text;\nusing System;\n#if NEVER\nvoid M() {\n#endif\nclass C\n{\n    System.Collections.Generic.Dictionary<string, System.Collections.Generic.List<System.Collections.Generic.KeyValuePair<string, int>>> field;\n    int y;\n}\n",
                            "Two touching closers stay touching, however long the line."
                            "Recovered.cs",
                            "class C\n{\n    static internal void M()\n    {\n#if MDA\n        catch\n#endif\n    }\n#if FEATURE\n    static extern void N();   \n#endif\n}\n",
                            "class C\n{\n    static internal void M()\n    {\n#if MDA\n        catch\n#endif\n    }\n#if FEATURE\n    static extern void N();\n#endif\n}\n",
                            "A disabled region loses its trailing blanks."
                            "RawMargin.cs",
                            "#if DEBUG\nclass C\n{\n    void M()   \n    {\n        var test = \"\"\"\n            #if X\n #else\n            #endif\n            \"\"\";\n        {\n        };\n    }\n}\n#endif\n",
                            "#if DEBUG\nclass C\n{\n    void M()\n    {\n        var test = \"\"\"\n            #if X\n #else\n            #endif\n            \"\"\";\n        {\n        };\n    }\n}\n#endif\n",
                            "A raw string another configuration reads keeps its lines."
                        ]

                    for name, source, _, _ in cases do
                        write root name source |> ignore

                    let code, _, errors = capture (fun () -> Program.run [| "--no-cache"; root |])
                    Expect.equal code 0 errors
                    Expect.stringContains errors "0 unverified" "Every file is proven."

                    for name, source, expected, why in cases do
                        let path = Path.Combine(root, name)
                        Expect.equal (File.ReadAllText path) expected (name + ": " + why)

                        let code, output, errors =
                            capture (fun () -> Program.run [| "--write-stdout"; path |])

                        Expect.equal code 0 (name + ": " + errors)
                        Expect.equal output expected (name + ": the output is stable.")

                        write root name source |> ignore

                        let code, output, errors =
                            capture (fun () -> Program.run [| "--write-stdout"; path |])

                        Expect.equal code 0 (name + ": " + errors)

                        Expect.equal
                            output
                            expected
                            (name + ": --write-stdout prints the same text."))
            }
            test "CLI leaves unresolved conflict markers untouched in every output mode" {
                withDirectory (fun root ->
                    let conflict = "<<<<<<< HEAD\nclass A{}\n=======\nclass B{}\n>>>>>>> other\n"

                    for source in
                        [
                            conflict
                            "#if X\n" + conflict + "#endif\nclass C{}\n"
                            "#if X\n<<<<<<< HEAD\nclass A{\n=======\nclass B{}\n>>>>>>> other\n#endif\nclass C{}\n"
                            "// csff-ignore\nclass C{\n" + conflict + "}\nclass D{}\n"
                            "class C{\n// csff-ignore\nvoid M(){\n"
                            + conflict
                            + "}\n}\nclass D{}\n"
                            "// csff-ignore-start\nclass C{\n"
                            + conflict
                            + "}\n// csff-ignore-end\nclass D{}\n"
                        ] do
                        let path = write root "conflict.cs" source

                        for args, expected in
                            [
                                [| "--no-cache"; path |], 1
                                [| "--check"; "--no-cache"; path |], 1
                                [| "--write-stdout"; path |], 2
                            ] do
                            let code, output, errors = capture (fun () -> Program.run args)
                            Expect.equal code expected errors
                            Expect.equal output "" "Unresolved source is never published."

                            Expect.equal
                                (File.ReadAllText path)
                                source
                                "Conflict data remains intact."

                    for source in
                        [
                            "class C { string S = \"\"\"\n<<<<<<< HEAD\n=======\n>>>>>>> other\n\"\"\"; }"
                            "#if false\n" + conflict + "#endif\nclass C{}\n"
                            "class G<T>{}\nclass C{\nG<G<G<G<G<G<G<int\n>>>>>>> field;\n}\n"
                        ] do
                        let path = write root "literal.cs" source

                        let code, output, errors =
                            capture (fun () -> Program.run [| "--write-stdout"; path |])

                        Expect.equal code 0 errors

                        if source.Contains("<<<<<<< HEAD", StringComparison.Ordinal) then
                            Expect.stringContains
                                output
                                "<<<<<<< HEAD"
                                "Literal and inactive marker-like text survives."
                        else
                            Expect.stringContains
                                output
                                "field;"
                                "Valid generic declarations format.")
            }
            test "CLI refuses output it cannot verify in write, check, and stdout modes" {
                withDirectory (fun root ->
                    let source = "class C\n{\n    void M()\n    {\n"
                    let path = write root "incomplete.cs" source

                    for check in [ false; true ] do
                        let _, results = run [| path |] check true false 1

                        Expect.stringContains
                            results[0].Error
                            "Incomplete C# syntax"
                            "Reject what cannot be verified."

                        Expect.isFalse results[0].Cacheable "Do not cache rejected output."
                        Expect.equal (File.ReadAllText path) source "Leave the input untouched."

                    let code, output, errors =
                        capture (fun () -> Program.run [| "--write-stdout"; path |])

                    Expect.equal code 2 "A rejected stdout render fails."
                    Expect.equal output "" "Do not print invalid formatted text."

                    Expect.stringContains
                        errors
                        "Incomplete C# syntax"
                        "Explain the rejected output.")
            }
            test "a nested lambda's conditional branches each keep their line" {
                withDirectory (fun root ->
                    let source =
                        "using System;\nusing System.Collections.Generic;\nusing System.Linq;\nclass C\n{\n    private static IEnumerable<Assembly> GetApplicationPartAssemblies(Assembly assembly)\n    {\n#if NETCOREAPP3_1_OR_GREATER\n        var assemblyContext = AssemblyLoadContext.GetLoadContext(assembly) ?? AssemblyLoadContext.Default;\n#endif\n        return ExpandApplicationParts(\n            new[] { assembly }.Concat(assembly.GetCustomAttributes<ApplicationPartAttribute>()\n                .Select(name =>\n#if NETCOREAPP3_1_OR_GREATER\n                    assemblyContext.LoadFromAssemblyName(new AssemblyName(name.AssemblyName))\n#else\n                    Assembly.Load(new AssemblyName(name.AssemblyName))\n#endif\n                )));\n    }\n}\n"

                    let path = write root "conditional-lambda.cs" source
                    let _, results = run [| path |] false true false 1
                    allGood results
                    let formatted = File.ReadAllText path

                    for line in formatted.Split('\n') do
                        let hash = line.IndexOf('#')

                        if hash >= 0 then
                            Expect.isTrue
                                (line.AsSpan(0, hash).IsWhiteSpace())
                                $"Nothing shares a directive's line before it: {line}"

                    let _, again = run [| path |] true true false 1
                    allGood again
                    Expect.equal (File.ReadAllText path) formatted "The output is formatted.")
            }
            test "CLI accepts safe sorting, trailing commas, and raw-string EOL changes" {
                withDirectory (fun root ->
                    let samples =
                        [
                            "commented-modifiers.cs",
                            "class C{\r\n// comment\r\nreadonly static string[] X = new[] { \"\"\"\n    hello\n    \"\"\", \"\"\"\n    other\n    \"\"\" };\r\n}\r\n",
                            "static readonly"
                            "conditional-usings.cs",
                            "using System.Text;\n#if X\nusing System.Linq;\n#endif\nusing System.Collections.Generic;\nclass C{string[] X = new[] { \"\"\"\r\n    hello\r\n    \"\"\", \"\"\"\r\n    other\r\n    \"\"\" };}\n",
                            "using System.Collections.Generic;"
                            "utf8-raw.cs",
                            "using System.Text;\n#if X\nusing System.Linq;\n#endif\nusing System.Collections.Generic;\nclass C{byte[][] X = new[] { \"\"\"\r\n    hello\r\n    \"\"\"u8.ToArray(), \"\"\"\r\n    other\r\n    \"\"\"u8.ToArray() };}\n",
                            "\"\"\"u8.ToArray(),"
                        ]

                    for name, source, expected in samples do
                        let path = write root name source

                        let code, output, errors =
                            capture (fun () -> Program.run [| "--write-stdout"; path |])

                        Expect.equal code 0 $"{name}: {errors}"
                        Expect.stringContains output expected "Keep declared formatting changes."

                        Expect.equal
                            (File.ReadAllText path)
                            source
                            "Stdout leaves input untouched.")
            }
            for ancestor, location in [ false, "repository"; true, "ancestor" ] do
                test $"CLI automatic {location} csffrc skips fallback EditorConfig" {
                    for worktree in [ false; true ] do
                        withDirectory (fun root ->
                            let fallback = "root = true\n[*.cs]\nindent_size = 6\n"
                            write root ".editorconfig" fallback |> ignore
                            let repository = Path.Combine(root, "repo")
                            let source = "class C{int x;}"
                            let path = write repository "sub/a.cs" source
                            let directory = Path.GetDirectoryName path

                            if worktree then
                                write repository ".git" "gitdir: /fixture" |> ignore
                            else
                                Directory.CreateDirectory(Path.Combine(repository, ".git"))
                                |> ignore

                            let code, output, _ =
                                capture (fun () -> Program.run [| "--write-stdout"; path |])

                            Expect.equal
                                (code, output)
                                (0, $"class C\n{{\n{String(' ', 6)}int x;\n}}\n")
                                "With no csffrc anywhere, the EditorConfig is the fallback."

                            let configDirectory = if ancestor then root else repository

                            write
                                configDirectory
                                ".csffrc.json"
                                "{\"indentSize\":2,\"printWidth\":80}"
                            |> ignore

                            let verify indent =
                                let inputs =
                                    [ path; repository; directory ]
                                    @ (if ancestor then [ root ] else [])

                                for input in inputs do
                                    let files = discover [| input |]
                                    Expect.equal files.Length 1 "Every input finds the source."

                                    Expect.equal
                                        (files[0].Settings.Printer.IndentSize,
                                         files[0].Settings.Printer.Width)
                                        (indent, 80)
                                        "The nearest csffrc supplies all formatting settings."

                                let expected = $"class C\n{{\n{String(' ', indent)}int x;\n}}\n"

                                let code, output, errors =
                                    capture (fun () -> Program.run [| "--write-stdout"; path |])

                                Expect.equal
                                    (code, output, errors)
                                    (0, expected, "")
                                    "Automatic csffrc selection bypasses irrelevant EditorConfig."

                                let currentDirectory = Environment.CurrentDirectory

                                try
                                    Environment.CurrentDirectory <- directory

                                    let code, output, errors =
                                        capture (fun () ->
                                            Console.SetIn(new StringReader(source))
                                            Program.run [| "--write-stdout"; "-" |])

                                    Expect.equal
                                        (code, output, errors)
                                        (0, expected, "")
                                        "Stdin uses the same automatic configuration selection."
                                finally
                                    Environment.CurrentDirectory <- currentDirectory

                            verify 2
                            write directory ".editorconfig" fallback |> ignore
                            verify 2

                            write directory ".csffrc.json" "{\"indentSize\":3,\"printWidth\":80}"
                            |> ignore

                            verify 3)
                }
            test "CLI explicit config skips automatic configuration parsing" {
                for name, invalid, automatic in
                    [
                        ".csffrc.json", "{", 2
                        ".csffrc.yaml", "indentSize: [", 2
                        ".editorconfig", "[[*.cs]\nindent_size = 6\n", 0
                    ] do
                    for worktree in [ false; true ] do
                        withDirectory (fun root ->
                            write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 6\n"
                            |> ignore

                            write root name invalid |> ignore
                            let repository = Path.Combine(root, "repo")
                            let source = "class C{int x;}"
                            let path = write repository "sub/a.cs" source
                            let directory = Path.GetDirectoryName path

                            if worktree then
                                write repository ".git" "gitdir: /fixture" |> ignore
                            else
                                Directory.CreateDirectory(Path.Combine(repository, ".git"))
                                |> ignore

                            let config =
                                write
                                    root
                                    "custom.json"
                                    "{\"indentSize\":6,\"overrides\":[{\"files\":\"repo/**/*.cs\",\"indentSize\":2}]}"

                            let verify () =
                                let code, _, _ =
                                    capture (fun () -> Program.run [| "--write-stdout"; path |])

                                Expect.equal
                                    code
                                    automatic
                                    "A csff-owned config fails; a foreign dialect's dead section does not."

                                let code, output, errors =
                                    capture (fun () ->
                                        Program.run
                                            [| "--write-stdout"; "--config-path"; config; path |])

                                let expected = "class C\n{\n  int x;\n}\n"

                                Expect.equal
                                    (code, output, errors)
                                    (0, expected, "")
                                    "Explicit configuration bypasses discarded files."

                                for input in [ path; repository; directory; root ] do
                                    let files =
                                        Discovery.files [| input |] (Some config) None false 1

                                    Expect.equal files.Length 1 "Every root finds the source."

                                    Expect.equal
                                        files[0].Settings.Printer.IndentSize
                                        2
                                        "Explicit overrides remain relative to the selected config."

                                let currentDirectory = Environment.CurrentDirectory

                                try
                                    Environment.CurrentDirectory <- directory

                                    let code, output, errors =
                                        capture (fun () ->
                                            Console.SetIn(new StringReader(source))

                                            Program.run
                                                [|
                                                    "--write-stdout"
                                                    "--config-path"
                                                    config
                                                    "-"
                                                |])

                                    Expect.equal
                                        (code, output, errors)
                                        (0, expected, "")
                                        "Stdin also bypasses automatic configuration."
                                finally
                                    Environment.CurrentDirectory <- currentDirectory

                            verify ()
                            write directory name invalid |> ignore
                            verify ())
            }
            test "Git's reading of an unclosed character class keeps a repo formattable" {
                for name, expected in [ ".gitignore", 0; ".csffignore", 2 ] do
                    withDirectory (fun root ->
                        let path = write root "a.cs" "class C{int x;}"
                        write root name "[a-z\n" |> ignore

                        let code, _, _ =
                            capture (fun () -> Program.run [| "--write-stdout"; path |])

                        Expect.equal code expected $"An unclosed character class in {name}.")

                withDirectory (fun root ->
                    write root "a.cs" "class C{int x;}" |> ignore
                    write root "[a-z.cs" "class D{int y;}" |> ignore
                    write root ".gitignore" "[a-z.cs\n" |> ignore

                    let names =
                        discover [| root |]
                        |> Array.map (fun file -> Path.GetFileName file.Path)
                        |> Array.sort

                    Expect.equal
                        names
                        [| "[a-z.cs"; "a.cs" |]
                        "A malformed rule hides nothing, as Git hides nothing.")

                withDirectory (fun root ->
                    write root "a.cs" "class C{int x;}" |> ignore
                    write root "[a-z.cs" "class D{int y;}" |> ignore
                    write root ".gitignore" "*.cs\n![a-z.cs\n" |> ignore

                    Expect.equal
                        (discover [| root |]).Length
                        0
                        "A malformed negation re-includes nothing.")
            }
            test "CLI explicit ignore skips discovered ignore parsing" {
                for name, unusable in [ ".csffignore", true; ".gitignore", false ] do
                    for worktree in [ false; true ] do
                        withDirectory (fun root ->
                            write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 2\n"
                            |> ignore

                            write root name "[\n" |> ignore
                            let repository = Path.Combine(root, "repo")
                            let path = write repository "sub/a.cs" "class C{int x;}"
                            let directory = Path.GetDirectoryName path
                            write directory "drop.cs" "class D{}" |> ignore

                            if worktree then
                                write repository ".git" "gitdir: /fixture" |> ignore
                            else
                                Directory.CreateDirectory(Path.Combine(repository, ".git"))
                                |> ignore

                            if name = ".gitignore" then
                                write repository name "[\n" |> ignore

                            let custom = write root "custom.ignore" "drop.cs\n"

                            let verify () =
                                let code, _, _ =
                                    capture (fun () -> Program.run [| "--write-stdout"; path |])

                                Expect.equal
                                    code
                                    (if unusable then 2 else 0)
                                    "An unusable applicable ignore fails where csff owns the file."

                                let code, output, errors =
                                    capture (fun () ->
                                        Program.run
                                            [| "--write-stdout"; "--ignore-path"; custom; path |])

                                Expect.equal
                                    (code, output, errors)
                                    (0, "class C\n{\n  int x;\n}\n", "")
                                    "Explicit ignores bypass discarded files without losing configuration."

                                for input in [ path; repository; directory; root ] do
                                    let files =
                                        Discovery.files [| input |] None (Some custom) false 1

                                    Expect.equal
                                        (files
                                         |> Array.map (fun file -> Path.GetFullPath file.Path))
                                        [| Path.GetFullPath path |]
                                        "Explicit ignores apply for every root and throughout the walk."

                                let currentDirectory = Environment.CurrentDirectory

                                try
                                    Environment.CurrentDirectory <- directory

                                    let code, output, errors =
                                        capture (fun () ->
                                            Console.SetIn(new StringReader("class C{int x;}"))

                                            Program.run
                                                [|
                                                    "--write-stdout"
                                                    "--ignore-path"
                                                    custom
                                                    "-"
                                                |])

                                    Expect.equal
                                        (code, output, errors)
                                        (0, "class C\n{\n  int x;\n}\n", "")
                                        "Stdin settings do not parse unused ignore rules."
                                finally
                                    Environment.CurrentDirectory <- currentDirectory

                            verify ()
                            write directory name "[\n" |> ignore
                            verify ())
            }
            test "CLI formats despite unsupported Git ignores above the repository" {
                withDirectory (fun root ->
                    write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 2\n" |> ignore
                    write root ".gitignore" "[\n" |> ignore
                    let repository = Path.Combine(root, "repo")
                    let path = write repository "a.cs" "class C{int x;}"
                    write repository ".git" "gitdir: /fixture" |> ignore

                    let code, output, errors =
                        capture (fun () -> Program.run [| "--write-stdout"; path |])

                    Expect.equal
                        (code, output, errors)
                        (0, "class C\n{\n  int x;\n}\n", "")
                        "An out-of-scope Git ignore cannot cause exit code 2.")
            }
            test "CLI current-directory and stdin inputs inherit settings across Git roots" {
                withDirectory (fun root ->
                    write root ".editorconfig" "root = true\n[*.cs]\nindent_size = 2\n" |> ignore
                    let repository = Path.Combine(root, "repo")
                    let source = "class C{int x;}"
                    let path = write repository "a.cs" source
                    write repository ".git" "gitdir: /fixture" |> ignore
                    let currentDirectory = Environment.CurrentDirectory

                    try
                        Environment.CurrentDirectory <- repository

                        let code, output, errors =
                            capture (fun () ->
                                Console.SetIn(new StringReader(source))
                                Program.run [| "--write-stdout" |])

                        let expected = "class C\n{\n  int x;\n}\n"

                        Expect.equal
                            (code, output, errors)
                            (0, expected, "")
                            "Stdin inherits EditorConfig from outside the repository."

                        let code, _, errors = capture (fun () -> Program.run [| "--no-cache" |])

                        Expect.equal code 0 errors

                        Expect.equal
                            (File.ReadAllText path)
                            expected
                            "With no paths, formatting uses the same inherited indentation."
                    finally
                        Environment.CurrentDirectory <- currentDirectory)
            }
            test "CLI stdout handles stdin and files, prints only formatted text and never writes" {
                withDirectory (fun root ->
                    let path = write root "a.cs" "class C{}"

                    let code, output, errors =
                        capture (fun () -> Program.run [| "--write-stdout"; path |])

                    Expect.equal
                        (code, output, errors)
                        (0, "class C { }\n", "")
                        "Stdout is an editor protocol."

                    Expect.equal
                        (File.ReadAllText path)
                        "class C{}"
                        "Stdout cannot rewrite the file."

                    let code, output, errors =
                        capture (fun () ->
                            Console.SetIn(new StringReader("class D{}"))
                            Program.run [| "--write-stdout"; "-" |])

                    Expect.equal (code, output, errors) (0, "class D { }\n", "") "Support piping.")
            }
            test "a positional dash is a filename rather than stdin" {
                withDirectory (fun root ->
                    let path = write root "-" "class File{}"
                    let current = Environment.CurrentDirectory

                    try
                        Environment.CurrentDirectory <- root

                        let code, _, errors =
                            capture (fun () -> Program.run [| "--no-cache"; "--"; "-" |])

                        Expect.equal code 0 errors

                        Expect.equal
                            (File.ReadAllText path)
                            "class File{}"
                            "A non-CSharp filename is ignored normally."

                        let code, output, _ =
                            capture (fun () ->
                                Console.SetIn(new StringReader("class Stdin{}"))
                                Program.run [| "--write-stdout"; "--"; "-" |])

                        Expect.equal code 2 "Stdout validates the positional file as CSharp input."
                        Expect.equal output "" "A positional filename does not consume stdin."
                    finally
                        Environment.CurrentDirectory <- current)
            }
            test "stdout file arguments honor generated-source inclusion" {
                withDirectory (fun root ->
                    for name, source in
                        [ "a.g.cs", "class C{}"; "b.cs", "// <auto-generated />\nclass C{}" ] do
                        let path = write root name source

                        let code, output, _ =
                            capture (fun () -> Program.run [| "--write-stdout"; path |])

                        Expect.equal code 2 "Generated file arguments require explicit inclusion."
                        Expect.equal output "" "Excluded generated source is never published."

                        let code, output, errors =
                            capture (fun () ->
                                Program.run [| "--write-stdout"; "--include-generated"; path |])

                        Expect.equal code 0 errors

                        Expect.stringContains
                            output
                            "class C { }"
                            "Explicit inclusion permits formatting."

                        Expect.equal
                            (File.ReadAllText path)
                            source
                            "Stdout never writes the source.")
            }
            test "relative cache roots and missing inputs produce bounded path handling" {
                withDirectory (fun root ->
                    let current = Environment.CurrentDirectory

                    try
                        Environment.CurrentDirectory <- root
                        write root "a.cs" "class C{}" |> ignore

                        Expect.equal
                            (Formatter.cacheDirectory "a.cs")
                            (Path.Combine(root, "out", "csff", "cache"))
                            "Relative files resolve before selecting a cache directory."

                        Expect.throwsT<FileNotFoundException>
                            (fun () ->
                                Discovery.files [| "missing.cs" |] None None false 1 |> ignore)
                            "A missing input is checked before loading parent settings."

                        if OperatingSystem.IsWindows() then
                            for drive in [ "Y:\\"; "Z:\\" ] do
                                if not (Directory.Exists drive) then
                                    Expect.throwsT<FileNotFoundException>
                                        (fun () ->
                                            Discovery.files [| drive |] None None false 1
                                            |> ignore)
                                        "A missing drive root has a file-not-found diagnostic."
                    finally
                        Environment.CurrentDirectory <- current)
            }
            for name in [ "ignored"; "bin"; "obj"; "excluded" ] do
                test $"CLI current directory obeys ignore barriers for {name}" {
                    withDirectory (fun root ->
                        write root ".gitignore" "ignored/\n" |> ignore
                        write root ".csffignore" "excluded/\n" |> ignore
                        let direct = write root ($"{name}/a.cs") "class C{}"
                        let nested = write root ($"{name}/sub/b.cs") "class D{}"
                        let originalDirectory = Environment.CurrentDirectory

                        try
                            for path in [ direct; nested ] do
                                Environment.CurrentDirectory <- Path.GetDirectoryName path

                                for args in [ [| "--no-cache" |]; [| "--no-cache"; "." |] ] do
                                    let code, output, errors = capture (fun () -> Program.run args)

                                    Expect.equal
                                        (code, output)
                                        (0, "")
                                        "An ignored root succeeds without output."

                                    Expect.stringContains
                                        errors
                                        "Formatted 0 C# files"
                                        "Default and dot inputs must discover no files."

                                    Expect.equal
                                        (File.ReadAllText direct)
                                        "class C{}"
                                        "Keep ignored source untouched."

                                    Expect.equal
                                        (File.ReadAllText nested)
                                        "class D{}"
                                        "Keep ignored descendants untouched."
                        finally
                            Environment.CurrentDirectory <- originalDirectory)
                }
            for name in [ ".gitignore"; ".csffignore" ] do
                test $"CLI dot-star ignores preserve format and check for {name}" {
                    withDirectory (fun root ->
                        write root name ".*\n" |> ignore
                        let path = write root "a.cs" "class C{}"
                        let hidden = write root ".hidden/a.cs" "class Hidden{}"
                        let originalDirectory = Environment.CurrentDirectory

                        try
                            Environment.CurrentDirectory <- root

                            for paths in [ [||]; [| "." |] ] do
                                File.WriteAllText(path, "class C{}")

                                let code, output, errors =
                                    capture (fun () ->
                                        Program.run (
                                            Array.append [| "--check"; "--no-cache" |] paths
                                        ))

                                Expect.equal
                                    (code, output)
                                    (1, "")
                                    "Check detects ordinary source."

                                Expect.stringContains
                                    errors
                                    path
                                    "Check reports the unformatted file."

                                Expect.equal
                                    (File.ReadAllText path)
                                    "class C{}"
                                    "Check cannot write."

                                let code, output, errors =
                                    capture (fun () ->
                                        Program.run (Array.append [| "--no-cache" |] paths))

                                Expect.equal (code, output) (0, "") "Formatting succeeds."

                                Expect.stringContains
                                    errors
                                    "Formatted 1 C# files"
                                    "Default and dot inputs discover ordinary source."

                                Expect.equal
                                    (File.ReadAllText path)
                                    "class C { }\n"
                                    "Format the file."

                                Expect.equal
                                    (File.ReadAllText hidden)
                                    "class Hidden{}"
                                    "Keep ignored descendants untouched."
                        finally
                            Environment.CurrentDirectory <- originalDirectory)
                }
            test "--write-stdout formats a binary chain deeper than a thread-pool stack" {
                withDirectory (fun root ->
                    let operands = String.Join(" + ", Array.init 20000 (fun i -> $"\"{i}\""))
                    let path = write root "Deep.cs" $"class C {{ string S = {operands}; }}"

                    let code, output, _ =
                        capture (fun () -> Program.run [| "--write-stdout"; path |])

                    Expect.equal code 0 "Printing runs on a large stack too."
                    Expect.stringContains output "\"19999\";" "The last operand survives.")
            }
            test "CLI exit codes distinguish check failures, invalid arguments and success" {
                withDirectory (fun root ->
                    let path = write root "a.cs" "class C{}"
                    let code, _, errors = capture (fun () -> Program.run [| "--check"; path |])
                    Expect.equal code 1 "A formatting diff fails the gate."
                    Expect.stringContains errors path "Name every unformatted file."

                    for args in
                        [
                            [| "--check"; "--write-stdout" |]
                            [| "--jobs"; "0" |]
                            [| "--config-path" |]
                            [| "--unknown" |]
                            [| "--write-stdout"; root |]
                        ] do
                        let code, _, _ = capture (fun () -> Program.run args)
                        Expect.equal code 2 "Invalid CLI usage is distinguishable."

                    let code, _, _ = capture (fun () -> Program.run [| path |])
                    Expect.equal code 0 "Write succeeds."
                    let code, _, _ = capture (fun () -> Program.run [| "--check"; path |])
                    Expect.equal code 0 "Formatted content passes.")
            }
            test "aliased root spellings keep one formatting cache" {
                withDirectory (fun root ->
                    write root "Mixed/a.cs" "class C { }\n" |> ignore
                    let child = Path.Combine(root, "Mixed")
                    let variant = Path.Combine(root, "mixed")

                    if caseSensitiveTemporaryVolume.Value then
                        skiptest "The temporary volume is case-sensitive;"

                    let cacheDirectory = Path.Combine(root, "cache")

                    let csff () =
                        capture (fun () ->
                            Program.run
                                [| "--check"; "--cache-path"; cacheDirectory; child; variant |])

                    let code, output, errors = csff ()
                    Expect.equal (code, output) (0, "") "Two spellings of one root succeed."

                    Expect.stringContains
                        errors
                        "Checked 1 C# files"
                        "Aliased roots discover the one file once."

                    for pass in 1..3 do
                        let code, output, errors = csff ()
                        Expect.equal (code, output) (0, "") $"Warm pass {pass} succeeds."

                        Expect.stringContains
                            errors
                            "(1 cached, 0 changed, 0 unverified)"
                            $"Warm pass {pass} finds the cache the pass before it wrote."

                    let caches = Directory.GetFiles cacheDirectory
                    Expect.equal caches.Length 1 "Spellings of one root share one cache slot."

                    Expect.equal
                        (Cache.read caches[0]).Count
                        1
                        "The one cache holds the one file it was written for.")
            }
            test "the three verification outcomes are reported and exited apart" {
                let proven = "class C{int x  =  1;}\n"

                let unprovable = "# \nclass C { }\n"

                let error = "class C { void M( }\n"

                let cases =
                    [
                        "all proven",
                        [ "Proven.cs", proven ],
                        0,
                        "(0 cached, 1 changed, 0 unverified)"
                        "one unprovable",
                        [ "Unprovable.cs", unprovable ],
                        Program.unverifiedExitCode,
                        "(0 cached, 0 changed, 1 unverified)"
                        "one error", [ "Error.cs", error ], 1, "(0 cached, 0 changed, 0 unverified)"
                        "one of each",
                        [ "Proven.cs", proven; "Unprovable.cs", unprovable; "Error.cs", error ],
                        1,
                        "(0 cached, 1 changed, 1 unverified)"
                    ]

                for name, files, expected, summary in cases do
                    withDirectory (fun root ->
                        let written =
                            files
                            |> List.map (fun (file, source) -> write root file source, source)

                        let code, output, errors =
                            capture (fun () -> Program.run [| "--no-cache"; root |])

                        Expect.equal code expected (name + ": the exit code names the outcome.")
                        Expect.equal output "" (name + ": nothing goes to standard output.")
                        Expect.stringContains errors summary (name + ": the summary counts it.")

                        for path, source in written do
                            match Path.GetFileName path with
                            | "Proven.cs" ->
                                Expect.notEqual
                                    (File.ReadAllText path)
                                    source
                                    (name + ": a proven file is written.")
                            | "Unprovable.cs" ->
                                Expect.stringContains
                                    errors
                                    "Unprovable.cs: formatting could not be proven to preserve the C# syntax"
                                    (name + ": an unproven file is named.")

                                Expect.equal
                                    (File.ReadAllText path)
                                    source
                                    (name + ": an unproven file keeps its own bytes.")
                            | _ ->
                                Expect.stringContains
                                    errors
                                    "Error.cs: Incomplete C# syntax"
                                    (name + ": an error is named as one.")

                                Expect.equal
                                    (File.ReadAllText path)
                                    source
                                    (name + ": a refused file keeps its own bytes."))
            }
            test "an unproven result is not also a changed one, or a cacheable one" {
                withDirectory (fun root ->
                    let source = "# \nclass C { }\n"
                    let path = write root "Unprovable.cs" source
                    let files, results = run [| root |] false true false 1
                    Expect.equal files.Length 1 "The fixture is discovered."
                    let result = results[0]

                    Expect.stringContains
                        result.Unverified
                        "could not be proven"
                        "The result carries the reason."

                    Expect.isNull result.Error "An unproven file is not an error."
                    Expect.isFalse result.Changed "An unproven file changed nothing."
                    Expect.isFalse result.Cacheable "An unproven file is not cacheable."
                    Expect.isFalse result.Cached "It was not answered from the cache."
                    Expect.isFalse result.Skipped "It was read and formatted, not skipped."
                    Expect.equal (File.ReadAllText path) source "Its bytes are its own.")
            }
            test "an unproven file is reported again by every run, never from the cache" {
                withDirectory (fun root ->
                    let source = "# \nclass C { }\n"
                    let path = write root "Unprovable.cs" source
                    let cacheDirectory = Path.Combine(root, "cache")

                    for pass in 1..2 do
                        let code, _, errors =
                            capture (fun () ->
                                Program.run [| "--cache-path"; cacheDirectory; root |])

                        Expect.equal
                            code
                            Program.unverifiedExitCode
                            $"Pass {pass} exits for the work it could not verify."

                        Expect.stringContains
                            errors
                            "could not be proven"
                            $"Pass {pass} names the unproven file."

                        Expect.stringContains
                            errors
                            "(0 cached, 0 changed, 1 unverified)"
                            $"Pass {pass} counts it rather than reading a cached answer."

                    Expect.equal (File.ReadAllText path) source "The file is never written.")
            }
            test "--write-stdout prints nothing it cannot prove" {
                withDirectory (fun root ->
                    let source = "# \nclass C { }\n"
                    let path = write root "Unprovable.cs" source

                    let code, output, errors =
                        capture (fun () -> Program.run [| "--write-stdout"; path |])

                    Expect.equal
                        code
                        Program.unverifiedExitCode
                        "Unproven output is not printed either."

                    Expect.equal output "" "Standard output stays empty."

                    Expect.stringContains
                        errors
                        "could not be proven"
                        "The reason goes to standard error.")
            }
            test "parallel in-place batch pipeline pre-reads and commits small and large files" {
                withDirectory (fun root ->
                    let cacheDirectory = Path.Combine(root, "cache")
                    let largeBodyA = String.replicate 700 "class LargeA{int M(){return 1;}}\n"
                    let largeBodyB = String.replicate 900 "class LargeB{int M(){return 2;}}\n"

                    write root "sub1/z_large_a.cs" largeBodyA |> ignore
                    write root "sub2/a_large_b.cs" largeBodyB |> ignore

                    for i = 0 to 39 do
                        let dir = if i % 2 = 0 then "sub1" else "sub2"

                        write
                            root
                            $"{dir}/small_{i:D2}.cs"
                            $"class S{i}{{int X(){{return {i};}}}}\n"
                        |> ignore

                    let bomPath = Path.Combine(root, "sub1", "bom_small.cs")
                    File.WriteAllText(bomPath, "class Bom{int Y()=>0;}\n", UTF8Encoding(true))

                    let utf16Path = Path.Combine(root, "sub2", "utf16_small.cs")

                    File.WriteAllText(
                        utf16Path,
                        "class U16{int Z()=>0;}\n",
                        UnicodeEncoding(false, true)
                    )

                    write root "sub1/unchanged.cs" "class Unchanged\n{\n    int K() => 0;\n}\n"
                    |> ignore

                    let files = Discovery.files [| root |] None None false 4
                    Expect.equal files.Length 45 "All 45 files are discovered."

                    let links = Array.zeroCreate<int> files.Length

                    let struct (order, _, largeCount) =
                        Formatter.scheduleOrderWithLengths files 4 links

                    Expect.equal largeCount 2 "Two files exceed the 16 KiB threshold."

                    Expect.equal
                        (Path.GetFileName files[order[0]].Path)
                        "a_large_b.cs"
                        "Longest large file is scheduled first."

                    Expect.equal
                        (Path.GetFileName files[order[1]].Path)
                        "z_large_a.cs"
                        "Second longest large file is scheduled second."

                    let smallScheduled =
                        order[largeCount..] |> Array.map (fun idx -> files[idx].Path)

                    let smallNatural =
                        files
                        |> Array.filter (fun f ->
                            let name = Path.GetFileName f.Path
                            name <> "a_large_b.cs" && name <> "z_large_a.cs")
                        |> Array.map (fun f -> f.Path)

                    Expect.sequenceEqual
                        smallScheduled
                        smallNatural
                        "Small files preserve their directory-contiguous path order."

                    let code1, _, errors1 =
                        capture (fun () ->
                            Program.run [| "--cache-path"; cacheDirectory; "--jobs"; "4"; root |])

                    Expect.equal code1 0 errors1

                    Expect.stringContains
                        errors1
                        "(0 cached, 44 changed, 0 unverified)"
                        "All 44 unformatted files are committed."

                    let bomBytes = File.ReadAllBytes bomPath

                    Expect.isTrue
                        (bomBytes.Length > 3
                         && bomBytes[0] = 0xefuy
                         && bomBytes[1] = 0xbbuy
                         && bomBytes[2] = 0xbfuy)
                        "UTF-8 BOM is preserved by CommitSlot commits."

                    let utf16Bytes = File.ReadAllBytes utf16Path

                    Expect.isTrue
                        (utf16Bytes.Length > 2 && utf16Bytes[0] = 0xffuy && utf16Bytes[1] = 0xfeuy)
                        "UTF-16 LE BOM and encoding are preserved by CommitSlot commits."

                    let sub1 = Path.Combine(root, "sub1")

                    for nested in [ "sub1/d1"; "sub1/d2"; "sub1/d3"; "sub2/d1"; "sub2/d2" ] do
                        write root $"{nested}/extra.cs" "class Extra { int V() => 1; }\n" |> ignore

                    let overlapFiles = Discovery.files [| sub1; root |] None None false 4

                    Expect.equal
                        overlapFiles.Length
                        50
                        "Overlapping roots deduplicate and never re-enter cached walks."

                    let code2, _, errors2 =
                        capture (fun () ->
                            Program.run [| "--cache-path"; cacheDirectory; "--jobs"; "4"; root |])

                    Expect.equal code2 0 errors2

                    Expect.stringContains
                        errors2
                        "(45 cached, 5 changed, 0 unverified)"
                        "Pass 2 answers the 45 previously cached files from the cache written in Pass 1 and formats the 5 new files."

                    let withMissing =
                        Array.append
                            overlapFiles
                            [|
                                { overlapFiles[0] with
                                    Path = Path.Combine(root, "sub1", "missing_small.cs")
                                }
                            |]

                    let resultsWithError =
                        Formatter.run
                            [| sub1; root |]
                            withMissing
                            false
                            true
                            false
                            4
                            None
                            System.Threading.CancellationToken.None

                    Expect.isNotNull
                        resultsWithError[resultsWithError.Length - 1].Error
                        "A pre-read failure in readerThreads is propagated through CommitSlot.ReadError to the file's result.")
            }
        ]
    |> testSequenced

let tests = TestList([ fileTests; commandTests ], Normal)
