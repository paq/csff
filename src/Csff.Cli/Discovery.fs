namespace Csff.Cli

open System
open System.Buffers
open System.Buffers.Binary
open System.Collections.Concurrent
open System.Collections.Generic
open System.IO
open System.IO.Enumeration
open System.Runtime.ExceptionServices
open System.Runtime.InteropServices
open System.Text
open System.Text.RegularExpressions
open System.Threading
open System.Threading.Tasks
open Csff.Lexer
open Microsoft.Win32.SafeHandles

[<NoEquality; NoComparison>]
type internal IgnoreRule =
    {
        mutable Regex: Regex
        Fast: FastGlob
        DirectoryOnly: bool
        Ignore: bool
    }

    member this.Pattern = Glob.ensureRegex &this.Regex this.Fast

[<NoEquality; NoComparison>]
type internal IgnoreFile =
    {
        Directory: string
        Rules: IgnoreRule array
        CsRules: IgnoreRule array
    }

[<NoEquality; NoComparison>]
type internal DirectorySettings =
    {
        Config: Config option
        Editor: EditorGroup option
        UniformCsSettings: Settings option voption
        CsffIgnore: IgnoreFile option
        GitIgnores: IgnoreFile list
    }

    static member Empty =
        {
            Config = None
            Editor = None
            UniformCsSettings = ValueSome(Some Settings.Default)
            CsffIgnore = None
            GitIgnores = []
        }

[<Struct>]
type internal InputFile =
    {
        Path: string
        Settings: Settings
        Root: int
    }

[<Struct>]
type internal DirEntry =
    {
        Path: string
        Length: int64
        IsDirectory: bool
    }

[<NoEquality; NoComparison>]
type private DirectoryState =
    {
        Config: Lazy<Config option>
        Editor: Lazy<EditorGroup option>
        CsffIgnore: Lazy<IgnoreFile option>
        GitIgnores: Lazy<IgnoreFile list>
        Settings: Lazy<DirectorySettings>
    }

[<NoEquality; NoComparison>]
type private DirectoryFiles =
    {
        Files: InputFile array
        Lengths: int64 array
        Children: DirectoryFiles array
    }

[<Struct; StructLayout(LayoutKind.Sequential)>]
type private DirectoryIdentity =
    {
        Volume: uint64
        FileLow: uint64
        FileHigh: uint64
    }

module internal Discovery =
    [<DllImport("kernel32.dll", CharSet = CharSet.Unicode, ExactSpelling = true)>]
    extern SafeFileHandle private CreateFileW(
        string path,
        uint32 access,
        uint32 share,
        nativeint security,
        uint32 disposition,
        uint32 flags,
        nativeint template
    )

    [<DllImport("kernel32.dll", ExactSpelling = true)>]
    extern int private GetFileInformationByHandleEx(
        SafeFileHandle handle,
        int informationClass,
        DirectoryIdentity& information,
        uint32 size
    )

    let private directoryIdentity path =
        use handle = CreateFileW(path, 0u, 7u, 0n, 3u, 0x02200000u, 0n)
        let mutable identity = Unchecked.defaultof<DirectoryIdentity>

        if
            not handle.IsInvalid
            && GetFileInformationByHandleEx(handle, 18, &identity, uint32 sizeof<DirectoryIdentity>)
               <> 0
        then
            Some identity
        else
            None

    let readIgnore directory (path: string) =
        let rules = ResizeArray<IgnoreRule>()

        let git =
            String.Equals(Path.GetFileName path, ".gitignore", StringComparison.Ordinal)

        for line in File.ReadAllLines path do
            let mutable length = line.Length

            let mutable trimming = true

            while trimming && length > 0 && line[length - 1] = ' ' do
                let mutable before = length - 2

                while before >= 0 && line[before] = '\\' do
                    before <- before - 1

                if (length - 2 - before) % 2 = 1 then
                    trimming <- false
                else
                    length <- length - 1

            let text = line.Substring(0, length)

            if text.Length > 0 && not (text.StartsWith('#')) then
                let negated = text.StartsWith('!')
                let pattern = if negated then text.Substring(1) else text

                if pattern.Length > 0 then
                    let directoryOnly = pattern.EndsWith('/')
                    let pattern = pattern.TrimEnd('/')
                    let anchored = pattern.StartsWith('/') || pattern.Contains('/')
                    let pattern = pattern.TrimStart('/')

                    let expanded = if anchored then pattern else "**/" + pattern

                    let fast = Glob.fastCompileWithFlags false git expanded

                    let regex = if git then null else Glob.compileIgnore expanded

                    rules.Add
                        {
                            Regex = regex
                            Fast = fast
                            DirectoryOnly = directoryOnly
                            Ignore = not negated
                        }

        let allRules = rules.ToArray()

        let csRules =
            allRules
            |> Array.filter (fun rule ->
                not rule.DirectoryOnly && Glob.canMatchLowercaseCs rule.Fast)

        {
            Directory = directory
            Rules = allRules
            CsRules = csRules
        }

    type Context(autoConfig, autoIgnore) =
        let directories = Dictionary<string, Lazy<DirectoryState>>(StringComparer.Ordinal)

        let rec resolve directory =
            let entry =
                lock directories (fun () ->
                    match directories.TryGetValue directory with
                    | true, entry -> entry
                    | _ ->
                        let entry = lazy (create directory)
                        directories.Add(directory, entry)
                        entry)

            entry.Value

        and create directory =
            let parent =
                lazy
                    match Path.GetDirectoryName directory with
                    | null -> None
                    | parent -> Some(resolve parent)

            let config =
                lazy
                    if autoConfig then
                        Configuration.find directory
                        |> Option.orElseWith (fun () ->
                            parent.Value |> Option.bind (fun state -> state.Config.Value))
                    else
                        None

            let editor =
                lazy
                    if not autoConfig || Option.isSome config.Value then
                        None
                    else
                        let root, sections = Configuration.readEditor directory

                        let inherited =
                            if root then
                                None
                            else
                                parent.Value |> Option.bind (fun state -> state.Editor.Value)

                        if sections.Length = 0 then
                            inherited
                        else
                            Some
                                {
                                    Sections = sections
                                    Parent = inherited
                                }

            let csffIgnore =
                lazy
                    if autoIgnore then
                        let path = Path.Combine(directory, ".csffignore")

                        if File.Exists path then
                            Some(readIgnore directory path)
                        else
                            parent.Value |> Option.bind (fun state -> state.CsffIgnore.Value)
                    else
                        None

            let gitIgnores =
                lazy
                    if autoIgnore then
                        let path = Path.Combine(directory, ".gitignore")

                        let local =
                            if File.Exists path then
                                Some(readIgnore directory path)
                            else
                                None

                        let inherited =
                            if Path.Exists(Path.Combine(directory, ".git")) then
                                []
                            else
                                parent.Value
                                |> Option.map (fun state -> state.GitIgnores.Value)
                                |> Option.defaultValue []

                        match local with
                        | Some ignore -> ignore :: inherited
                        | None -> inherited
                    else
                        []

            {
                Config = config
                Editor = editor
                CsffIgnore = csffIgnore
                GitIgnores = gitIgnores
                Settings =
                    lazy
                        let cfg = config.Value
                        let ed = editor.Value

                        {
                            Config = cfg
                            Editor = ed
                            UniformCsSettings =
                                match cfg with
                                | Some _ -> ValueNone
                                | None -> Configuration.tryUniformCsSettings ed directory
                            CsffIgnore = csffIgnore.Value
                            GitIgnores = gitIgnores.Value
                        }
            }

        member _.Inherited directory =
            let directory = Path.GetFullPath directory |> Path.TrimEndingDirectorySeparator
            (resolve directory).Settings.Value

        member _.CsffIgnore directory =
            let directory = Path.GetFullPath directory |> Path.TrimEndingDirectorySeparator
            (resolve directory).CsffIgnore.Value

    let private parentDirectoryOf (path: string) =
        match Path.GetDirectoryName(Path.GetFullPath path) with
        | null -> Environment.CurrentDirectory
        | directory when directory.Length = 0 -> Environment.CurrentDirectory
        | directory -> directory

    let settingsForFile (path: string) configPath =
        let fullPath = Path.GetFullPath path
        let specified = configPath |> Option.map Configuration.read
        let context = Context(Option.isNone specified, false)
        let state = context.Inherited(parentDirectoryOf fullPath)

        let config = specified |> Option.orElse state.Config

        match config with
        | Some _ -> Some(Configuration.forFile config fullPath)
        | None -> Configuration.editorForFile state.Editor fullPath

    let private matches (ignore: IgnoreFile) (path: string) isDirectory =
        if
            not isDirectory
            && path.EndsWith(".cs", StringComparison.Ordinal)
            && not (Glob.hasNewline path)
        then
            let rules = ignore.CsRules

            if rules.Length = 0 then
                ValueNone
            else
                match Glob.relative ignore.Directory path with
                | None
                | Some "." -> ValueNone
                | Some relative ->
                    let mutable index = rules.Length - 1
                    let mutable result = ValueNone

                    while result.IsNone && index >= 0 do
                        let rule = rules[index]

                        if Glob.isMatchScanned false rule.Fast &rule.Regex relative then
                            result <- ValueSome rule.Ignore

                        index <- index - 1

                    result
        else
            match Glob.relative ignore.Directory path with
            | None
            | Some "." -> ValueNone
            | Some relative ->
                let rules = ignore.Rules
                let newline = Glob.hasNewline relative
                let mutable index = rules.Length - 1
                let mutable result = ValueNone

                while result.IsNone && index >= 0 do
                    let rule = rules[index]

                    if
                        (isDirectory || not rule.DirectoryOnly)
                        && Glob.isMatchScanned newline rule.Fast &rule.Regex relative
                    then
                        result <- ValueSome rule.Ignore

                    index <- index - 1

                result

    let private ignored (state: DirectorySettings) path isDirectory =
        match state.CsffIgnore with
        | Some ignore ->
            match matches ignore path isDirectory with
            | ValueSome matched -> matched
            | ValueNone ->
                let rec loop (ignores: IgnoreFile list) =
                    match ignores with
                    | [] -> false
                    | head :: tail ->
                        match matches head path isDirectory with
                        | ValueSome matched -> matched
                        | ValueNone -> loop tail

                loop state.GitIgnores
        | None ->
            let rec loop (ignores: IgnoreFile list) =
                match ignores with
                | [] -> false
                | head :: tail ->
                    match matches head path isDirectory with
                    | ValueSome matched -> matched
                    | ValueNone -> loop tail

            loop state.GitIgnores

    let private matchesCanonical
        (ignore: IgnoreFile)
        (path: string)
        (segOffset: int)
        isCsFile
        isDirectory
        =
        let ignoreDir = ignore.Directory
        let sep = Path.DirectorySeparatorChar

        if
            ignoreDir.Length > 1
            && ignoreDir[ignoreDir.Length - 1] <> sep
            && path.Length > ignoreDir.Length + 1
            && path[ignoreDir.Length] = sep
            && path.StartsWith(ignoreDir, StringComparison.Ordinal)
        then
            let relSpan = path.AsSpan(ignoreDir.Length + 1)
            let segment = path.AsSpan(segOffset)

            if isCsFile then
                let rules = ignore.CsRules
                let mutable index = rules.Length - 1
                let mutable result = ValueNone

                while result.IsNone && index >= 0 do
                    let rule = rules[index]

                    if Glob.isMatchSpan rule.Fast &rule.Regex relSpan segment then
                        result <- ValueSome rule.Ignore

                    index <- index - 1

                result
            else
                let rules = ignore.Rules
                let mutable index = rules.Length - 1
                let mutable result = ValueNone

                while result.IsNone && index >= 0 do
                    let rule = rules[index]

                    if
                        (isDirectory || not rule.DirectoryOnly)
                        && Glob.isMatchSpan rule.Fast &rule.Regex relSpan segment
                    then
                        result <- ValueSome rule.Ignore

                    index <- index - 1

                result
        else
            matches ignore path isDirectory

    let private ignoredCanonical
        (state: DirectorySettings)
        (path: string)
        (segOffset: int)
        isCsFile
        isDirectory
        =
        let mutable decided = ValueNone

        match state.CsffIgnore with
        | Some ignore -> decided <- matchesCanonical ignore path segOffset isCsFile isDirectory
        | None -> ()

        let mutable ignores = state.GitIgnores

        while decided.IsNone && not ignores.IsEmpty do
            decided <- matchesCanonical ignores.Head path segOffset isCsFile isDirectory
            ignores <- ignores.Tail

        match decided with
        | ValueSome matched -> matched
        | ValueNone -> false

    let private alwaysIgnoredComparison =
        if OperatingSystem.IsWindows() || OperatingSystem.IsMacOS() then
            StringComparison.OrdinalIgnoreCase
        else
            StringComparison.Ordinal

    let private alwaysIgnored (name: ReadOnlySpan<char>) =
        name.Equals(".git".AsSpan(), alwaysIgnoredComparison)
        || name.Equals("bin".AsSpan(), alwaysIgnoredComparison)
        || name.Equals("obj".AsSpan(), alwaysIgnoredComparison)
        || name.Equals("node_modules".AsSpan(), alwaysIgnoredComparison)
        || name.Equals(".cache".AsSpan(), alwaysIgnoredComparison)

    let private generatedName (path: ReadOnlySpan<char>) =
        let name = Path.GetFileNameWithoutExtension path

        if name.Length >= 2 then
            let last = int name[name.Length - 1] ||| 0x20

            (last = int 'g'
             && name.EndsWith(".g".AsSpan(), StringComparison.OrdinalIgnoreCase))
            || (last = int 'r'
                && name.EndsWith(".designer".AsSpan(), StringComparison.OrdinalIgnoreCase))
            || (last = int 'd'
                && name.EndsWith(".generated".AsSpan(), StringComparison.OrdinalIgnoreCase))
            || (last = int 'i'
                && name.EndsWith(".g.i".AsSpan(), StringComparison.OrdinalIgnoreCase))
            || (name.Length >= 23
                && (int name[0] ||| 0x20) = int 't'
                && name.StartsWith(
                    "TemporaryGeneratedFile_".AsSpan(),
                    StringComparison.OrdinalIgnoreCase
                ))
        else
            false

    let private csharpSource includeGenerated (path: string) =
        let span = path.AsSpan()

        Path.GetExtension(span).Equals(".cs".AsSpan(), StringComparison.OrdinalIgnoreCase)
        && (includeGenerated || not (generatedName span))

    let enumerate directory =
        let enumerable =
            FileSystemEnumerable<struct (string * bool)>(
                directory,
                FileSystemEnumerable<struct (string * bool)>.FindTransform(fun entry ->
                    struct (entry.ToFullPath(), entry.IsDirectory)),
                EnumerationOptions(
                    AttributesToSkip = FileAttributes.ReparsePoint,
                    IgnoreInaccessible = false
                )
            )

        enumerable.ShouldIncludePredicate <-
            FileSystemEnumerable<struct (string * bool)>.FindPredicate(fun entry ->
                entry.IsDirectory
                || Path
                    .GetExtension(entry.FileName)
                    .Equals(".cs".AsSpan(), StringComparison.OrdinalIgnoreCase))

        enumerable :> seq<struct (string * bool)>

    [<Struct; StructLayout(LayoutKind.Sequential)>]
    type private DarwinAttrList =
        {
            mutable BitmapCount: uint16
            mutable Reserved: uint16
            mutable CommonAttr: uint32
            mutable VolAttr: uint32
            mutable DirAttr: uint32
            mutable FileAttr: uint32
            mutable ForkAttr: uint32
        }

    [<DllImport("libSystem.B.dylib", EntryPoint = "open", ExactSpelling = true)>]
    extern int private darwinOpenDirectory(string path, int oflag)

    [<DllImport("libSystem.B.dylib", EntryPoint = "close", ExactSpelling = true)>]
    extern int private darwinCloseDirectory(int fd)

    [<DllImport("libSystem.B.dylib", EntryPoint = "getattrlistbulk", ExactSpelling = true)>]
    extern int private darwinGetAttrListBulk(
        int dirfd,
        DarwinAttrList& attrList,
        byte& attrBuf,
        unativeint attrBufSize,
        uint64 options
    )

    [<DllImport("libSystem.B.dylib", EntryPoint = "opendir", ExactSpelling = true)>]
    extern nativeint private darwinOpenDir(string path)

    [<DllImport("libSystem.B.dylib", EntryPoint = "readdir", ExactSpelling = true)>]
    extern nativeint private darwinReadDirArm64(nativeint dirp)

    [<DllImport("libSystem.B.dylib", EntryPoint = "readdir$INODE64", ExactSpelling = true)>]
    extern nativeint private darwinReadDirX64(nativeint dirp)

    [<DllImport("libSystem.B.dylib", EntryPoint = "closedir", ExactSpelling = true)>]
    extern int private darwinCloseDir(nativeint dirp)

    [<DllImport("libSystem.B.dylib",
                EntryPoint = "pthread_set_qos_class_self_np",
                ExactSpelling = true)>]
    extern int private darwinSetQosClassSelf(uint32 qosClass, int relativePriority)

    let private isArm64 = RuntimeInformation.ProcessArchitecture = Architecture.Arm64

    let private darwinReadDirAvailable =
        OperatingSystem.IsMacOS()
        && (isArm64 || RuntimeInformation.ProcessArchitecture = Architecture.X64)
        && (let mutable lib = 0n
            let mutable symOpen = 0n
            let mutable symClose = 0n
            let mutable symRead = 0n

            NativeLibrary.TryLoad("libSystem.B.dylib", &lib)
            && NativeLibrary.TryGetExport(lib, "opendir", &symOpen)
            && NativeLibrary.TryGetExport(lib, "closedir", &symClose)
            && NativeLibrary.TryGetExport(
                lib,
                (if isArm64 then "readdir" else "readdir$INODE64"),
                &symRead
            ))

    let private darwinBulkAvailable =
        darwinReadDirAvailable
        && (let mutable lib = 0n
            let mutable symOpen = 0n
            let mutable symClose = 0n
            let mutable symBulk = 0n

            NativeLibrary.TryLoad("libSystem.B.dylib", &lib)
            && NativeLibrary.TryGetExport(lib, "open", &symOpen)
            && NativeLibrary.TryGetExport(lib, "close", &symClose)
            && NativeLibrary.TryGetExport(lib, "getattrlistbulk", &symBulk))

    let private boostThread () =
        if darwinReadDirAvailable then
            try
                darwinSetQosClassSelf (0x21u, 0) |> ignore
            with
            | :? EntryPointNotFoundException
            | :? DllNotFoundException -> ()

    let private metadataBit (name: ReadOnlySpan<char>) =
        if name.Length >= 4 && name[0] = '.' then
            if name.Equals(".editorconfig".AsSpan(), StringComparison.OrdinalIgnoreCase) then
                2
            elif name.Equals(".gitignore".AsSpan(), StringComparison.OrdinalIgnoreCase) then
                8
            elif name.Equals(".git".AsSpan(), StringComparison.OrdinalIgnoreCase) then
                16
            elif name.Equals(".csffignore".AsSpan(), StringComparison.OrdinalIgnoreCase) then
                4
            elif
                name.Equals(".csffrc.json".AsSpan(), StringComparison.OrdinalIgnoreCase)
                || name.Equals(".csffrc.yaml".AsSpan(), StringComparison.OrdinalIgnoreCase)
                || name.Equals(".csffrc.yml".AsSpan(), StringComparison.OrdinalIgnoreCase)
            then
                1
            else
                0
        else
            0

    let private defaultEnumerationOptions =
        EnumerationOptions(AttributesToSkip = enum<FileAttributes> 0, IgnoreInaccessible = false)

    let private dirEntryTransform =
        FileSystemEnumerable<DirEntry>.FindTransform(fun entry ->
            let isDir = entry.IsDirectory

            {
                Path = entry.ToFullPath()
                Length = if isDir then -1L else entry.Length
                IsDirectory = isDir
            })

    let private enumerateArrayFallback includeGenerated directory =
        let mutable metaMask = 0

        let enumerable =
            FileSystemEnumerable<DirEntry>(directory, dirEntryTransform, defaultEnumerationOptions)

        enumerable.ShouldIncludePredicate <-
            FileSystemEnumerable<DirEntry>.FindPredicate(fun entry ->
                let name = entry.FileName
                let bit = metadataBit name

                if bit <> 0 then
                    metaMask <- metaMask ||| bit

                if entry.IsDirectory then
                    not (alwaysIgnored name)
                    && (entry.Attributes &&& FileAttributes.ReparsePoint) = enum<FileAttributes> 0
                else
                    Path
                        .GetExtension(name)
                        .Equals(".cs".AsSpan(), StringComparison.OrdinalIgnoreCase)
                    && (includeGenerated || not (generatedName name))
                    && (entry.Attributes &&& FileAttributes.ReparsePoint) = enum<FileAttributes> 0)

        let contents = ResizeArray<DirEntry>()

        for item in enumerable do
            contents.Add item

        struct (metaMask, contents.ToArray())

    let private enumerateArrayReadDir includeGenerated (directory: string) =
        if not darwinReadDirAvailable then
            enumerateArrayFallback includeGenerated directory
        else
            let dirp = darwinOpenDir directory

            if dirp = 0n then
                enumerateArrayFallback includeGenerated directory
            else
                let mutable metaMask = 0
                let mutable fallback = false
                let items = ResizeArray<DirEntry>()
                let mutable prefix: string = null

                try
                    Marshal.SetLastSystemError 0
                    let mutable looping = true

                    while looping do
                        let ptr =
                            if isArm64 then
                                darwinReadDirArm64 dirp
                            else
                                darwinReadDirX64 dirp

                        if ptr = 0n then
                            if Marshal.GetLastSystemError() <> 0 then
                                Marshal.SetLastSystemError 0

                                let retry =
                                    if isArm64 then
                                        darwinReadDirArm64 dirp
                                    else
                                        darwinReadDirX64 dirp

                                if retry <> 0n || Marshal.GetLastSystemError() <> 0 then
                                    fallback <- true

                            looping <- false
                        else
                            let namlen = int (uint16 (Marshal.ReadInt16(ptr, 18)))
                            let dtype = Marshal.ReadByte(ptr, 20)
                            let b0 = if namlen > 0 then Marshal.ReadByte(ptr, 21) else 0uy

                            let isDotOrDotDot =
                                (namlen = 1 && b0 = 46uy)
                                || (namlen = 2 && b0 = 46uy && Marshal.ReadByte(ptr, 22) = 46uy)

                            if not isDotOrDotDot then
                                if dtype <> 4uy && dtype <> 8uy && dtype <> 10uy then
                                    fallback <- true
                                    looping <- false
                                else
                                    let mutable decodedName: string = null

                                    if namlen >= 4 && b0 = 46uy then
                                        let s = Marshal.PtrToStringUTF8(ptr + 21n, namlen)
                                        decodedName <- s
                                        let bit = metadataBit (s.AsSpan())

                                        if bit <> 0 then
                                            metaMask <- metaMask ||| bit

                                    if dtype = 4uy then
                                        let s =
                                            if not (isNull decodedName) then
                                                decodedName
                                            else
                                                Marshal.PtrToStringUTF8(ptr + 21n, namlen)

                                        if not (alwaysIgnored (s.AsSpan())) then
                                            if isNull prefix then
                                                prefix <-
                                                    if directory.EndsWith('/') then
                                                        directory
                                                    else
                                                        directory + "/"

                                            items.Add
                                                {
                                                    Path = prefix + s
                                                    Length = -1L
                                                    IsDirectory = true
                                                }
                                    elif dtype = 8uy && namlen >= 3 then
                                        let dot = Marshal.ReadByte(ptr, 21 + namlen - 3)

                                        let c = Marshal.ReadByte(ptr, 21 + namlen - 2) ||| 0x20uy

                                        let sByte =
                                            Marshal.ReadByte(ptr, 21 + namlen - 1) ||| 0x20uy

                                        if dot = 46uy && c = 99uy && sByte = 115uy then
                                            let s =
                                                if not (isNull decodedName) then
                                                    decodedName
                                                else
                                                    Marshal.PtrToStringUTF8(ptr + 21n, namlen)

                                            if
                                                includeGenerated || not (generatedName (s.AsSpan()))
                                            then
                                                if isNull prefix then
                                                    prefix <-
                                                        if directory.EndsWith('/') then
                                                            directory
                                                        else
                                                            directory + "/"

                                                items.Add
                                                    {
                                                        Path = prefix + s
                                                        Length = -1L
                                                        IsDirectory = false
                                                    }
                finally
                    darwinCloseDir dirp |> ignore

                if fallback then
                    enumerateArrayFallback includeGenerated directory
                else
                    struct (metaMask, items.ToArray())

    let private joinChildPath (directory: string) hasTrailingSlash (nameSpan: ReadOnlySpan<char>) =
        if hasTrailingSlash then
            String.Concat(directory.AsSpan(), nameSpan)
        else
            String.Concat(directory.AsSpan(), "/".AsSpan(), nameSpan)

    let private decodeUtf8Name
        (attrBuf: byte array)
        nameStart
        namlen
        (charBuf: char array byref)
        (decodedLen: int byref)
        =
        if decodedLen < 0 then
            if charBuf.Length < namlen + 1 then
                PoolArray.grow &charBuf 0 (namlen + 1)

            let nameBytes = ReadOnlySpan<byte>(attrBuf, nameStart, namlen)
            let mutable written = 0

            decodedLen <-
                if Ascii.ToUtf16(nameBytes, charBuf.AsSpan(), &written) = OperationStatus.Done then
                    written
                else
                    Encoding.UTF8.GetChars(nameBytes, charBuf.AsSpan())

        decodedLen

    let private enumerateArrayFor includeGenerated (directory: string) =
        if not darwinBulkAvailable then
            enumerateArrayReadDir includeGenerated directory
        else
            let fd = darwinOpenDirectory (directory, 0x01100004)

            if fd < 0 then
                enumerateArrayReadDir includeGenerated directory
            else
                let mutable attrBuf = SharedBuckets<byte>.Rent 65536
                let mutable charBuf = SharedBuckets<char>.Rent 1024
                let mutable metaMask = 0
                let mutable fallback = false
                let items = ResizeArray<DirEntry>()
                let hasTrailingSlash = directory.EndsWith('/')

                try
                    let mutable attrList = Unchecked.defaultof<DarwinAttrList>
                    attrList.BitmapCount <- 5us
                    attrList.CommonAttr <- 0xA0000009u
                    attrList.FileAttr <- 0x00000200u

                    let mutable looping = true

                    while looping do
                        let count =
                            darwinGetAttrListBulk (
                                fd,
                                &attrList,
                                &attrBuf[0],
                                unativeint attrBuf.Length,
                                0UL
                            )

                        if count = 0 then
                            looping <- false
                        elif count < 0 then
                            fallback <- true
                            looping <- false
                        else
                            let mutable offset = 0
                            let mutable entryIdx = 0

                            while entryIdx < count && not fallback do
                                if offset + 24 > attrBuf.Length then
                                    fallback <- true
                                    looping <- false
                                else
                                    let recLen =
                                        int (
                                            BinaryPrimitives.ReadUInt32LittleEndian(
                                                ReadOnlySpan<byte>(attrBuf, offset, 4)
                                            )
                                        )

                                    let recEnd = offset + recLen

                                    if recLen < 24 || recEnd > attrBuf.Length then
                                        fallback <- true
                                        looping <- false
                                    else
                                        let retCommon =
                                            BinaryPrimitives.ReadUInt32LittleEndian(
                                                ReadOnlySpan<byte>(attrBuf, offset + 4, 4)
                                            )

                                        let retVol =
                                            BinaryPrimitives.ReadUInt32LittleEndian(
                                                ReadOnlySpan<byte>(attrBuf, offset + 8, 4)
                                            )

                                        let retDir =
                                            BinaryPrimitives.ReadUInt32LittleEndian(
                                                ReadOnlySpan<byte>(attrBuf, offset + 12, 4)
                                            )

                                        let retFile =
                                            BinaryPrimitives.ReadUInt32LittleEndian(
                                                ReadOnlySpan<byte>(attrBuf, offset + 16, 4)
                                            )

                                        let mutable pos = offset + 24
                                        let mutable entryErr = 0u

                                        if (retCommon &&& 0x20000000u) <> 0u then
                                            if pos + 4 > recEnd then
                                                entryErr <- 1u
                                            else
                                                entryErr <-
                                                    BinaryPrimitives.ReadUInt32LittleEndian(
                                                        ReadOnlySpan<byte>(attrBuf, pos, 4)
                                                    )

                                                pos <- pos + 4

                                        if
                                            entryErr <> 0u
                                            || (retCommon &&& ~~~0xA0000009u) <> 0u
                                            || (retCommon &&& 0x00000009u) <> 0x00000009u
                                            || retVol <> 0u
                                            || retDir <> 0u
                                            || pos + 12 > recEnd
                                        then
                                            fallback <- true
                                            looping <- false
                                        else
                                            let dataOffset =
                                                BinaryPrimitives.ReadInt32LittleEndian(
                                                    ReadOnlySpan<byte>(attrBuf, pos, 4)
                                                )

                                            let dataLength =
                                                int (
                                                    BinaryPrimitives.ReadUInt32LittleEndian(
                                                        ReadOnlySpan<byte>(attrBuf, pos + 4, 4)
                                                    )
                                                )

                                            let nameStart = pos + dataOffset
                                            pos <- pos + 8

                                            let objType =
                                                BinaryPrimitives.ReadUInt32LittleEndian(
                                                    ReadOnlySpan<byte>(attrBuf, pos, 4)
                                                )

                                            pos <- pos + 4

                                            if
                                                dataOffset < 8
                                                || dataLength < 1
                                                || nameStart < offset + 24
                                                || nameStart + dataLength > recEnd
                                            then
                                                fallback <- true
                                                looping <- false
                                            else
                                                let rawName =
                                                    ReadOnlySpan<byte>(
                                                        attrBuf,
                                                        nameStart,
                                                        dataLength
                                                    )

                                                let nulIdx = rawName.IndexOf 0uy

                                                let namlen =
                                                    if nulIdx >= 0 then nulIdx else dataLength

                                                let b0 =
                                                    if namlen > 0 then attrBuf[nameStart] else 0uy

                                                let isDotOrDotDot =
                                                    (namlen = 1 && b0 = 46uy)
                                                    || (namlen = 2
                                                        && b0 = 46uy
                                                        && attrBuf[nameStart + 1] = 46uy)

                                                if not isDotOrDotDot then
                                                    if
                                                        objType <> 1u
                                                        && objType <> 2u
                                                        && objType <> 5u
                                                    then
                                                        fallback <- true
                                                        looping <- false
                                                    else
                                                        let mutable decodedLen = -1

                                                        if namlen >= 4 && b0 = 46uy then
                                                            let cLen =
                                                                decodeUtf8Name
                                                                    attrBuf
                                                                    nameStart
                                                                    namlen
                                                                    &charBuf
                                                                    &decodedLen

                                                            let bit =
                                                                metadataBit (
                                                                    ReadOnlySpan<char>(
                                                                        charBuf,
                                                                        0,
                                                                        cLen
                                                                    )
                                                                )

                                                            if bit <> 0 then
                                                                metaMask <- metaMask ||| bit

                                                        if objType = 2u then
                                                            let cLen =
                                                                decodeUtf8Name
                                                                    attrBuf
                                                                    nameStart
                                                                    namlen
                                                                    &charBuf
                                                                    &decodedLen

                                                            let nameSpan =
                                                                ReadOnlySpan<char>(charBuf, 0, cLen)

                                                            if not (alwaysIgnored nameSpan) then
                                                                let fullPath =
                                                                    joinChildPath
                                                                        directory
                                                                        hasTrailingSlash
                                                                        nameSpan

                                                                items.Add
                                                                    {
                                                                        Path = fullPath
                                                                        Length = -1L
                                                                        IsDirectory = true
                                                                    }
                                                        elif objType = 1u && namlen >= 3 then
                                                            let dot =
                                                                attrBuf[nameStart + namlen - 3]

                                                            let c =
                                                                attrBuf[nameStart + namlen - 2]
                                                                ||| 0x20uy

                                                            let sByte =
                                                                attrBuf[nameStart + namlen - 1]
                                                                ||| 0x20uy

                                                            if
                                                                dot = 46uy
                                                                && c = 99uy
                                                                && sByte = 115uy
                                                            then
                                                                let cLen =
                                                                    decodeUtf8Name
                                                                        attrBuf
                                                                        nameStart
                                                                        namlen
                                                                        &charBuf
                                                                        &decodedLen

                                                                let nameSpan =
                                                                    ReadOnlySpan<char>(
                                                                        charBuf,
                                                                        0,
                                                                        cLen
                                                                    )

                                                                if
                                                                    includeGenerated
                                                                    || not (generatedName nameSpan)
                                                                then
                                                                    let fileLen =
                                                                        if
                                                                            (retFile &&& 0x00000200u)
                                                                            <> 0u
                                                                            && (retFile
                                                                                &&& 0x000001FFu)
                                                                                =
                                                                                0u
                                                                            && pos + 8 <= recEnd
                                                                        then
                                                                            let v =
                                                                                BinaryPrimitives.ReadInt64LittleEndian(
                                                                                    ReadOnlySpan<
                                                                                        byte
                                                                                     >(
                                                                                        attrBuf,
                                                                                        pos,
                                                                                        8
                                                                                    )
                                                                                )

                                                                            if v >= 0L then
                                                                                v
                                                                            else
                                                                                -1L
                                                                        else
                                                                            -1L

                                                                    let fullPath =
                                                                        joinChildPath
                                                                            directory
                                                                            hasTrailingSlash
                                                                            nameSpan

                                                                    items.Add
                                                                        {
                                                                            Path = fullPath
                                                                            Length = fileLen
                                                                            IsDirectory = false
                                                                        }

                                        offset <- recEnd

                                entryIdx <- entryIdx + 1
                finally
                    darwinCloseDirectory fd |> ignore
                    PoolArray.release &attrBuf
                    PoolArray.release &charBuf

                if fallback then
                    enumerateArrayReadDir includeGenerated directory
                else
                    struct (metaMask, items.ToArray())

    type internal Spellings(readDirectory: string -> seq<string>, foldRootCase: bool) =
        let resolved = Dictionary<string, string>(StringComparer.Ordinal)

        let listings =
            Dictionary<string, struct (bool * Dictionary<string, ResizeArray<string>>)>(
                StringComparer.Ordinal
            )

        let listing parent =
            match listings.TryGetValue parent with
            | true, value -> value
            | _ ->
                let names =
                    Dictionary<string, ResizeArray<string>>(StringComparer.OrdinalIgnoreCase)

                let mutable complete = true

                try
                    for entry in readDirectory parent do
                        let leaf = Path.GetFileName entry

                        match names.TryGetValue leaf with
                        | true, stored -> stored.Add leaf
                        | _ -> names[leaf] <- ResizeArray [ leaf ]
                with
                | :? IOException
                | :? UnauthorizedAccessException
                | :? ArgumentException -> complete <- false

                let value = struct (complete, names)
                listings[parent] <- value
                value

        let rec resolve (path: string) =
            match resolved.TryGetValue path with
            | true, value -> value
            | _ ->
                let value =
                    match Path.GetDirectoryName path with
                    | null -> if foldRootCase then path.ToUpperInvariant() else path
                    | parent ->
                        let leaf = Path.GetFileName path

                        if leaf.Length = 0 then
                            path
                        else
                            let parent = resolve parent
                            let requested = Path.Combine(parent, leaf)

                            let struct (complete, names) = listing parent

                            match names.TryGetValue leaf with
                            | true, stored ->
                                if
                                    stored
                                    |> Seq.exists (fun name ->
                                        StringComparer.Ordinal.Equals(name, leaf))
                                then
                                    requested
                                elif
                                    complete
                                    && stored.Count = 1
                                    && (Directory.Exists requested || File.Exists requested)
                                then
                                    Path.Combine(parent, stored[0])
                                else
                                    requested
                            | _ -> requested

                resolved[path] <- value
                value

        new() = Spellings(Directory.EnumerateFileSystemEntries, OperatingSystem.IsWindows())

        new(readDirectory) = Spellings(readDirectory, OperatingSystem.IsWindows())

        member _.Identity(path: string) =
            resolve (Path.TrimEndingDirectorySeparator(Path.GetFullPath path))

        member this.SameEntry(left: string, right: string) =
            StringComparer.Ordinal.Equals(left, right)
            || StringComparer.Ordinal.Equals(this.Identity left, this.Identity right)

    let internal pathIdentity (path: string) = Spellings().Identity path

    let private inputFileComparer =
        { new IComparer<InputFile> with
            member _.Compare(a, b) = String.CompareOrdinal(a.Path, b.Path)
        }

    let private inputFileWithLengthComparer =
        { new IComparer<struct (InputFile * int64)> with
            member _.Compare(struct (a, _), struct (b, _)) = String.CompareOrdinal(a.Path, b.Path)
        }

    let private filesCore
        (enumerateArray: string -> struct (int * DirEntry array))
        (treeWalkFastPath: bool)
        (roots: string array)
        configPath
        ignorePath
        includeGenerated
        jobs
        =
        boostThread ()
        let results = ResizeArray<InputFile>()

        let comparer =
            if OperatingSystem.IsWindows() then
                StringComparer.OrdinalIgnoreCase
            else
                StringComparer.Ordinal

        let specified = configPath |> Option.map Configuration.read

        let specifiedIgnore =
            ignorePath
            |> Option.map (fun path -> readIgnore Environment.CurrentDirectory path)

        let autoConfig = Option.isNone specified
        let autoIgnore = Option.isNone specifiedIgnore
        let context = Context(autoConfig, autoIgnore)

        let inline cached (cache: Dictionary<string, Lazy<'T>>) path create =
            let entry =
                lock cache (fun () ->
                    match cache.TryGetValue path with
                    | true, entry -> entry
                    | _ ->
                        let entry = Lazy<'T>(Func<'T>(create))
                        cache.Add(path, entry)
                        entry)

            entry.Value

        let walks =
            Dictionary<string, Lazy<Dictionary<string, Lazy<DirectoryFiles>>>>(
                StringComparer.Ordinal
            )

        let listingComparer =
            { new IEqualityComparer<string> with
                member _.GetHashCode directory = comparer.GetHashCode directory

                member _.Equals(left, right) =
                    if StringComparer.Ordinal.Equals(left, right) then
                        true
                    elif not (comparer.Equals(left, right)) then
                        false
                    else
                        match directoryIdentity left, directoryIdentity right with
                        | Some left, Some right -> left = right
                        | _ -> false
            }

        let entries =
            Dictionary<string, Lazy<struct (string * int * DirEntry array)>>(listingComparer)

        let withIgnore directory (state: DirectorySettings) =
            match specifiedIgnore with
            | Some ignore ->
                { state with
                    CsffIgnore = Some { ignore with Directory = directory }
                    GitIgnores = []
                }
            | None -> state

        let inheritChildState directory (parentState: DirectorySettings) (metaMask: int) =
            let config =
                if not autoConfig then
                    None
                elif (metaMask &&& 1) <> 0 then
                    Configuration.find directory |> Option.orElse parentState.Config
                else
                    parentState.Config

            let editor, uniformCs =
                if not autoConfig || Option.isSome config then
                    None, ValueNone
                elif (metaMask &&& 2) = 0 then
                    parentState.Editor, parentState.UniformCsSettings
                else
                    let root, sections = Configuration.readEditor directory
                    let inherited = if root then None else parentState.Editor

                    let ed =
                        if sections.Length = 0 then
                            inherited
                        else
                            Some
                                {
                                    Sections = sections
                                    Parent = inherited
                                }

                    ed, Configuration.tryUniformCsSettings ed directory

            let csffIgnore, gitIgnores =
                if not autoIgnore then
                    parentState.CsffIgnore, []
                else
                    let csff =
                        if (metaMask &&& 4) <> 0 then
                            let path = Path.Combine(directory, ".csffignore")

                            if File.Exists path then
                                Some(readIgnore directory path)
                            else
                                parentState.CsffIgnore
                        else
                            parentState.CsffIgnore

                    let inheritedGit =
                        if
                            (metaMask &&& 16) <> 0 && Path.Exists(Path.Combine(directory, ".git"))
                        then
                            []
                        else
                            parentState.GitIgnores

                    let git =
                        if (metaMask &&& 8) <> 0 then
                            let path = Path.Combine(directory, ".gitignore")

                            if File.Exists path then
                                readIgnore directory path :: inheritedGit
                            else
                                inheritedGit
                        else
                            inheritedGit

                    csff, git

            {
                Config = config
                Editor = editor
                UniformCsSettings = uniformCs
                CsffIgnore = csffIgnore
                GitIgnores = gitIgnores
            }

        let addAccepted
            (results: ResizeArray<InputFile>)
            (directory: string)
            (state: DirectorySettings)
            root
            (path: string)
            =
            if not (ignored state path false) then
                let settings =
                    match specified |> Option.orElse state.Config with
                    | Some config -> Some(Configuration.forFile (Some config) path)
                    | None ->
                        match state.UniformCsSettings with
                        | ValueSome uniform when
                            path.EndsWith(".cs", StringComparison.Ordinal)
                            && not (Glob.hasNewline path)
                            && Glob.isCanonicalChildPath directory path
                            ->
                            uniform
                        | _ -> Configuration.editorForFile state.Editor path

                match settings with
                | Some settings ->
                    results.Add
                        {
                            Path = path
                            Settings = settings
                            Root = root
                        }
                | None -> ()

        let addAcceptedWithLength
            (results: ResizeArray<struct (InputFile * int64)>)
            (directory: string)
            (state: DirectorySettings)
            root
            (path: string)
            (length: int64)
            =
            if not (ignored state path false) then
                let settings =
                    match specified |> Option.orElse state.Config with
                    | Some config -> Some(Configuration.forFile (Some config) path)
                    | None ->
                        match state.UniformCsSettings with
                        | ValueSome uniform when
                            path.EndsWith(".cs", StringComparison.Ordinal)
                            && not (Glob.hasNewline path)
                            && Glob.isCanonicalChildPath directory path
                            ->
                            uniform
                        | _ -> Configuration.editorForFile state.Editor path

                match settings with
                | Some settings ->
                    results.Add(
                        struct ({
                                    Path = path
                                    Settings = settings
                                    Root = root
                                },
                                length)
                    )
                | None -> ()

        let addAcceptedCanonical
            (results: ResizeArray<struct (InputFile * int64)>)
            (state: DirectorySettings)
            root
            (path: string)
            (length: int64)
            (segOffset: int)
            =
            let isCsFile = path.EndsWith(".cs", StringComparison.Ordinal)

            if not (ignoredCanonical state path segOffset isCsFile false) then
                let settings =
                    match specified |> Option.orElse state.Config with
                    | Some config -> Some(Configuration.forFile (Some config) path)
                    | None ->
                        match state.UniformCsSettings with
                        | ValueSome uniform when isCsFile -> uniform
                        | _ -> Configuration.editorForCanonicalFile state.Editor path segOffset

                match settings with
                | Some settings ->
                    results.Add(
                        struct ({
                                    Path = path
                                    Settings = settings
                                    Root = root
                                },
                                length)
                    )
                | None -> ()

        let add (results: ResizeArray<InputFile>) (state: DirectorySettings) root (path: string) =
            if csharpSource includeGenerated path then
                let dir = Path.GetDirectoryName path |> Path.TrimEndingDirectorySeparator
                addAccepted results dir state root path

        let mutable idleHelpers = max 0 (jobs - 1)

        let tryAcquireHelper () =
            let mutable acquired = false
            let mutable looping = true

            while looping do
                let current = Volatile.Read(&idleHelpers)

                if current <= 0 then
                    looping <- false
                elif Interlocked.CompareExchange(&idleHelpers, current - 1, current) = current then
                    acquired <- true
                    looping <- false

            acquired

        let runParallel count (body: int -> unit) =
            if count = 1 then
                body 0
            elif count > 1 then
                let errors = Array.zeroCreate<exn> count

                if jobs <= 1 then
                    for index = 0 to count - 1 do
                        try
                            body index
                        with error ->
                            errors[index] <- error
                else
                    let mutable next = -1

                    let work () =
                        let mutable index = Interlocked.Increment(&next)

                        while index < count do
                            try
                                body index
                            with error ->
                                errors[index] <- error

                            index <- Interlocked.Increment(&next)

                    let tasks = ResizeArray<Task>()

                    while tasks.Count < count - 1
                          && Volatile.Read(&next) < count - 1
                          && tryAcquireHelper () do
                        tasks.Add(
                            Task.Run(fun () ->
                                try
                                    work ()
                                finally
                                    Interlocked.Increment(&idleHelpers) |> ignore)
                        )

                    work ()

                    for index = 0 to tasks.Count - 1 do
                        tasks[index].GetAwaiter().GetResult()

                for index = 0 to errors.Length - 1 do
                    if not (isNull errors[index]) then
                        ExceptionDispatchInfo.Capture(errors[index]).Throw()

        let walkFastRoot root parentState ignoreDirectory =
            let rootDir = Path.GetFullPath root |> Path.TrimEndingDirectorySeparator
            let maxCores = Environment.ProcessorCount

            let workerCount =
                if jobs > 4 && maxCores >= 8 then
                    min jobs (maxCores - 3)
                else
                    max 1 (min jobs maxCores)

            if workerCount <= 1 then
                let files = ResizeArray<struct (InputFile * int64)>()
                let stack = Stack<struct (string * DirectorySettings * bool)>()
                stack.Push(struct (rootDir, parentState, true))

                while stack.Count > 0 do
                    let struct (directory, pState, isRoot) = stack.Pop()
                    let struct (metaMask, contents) = enumerateArray directory

                    let state =
                        if isRoot then
                            pState
                        elif metaMask >= 0 then
                            if metaMask = 0 then
                                pState
                            else
                                inheritChildState directory pState metaMask
                        else
                            context.Inherited directory |> withIgnore ignoreDirectory

                    for entry in contents do
                        let path = entry.Path

                        if entry.IsDirectory then
                            if
                                not (alwaysIgnored (Path.GetFileName(path.AsSpan())))
                                && not (ignored state path true)
                            then
                                stack.Push(struct (path, state, false))
                        else
                            addAcceptedWithLength files directory state 0 path entry.Length

                files.Sort(inputFileWithLengthComparer)
                let n = files.Count
                let outFiles = Array.zeroCreate<InputFile> n
                let mutable allLengthsKnown = n > 0

                for i = 0 to n - 1 do
                    let struct (f, len) = files[i]
                    outFiles[i] <- f

                    if len < 0L then
                        allLengthsKnown <- false

                let outLengths =
                    if allLengthsKnown then
                        let arr = Array.zeroCreate<int64> n

                        for i = 0 to n - 1 do
                            let struct (_, len) = files[i]
                            arr[i] <- len

                        arr
                    else
                        null

                {
                    Files = outFiles
                    Lengths = outLengths
                    Children = [||]
                }
            else
                let queue = ConcurrentQueue<struct (string * DirectorySettings * bool)>()
                let mutable activeDirs = 1
                let mutable firstError: exn = null

                let perWorker =
                    Array.init workerCount (fun _ -> ResizeArray<struct (InputFile * int64)>(1024))

                queue.Enqueue(struct (rootDir, parentState, true))

                let processOneDirectory
                    (localFiles: ResizeArray<struct (InputFile * int64)>)
                    (curDir: string)
                    (curParentState: DirectorySettings)
                    (curIsRoot: bool)
                    (keepOneLocal: bool)
                    =
                    let struct (metaMask, contents) = enumerateArray curDir

                    let state =
                        if curIsRoot then
                            curParentState
                        elif metaMask >= 0 then
                            if metaMask = 0 then
                                curParentState
                            else
                                inheritChildState curDir curParentState metaMask
                        else
                            context.Inherited curDir |> withIgnore ignoreDirectory

                    let dirCanonical =
                        not (Glob.hasNewline curDir) && Glob.isCanonicalNativePath curDir

                    let sep = Path.DirectorySeparatorChar
                    let mutable nextDir: string = null

                    let hasIgnoreRules =
                        (match state.CsffIgnore with
                         | Some ig -> ig.Rules.Length > 0
                         | None -> false)
                        || (state.GitIgnores |> List.exists (fun ig -> ig.Rules.Length > 0))

                    let uniformAllFilesSettings =
                        if not dirCanonical then
                            ValueNone
                        else
                            match specified |> Option.orElse state.Config with
                            | Some config ->
                                if config.Overrides.Length = 0 then
                                    ValueSome config.Settings
                                else
                                    ValueNone
                            | None ->
                                match state.UniformCsSettings with
                                | ValueSome(Some uniform) -> ValueSome uniform
                                | _ -> ValueNone

                    if not hasIgnoreRules && uniformAllFilesSettings.IsSome then
                        let fastSettings = uniformAllFilesSettings.Value

                        for entry in contents do
                            let path = entry.Path

                            if entry.IsDirectory then
                                if keepOneLocal && isNull nextDir then
                                    nextDir <- path
                                else
                                    Interlocked.Increment(&activeDirs) |> ignore
                                    queue.Enqueue(struct (path, state, false))
                            elif
                                path.EndsWith(".cs", StringComparison.Ordinal)
                                && not (Glob.hasNewline path)
                                && Glob.isCanonicalChildPath curDir path
                            then
                                localFiles.Add(
                                    struct ({
                                                Path = path
                                                Settings = fastSettings
                                                Root = 0
                                            },
                                            entry.Length)
                                )
                            else
                                addAcceptedWithLength localFiles curDir state 0 path entry.Length
                    else
                        for entry in contents do
                            let path = entry.Path
                            let isDirectory = entry.IsDirectory
                            let mutable handled = false

                            if
                                dirCanonical
                                && path.Length > curDir.Length + 1
                                && path[curDir.Length] = sep
                                && path.StartsWith(curDir, StringComparison.Ordinal)
                            then
                                let segOffset = curDir.Length + 1
                                let seg = path.AsSpan(segOffset)

                                if
                                    seg.IndexOfAny('/', '\\', '\n') < 0
                                    && not (seg.Length = 1 && seg[0] = '.')
                                    && not (seg.Length = 2 && seg[0] = '.' && seg[1] = '.')
                                then
                                    handled <- true

                                    if isDirectory then
                                        if
                                            not (alwaysIgnored seg)
                                            && not (
                                                ignoredCanonical state path segOffset false true
                                            )
                                        then
                                            if keepOneLocal && isNull nextDir then
                                                nextDir <- path
                                            else
                                                Interlocked.Increment(&activeDirs) |> ignore
                                                queue.Enqueue(struct (path, state, false))
                                    else
                                        addAcceptedCanonical
                                            localFiles
                                            state
                                            0
                                            path
                                            entry.Length
                                            segOffset

                            if not handled then
                                if isDirectory then
                                    if
                                        not (alwaysIgnored (Path.GetFileName(path.AsSpan())))
                                        && not (ignored state path true)
                                    then
                                        if keepOneLocal && isNull nextDir then
                                            nextDir <- path
                                        else
                                            Interlocked.Increment(&activeDirs) |> ignore
                                            queue.Enqueue(struct (path, state, false))
                                else
                                    addAcceptedWithLength
                                        localFiles
                                        curDir
                                        state
                                        0
                                        path
                                        entry.Length

                    if isNull nextDir then
                        Interlocked.Decrement(&activeDirs) |> ignore
                        struct (false, "", Unchecked.defaultof<DirectorySettings>)
                    else
                        struct (true, nextDir, state)

                let mutable rootItem =
                    Unchecked.defaultof<struct (string * DirectorySettings * bool)>

                if queue.TryDequeue(&rootItem) then
                    let struct (d, ps, ir) = rootItem

                    try
                        processOneDirectory perWorker[0] d ps ir false |> ignore
                    with ex ->
                        firstError <- ex
                        Interlocked.Decrement(&activeDirs) |> ignore

                let workerBody (workerIdx: int) =
                    boostThread ()
                    let localFiles = perWorker[workerIdx]
                    let mutable hasCurrent = false
                    let mutable curDir = ""
                    let mutable curParentState = Unchecked.defaultof<DirectorySettings>
                    let mutable curIsRoot = false
                    let mutable spins = 0

                    try
                        while Volatile.Read(&activeDirs) > 0 && isNull (Volatile.Read(&firstError)) do
                            if not hasCurrent then
                                let mutable item =
                                    Unchecked.defaultof<struct (string * DirectorySettings * bool)>

                                if queue.TryDequeue(&item) then
                                    let struct (d, ps, ir) = item
                                    curDir <- d
                                    curParentState <- ps
                                    curIsRoot <- ir
                                    hasCurrent <- true

                            if hasCurrent then
                                hasCurrent <- false
                                spins <- 0

                                let struct (hasNext, nextDir, nextState) =
                                    processOneDirectory
                                        localFiles
                                        curDir
                                        curParentState
                                        curIsRoot
                                        true

                                if hasNext then
                                    curDir <- nextDir
                                    curParentState <- nextState
                                    curIsRoot <- false
                                    hasCurrent <- true
                            else
                                spins <- spins + 1

                                if (spins &&& 63) = 0 then
                                    Thread.Yield() |> ignore
                                else
                                    Thread.SpinWait 16

                        if isNull (Volatile.Read(&firstError)) && localFiles.Count > 1 then
                            localFiles.Sort(inputFileWithLengthComparer)
                    with ex ->
                        Interlocked.CompareExchange(&firstError, ex, null) |> ignore

                if isNull firstError && Volatile.Read(&activeDirs) > 0 then
                    let threads = Array.zeroCreate<Thread>(workerCount - 1)

                    for w = 1 to workerCount - 1 do
                        let idx = w
                        let t = Thread(ThreadStart(fun () -> workerBody idx))
                        t.IsBackground <- true
                        t.Start()
                        threads[w - 1] <- t

                    workerBody 0

                    for i = 0 to threads.Length - 1 do
                        threads[i].Join()
                elif isNull firstError && perWorker[0].Count > 1 then
                    perWorker[0].Sort(inputFileWithLengthComparer)

                if not (isNull firstError) then
                    ExceptionDispatchInfo.Capture(firstError).Throw()

                let mutable total = 0
                let mutable nonEmptyRuns = 0

                for w = 0 to workerCount - 1 do
                    let c = perWorker[w].Count
                    total <- total + c

                    if c > 0 then
                        nonEmptyRuns <- nonEmptyRuns + 1

                let mergedPairs =
                    if total = 0 then
                        [||]
                    elif nonEmptyRuns = 1 then
                        let mutable single = [||]

                        for w = 0 to workerCount - 1 do
                            if perWorker[w].Count > 0 then
                                single <- perWorker[w].ToArray()

                        single
                    else
                        let mutable src = Array.zeroCreate<struct (InputFile * int64)> total
                        let mutable dst = Array.zeroCreate<struct (InputFile * int64)> total
                        let runStarts = Array.zeroCreate<int>(nonEmptyRuns + 1)
                        let mutable offset = 0
                        let mutable r = 0

                        for w = 0 to workerCount - 1 do
                            let list = perWorker[w]

                            if list.Count > 0 then
                                runStarts[r] <- offset
                                list.CopyTo(src, offset)
                                offset <- offset + list.Count
                                r <- r + 1

                        runStarts[nonEmptyRuns] <- total
                        let mutable runCount = nonEmptyRuns

                        while runCount > 1 do
                            let mutable nextRuns = 0
                            let mutable i = 0

                            while i < runCount do
                                if i + 1 < runCount then
                                    let s0 = runStarts[i]
                                    let e0 = runStarts[i + 1]
                                    let e1 = runStarts[i + 2]
                                    let mutable p0 = s0
                                    let mutable p1 = e0
                                    let mutable outIdx = s0

                                    while p0 < e0 && p1 < e1 do
                                        let a = src[p0]
                                        let b = src[p1]
                                        let struct (fa, _) = a
                                        let struct (fb, _) = b

                                        if String.CompareOrdinal(fa.Path, fb.Path) <= 0 then
                                            dst[outIdx] <- a
                                            p0 <- p0 + 1
                                        else
                                            dst[outIdx] <- b
                                            p1 <- p1 + 1

                                        outIdx <- outIdx + 1

                                    if p0 < e0 then
                                        Array.Copy(src, p0, dst, outIdx, e0 - p0)
                                    elif p1 < e1 then
                                        Array.Copy(src, p1, dst, outIdx, e1 - p1)

                                    runStarts[nextRuns] <- s0
                                    nextRuns <- nextRuns + 1
                                    i <- i + 2
                                else
                                    let s0 = runStarts[i]
                                    let e0 = runStarts[i + 1]
                                    Array.Copy(src, s0, dst, s0, e0 - s0)
                                    runStarts[nextRuns] <- s0
                                    nextRuns <- nextRuns + 1
                                    i <- i + 1

                            runStarts[nextRuns] <- total
                            runCount <- nextRuns
                            let tmp = src
                            src <- dst
                            dst <- tmp

                        src

                let combined = Array.zeroCreate<InputFile> mergedPairs.Length
                let mutable allLengthsKnown = mergedPairs.Length > 0

                for i = 0 to mergedPairs.Length - 1 do
                    let struct (f, len) = mergedPairs[i]
                    combined[i] <- f

                    if len < 0L then
                        allLengthsKnown <- false

                let combinedLengths =
                    if allLengthsKnown then
                        let arr = Array.zeroCreate<int64> mergedPairs.Length

                        for i = 0 to mergedPairs.Length - 1 do
                            let struct (_, len) = mergedPairs[i]
                            arr[i] <- len

                        arr
                    else
                        null

                {
                    Files = combined
                    Lengths = combinedLengths
                    Children = [||]
                }

        let rec walk cache directory parentState ignoreDirectory isRoot =
            let directory = Path.GetFullPath directory |> Path.TrimEndingDirectorySeparator

            cached cache directory (fun () ->
                let files = ResizeArray<InputFile>()
                let subdirectories = ResizeArray<string>()

                let struct (original, metaMask, contents) =
                    cached entries directory (fun () ->
                        let struct (mask, arr) = enumerateArray directory
                        struct (directory, mask, arr))

                let state =
                    if isRoot then
                        parentState
                    elif directory = original && metaMask >= 0 then
                        if metaMask = 0 then
                            parentState
                        else
                            inheritChildState directory parentState metaMask
                    else
                        context.Inherited directory |> withIgnore ignoreDirectory

                for entry in contents do
                    let path =
                        if directory = original then
                            entry.Path
                        else
                            directory + entry.Path.Substring(original.Length)

                    if entry.IsDirectory then
                        if
                            not (alwaysIgnored (Path.GetFileName(path.AsSpan())))
                            && not (ignored state path true)
                        then
                            subdirectories.Add path
                    else
                        addAccepted files directory state 0 path

                let children = Array.zeroCreate<DirectoryFiles> subdirectories.Count

                runParallel subdirectories.Count (fun index ->
                    let path = subdirectories[index]
                    children[index] <- walk cache path state ignoreDirectory false)

                {
                    Files = files.ToArray()
                    Lengths = null
                    Children = children
                })

        let discover index =
            let results = ResizeArray<InputFile>()
            let root = roots[index]

            if not (Directory.Exists root || File.Exists root) then
                raise (FileNotFoundException("No file or directory at " + root, root))

            let directory =
                if Directory.Exists root then
                    root
                else
                    parentDirectoryOf root

            let state = context.Inherited directory |> withIgnore directory

            let mutable parent = DirectoryInfo directory
            let mutable excluded = false
            let mutable insideRepository = true

            while not (isNull parent) && not excluded do
                let repository =
                    insideRepository && Path.Exists(Path.Combine(parent.FullName, ".git"))

                excluded <-
                    (insideRepository && not repository && alwaysIgnored (parent.Name.AsSpan()))
                    || ignored state parent.FullName true

                if
                    not excluded
                    && autoIgnore
                    && insideRepository
                    && not repository
                    && not (isNull parent.Parent)
                then
                    excluded <-
                        ignored
                            { state with
                                CsffIgnore = context.CsffIgnore parent.Parent.FullName
                            }
                            parent.FullName
                            true

                if repository then
                    insideRepository <- false

                parent <- parent.Parent

            if not excluded then
                if Directory.Exists root then
                    if treeWalkFastPath then
                        Some(walkFastRoot root state directory)
                    else
                        let anchor =
                            if autoIgnore then
                                ""
                            else
                                Path.GetFullPath directory |> Path.TrimEndingDirectorySeparator

                        let cache =
                            cached walks anchor (fun () ->
                                Dictionary<string, Lazy<DirectoryFiles>>(StringComparer.Ordinal))

                        Some(walk cache root state directory true)
                else
                    add results state index (Path.GetFullPath root)

                    Some
                        {
                            Files = results.ToArray()
                            Lengths = null
                            Children = [||]
                        }
            else
                None

        let byRoot = Array.zeroCreate<DirectoryFiles option> roots.Length

        runParallel roots.Length (fun index -> byRoot[index] <- discover index)

        let mutable discoveredLengths: int64 array = null

        let files =
            if treeWalkFastPath then
                match byRoot[0] with
                | Some node when node.Children.Length = 0 ->
                    discoveredLengths <- node.Lengths
                    node.Files
                | Some node ->
                    let rec collect (n: DirectoryFiles) =
                        results.AddRange n.Files

                        for child in n.Children do
                            collect child

                    collect node
                    results.ToArray()
                | None -> [||]
            else
                let seen =
                    if roots.Length <= 1 then
                        null
                    else
                        let spellings = Spellings()

                        let sameEntry =
                            { new IEqualityComparer<string> with
                                member _.GetHashCode path =
                                    StringComparer.OrdinalIgnoreCase.GetHashCode path

                                member _.Equals(left, right) = spellings.SameEntry(left, right)
                            }

                        HashSet<string>(sameEntry)

                let merged = HashSet<DirectoryFiles>(HashIdentity.Reference)

                let rec merge index (node: DirectoryFiles) =
                    if merged.Add node then
                        if isNull seen then
                            results.AddRange node.Files
                        else
                            for file in node.Files do
                                if seen.Add file.Path then
                                    results.Add { file with Root = index }

                        for child in node.Children do
                            merge index child

                for index = 0 to roots.Length - 1 do
                    match byRoot[index] with
                    | Some node -> merge index node
                    | None -> ()

                results.ToArray()

        if not treeWalkFastPath then
            Array.Sort(files, inputFileComparer)

        struct (files, discoveredLengths)

    let filesWithEnumeration
        (enumerate: string -> seq<struct (string * bool)>)
        (roots: string array)
        configPath
        ignorePath
        includeGenerated
        jobs
        =
        let enumerateArray directory =
            let contents =
                enumerate directory
                |> Seq.filter (fun struct (path, isDirectory) ->
                    isDirectory || csharpSource includeGenerated path)
                |> Seq.map (fun struct (path, isDirectory) ->
                    {
                        Path = path
                        Length = -1L
                        IsDirectory = isDirectory
                    })
                |> Seq.toArray

            struct (-1, contents)

        let struct (files, _) =
            filesCore enumerateArray false roots configPath ignorePath includeGenerated jobs

        files

    let filesWithLengths (roots: string array) configPath ignorePath includeGenerated jobs =
        filesCore
            (enumerateArrayFor includeGenerated)
            (roots.Length = 1)
            roots
            configPath
            ignorePath
            includeGenerated
            jobs

    let files (roots: string array) configPath ignorePath includeGenerated jobs =
        let struct (files, _) =
            filesWithLengths roots configPath ignorePath includeGenerated jobs

        files
