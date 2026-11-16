namespace Csff.Cli

open System
open System.Buffers
open System.Collections.Concurrent
open System.Collections.Generic
open System.IO
open System.Runtime.CompilerServices
open System.Runtime.ExceptionServices
open System.Runtime.InteropServices
open System.Security.Cryptography
open System.Text
open System.Threading
open System.Threading.Tasks
open Csff.Lexer
open Csff.Parser
open Csff.Printer
open Csff.Conformance

[<Struct>]
type internal FileResult =
    {
        Key: CacheKey
        Cacheable: bool
        Changed: bool
        Cached: bool
        Skipped: bool
        Error: string
        Unverified: string
        Notice: string
    }

[<Sealed>]
type internal Windows1252() =
    inherit Encoding()

    static let upper = "€\u0081‚ƒ„…†‡ˆ‰Š‹Œ\u008DŽ\u008F\u0090‘’“”•–—˜™š›œ\u009DžŸ"

    override _.GetByteCount(_: char array, _: int, count: int) = count
    override _.GetCharCount(_: byte array, _: int, count: int) = count
    override _.GetMaxByteCount(charCount: int) = charCount
    override _.GetMaxCharCount(byteCount: int) = byteCount

    override _.GetChars
        (bytes: byte array, byteIndex: int, byteCount: int, chars: char array, charIndex: int)
        =
        for i = 0 to byteCount - 1 do
            let value = bytes[byteIndex + i]

            chars[charIndex + i] <-
                if value >= 0x80uy && value < 0xA0uy then
                    upper[int value - 0x80]
                else
                    char value

        byteCount

    override _.GetBytes
        (chars: char array, charIndex: int, charCount: int, bytes: byte array, byteIndex: int)
        =
        for i = 0 to charCount - 1 do
            let value = chars[charIndex + i]

            bytes[byteIndex + i] <-
                if value < '\u0080' || (value >= ' ' && value <= 'ÿ') then
                    byte value
                else
                    let index = upper.IndexOf value

                    if index < 0 then
                        raise (EncoderFallbackException "The text has no Windows-1252 byte.")

                    byte (0x80 + index)

        charCount

module internal SourceEncoding =
    let private utf8 = UTF8Encoding(false, true)
    let private utf16le = UnicodeEncoding(false, true, true)
    let private utf16be = UnicodeEncoding(true, true, true)
    let private utf32le = UTF32Encoding(false, true, true)
    let private utf32be = UTF32Encoding(true, true, true)
    let private windows1252 = Windows1252() :> Encoding

    let private encoding (bytes: ReadOnlySpan<byte>) =
        if
            bytes.Length >= 4
            && bytes[0] = 0xffuy
            && bytes[1] = 0xfeuy
            && bytes[2] = 0uy
            && bytes[3] = 0uy
        then
            struct (utf32le :> Encoding, 4)
        elif
            bytes.Length >= 4
            && bytes[0] = 0uy
            && bytes[1] = 0uy
            && bytes[2] = 0xfeuy
            && bytes[3] = 0xffuy
        then
            struct (utf32be :> Encoding, 4)
        elif bytes.Length >= 3 && bytes[0] = 0xefuy && bytes[1] = 0xbbuy && bytes[2] = 0xbfuy then
            struct (utf8 :> Encoding, 3)
        elif bytes.Length >= 2 && bytes[0] = 0xffuy && bytes[1] = 0xfeuy then
            struct (utf16le :> Encoding, 2)
        elif bytes.Length >= 2 && bytes[0] = 0xfeuy && bytes[1] = 0xffuy then
            struct (utf16be :> Encoding, 2)
        else
            struct (utf8 :> Encoding, 0)

    let isUtf8 (candidate: Encoding) = obj.ReferenceEquals(candidate, utf8)

    let private asciiDecodeAction =
        SpanAction<char, struct (byte array * int)>(fun dst state ->
            let struct (src, offset) = state
            let mutable written = 0

            Ascii.ToUtf16(ReadOnlySpan<byte>(src, offset, dst.Length), dst, &written)
            |> ignore)

    let decode (bytes: byte array) length =
        let struct (detected, preamble) = encoding (ReadOnlySpan<byte>(bytes, 0, length))
        let count = length - preamble

        if count = 0 then
            struct (detected, preamble, "")
        elif
            obj.ReferenceEquals(detected, utf8)
            && Ascii.IsValid(ReadOnlySpan<byte>(bytes, preamble, count))
        then
            struct (detected,
                    preamble,
                    String.Create(count, struct (bytes, preamble), asciiDecodeAction))
        else
            try
                struct (detected, preamble, detected.GetString(bytes, preamble, count))
            with :? DecoderFallbackException when preamble = 0 ->
                struct (windows1252, 0, windows1252.GetString(bytes, 0, length))

    let decodeBounded (bytes: byte array) length maxChars prefixWindow =
        if length <= maxChars then
            let struct (enc, pre, s) = decode bytes length
            struct (enc, pre, s, false)
        else
            let struct (detected, preamble) = encoding (ReadOnlySpan<byte>(bytes, 0, length))

            let struct (actual, actualPreamble, charCount) =
                try
                    struct (detected,
                            preamble,
                            detected.GetCharCount(bytes, preamble, length - preamble))
                with :? DecoderFallbackException when preamble = 0 ->
                    struct (windows1252, 0, length)

            if charCount <= maxChars then
                struct (actual,
                        actualPreamble,
                        actual.GetString(bytes, actualPreamble, length - actualPreamble),
                        false)
            elif obj.ReferenceEquals(actual, windows1252) then
                struct (actual, 0, windows1252.GetString(bytes, 0, min length prefixWindow), true)
            else
                let prefixChars = ArrayPool<char>.Shared.Rent prefixWindow

                try
                    let decoder = actual.GetDecoder()
                    let mutable bytesUsed = 0
                    let mutable charsUsed = 0
                    let mutable completed = false

                    decoder.Convert(
                        ReadOnlySpan<byte>(bytes, actualPreamble, length - actualPreamble),
                        Span<char>(prefixChars, 0, prefixWindow),
                        true,
                        &bytesUsed,
                        &charsUsed,
                        &completed
                    )

                    struct (actual, actualPreamble, String(prefixChars, 0, charsUsed), true)
                finally
                    ArrayPool<char>.Shared.Return prefixChars

    let decodePrefix (bytes: byte array) length prefixWindow =
        let struct (detected, preamble) = encoding (ReadOnlySpan<byte>(bytes, 0, length))
        let avail = length - preamble
        let prefixBytes = min avail (prefixWindow * 4)
        let prefixChars = ArrayPool<char>.Shared.Rent prefixWindow

        try
            try
                let decoder = detected.GetDecoder()
                let mutable bytesUsed = 0
                let mutable charsUsed = 0
                let mutable completed = false

                decoder.Convert(
                    ReadOnlySpan<byte>(bytes, preamble, prefixBytes),
                    Span<char>(prefixChars, 0, prefixWindow),
                    (prefixBytes = avail),
                    &bytesUsed,
                    &charsUsed,
                    &completed
                )

                struct (detected, preamble, String(prefixChars, 0, charsUsed))
            with :? DecoderFallbackException when preamble = 0 ->
                struct (windows1252, 0, windows1252.GetString(bytes, 0, min length prefixWindow))
        finally
            ArrayPool<char>.Shared.Return prefixChars

    let read path =
        let bytes = File.ReadAllBytes path
        let struct (_, _, source) = decode bytes bytes.Length
        source

module internal LinkCount =
    [<Struct; StructLayout(LayoutKind.Sequential)>]
    type DarwinStat =
        {
            Device: int32
            Mode: uint16
            Links: uint16
            Inode: uint64
            User: uint32
            Group: uint32
            ResidentDevice: int32
            AccessedSeconds: int64
            AccessedNanoseconds: int64
            ModifiedSeconds: int64
            ModifiedNanoseconds: int64
            ChangedSeconds: int64
            ChangedNanoseconds: int64
            BornSeconds: int64
            BornNanoseconds: int64
            Size: int64
            Blocks: int64
            BlockSize: int32
            Flags: uint32
            Generation: uint32
            LongSpare: int32
            QuadSpare0: int64
            QuadSpare1: int64
        }

    [<Struct; StructLayout(LayoutKind.Sequential)>]
    type WindowsByHandleFileInformation =
        {
            FileAttributes: uint32
            CreationTimeLow: uint32
            CreationTimeHigh: uint32
            LastAccessTimeLow: uint32
            LastAccessTimeHigh: uint32
            LastWriteTimeLow: uint32
            LastWriteTimeHigh: uint32
            VolumeSerialNumber: uint32
            FileSizeHigh: uint32
            FileSizeLow: uint32
            NumberOfLinks: uint32
            FileIndexHigh: uint32
            FileIndexLow: uint32
        }

    let private formatMask = 0xf000us
    let private regular = 0x8000us
    let private directory = 0x4000us

    let private windowsFileAttributeDirectory = 0x10u
    let private windowsFileAttributeDevice = 0x40u
    let private windowsFileFlagBackupSemantics = 0x02000000u

    [<DllImport("libc", EntryPoint = "stat", ExactSpelling = true)>]
    extern int private stat64BitInode(string path, DarwinStat& buffer)

    [<DllImport("libc", EntryPoint = "stat$INODE64", ExactSpelling = true)>]
    extern int private statInode64(string path, DarwinStat& buffer)

    [<DllImport("libc", EntryPoint = "fstat", ExactSpelling = true)>]
    extern int private fstat64BitInode(int fd, DarwinStat& buffer)

    [<DllImport("libc", EntryPoint = "fstat$INODE64", ExactSpelling = true)>]
    extern int private fstatInode64(int fd, DarwinStat& buffer)

    [<DllImport("libc", EntryPoint = "open", ExactSpelling = true)>]
    extern int openFile(string path, int flags)

    [<DllImport("libc", EntryPoint = "pread", ExactSpelling = true, SetLastError = true)>]
    extern nativeint preadBytes(int fd, byte& buf, unativeint count, int64 offset)

    [<DllImport("libc", EntryPoint = "pwrite", ExactSpelling = true, SetLastError = true)>]
    extern nativeint pwriteBytes(int fd, byte& buf, unativeint count, int64 offset)

    [<DllImport("libc", EntryPoint = "ftruncate", ExactSpelling = true)>]
    extern int ftruncateFd(int fd, int64 length)

    [<DllImport("libc", EntryPoint = "close", ExactSpelling = true)>]
    extern int closeFd(int fd)

    [<DllImport("libc", EntryPoint = "pthread_set_qos_class_self_np", ExactSpelling = true)>]
    extern int private setQosClassSelf(uint32 qosClass, int relativePriority)

    [<Struct; StructLayout(LayoutKind.Sequential)>]
    type WindowsOverlapped =
        {
            mutable Internal: nativeint
            mutable InternalHigh: nativeint
            mutable Offset: uint32
            mutable OffsetHigh: uint32
            mutable EventHandle: nativeint
        }

    [<DllImport("kernel32.dll",
                EntryPoint = "CreateFileW",
                CharSet = CharSet.Unicode,
                ExactSpelling = true)>]
    extern nativeint openWindowsHandle(
        string path,
        uint32 access,
        uint32 share,
        nativeint security,
        uint32 disposition,
        uint32 flags,
        nativeint template
    )

    [<DllImport("kernel32.dll", EntryPoint = "CloseHandle", ExactSpelling = true)>]
    extern int closeWindowsHandle(nativeint handle)

    [<DllImport("kernel32.dll", EntryPoint = "GetFileInformationByHandle", ExactSpelling = true)>]
    extern int getWindowsFileInfo(nativeint handle, WindowsByHandleFileInformation& information)

    [<DllImport("kernel32.dll", EntryPoint = "ReadFile", ExactSpelling = true)>]
    extern int readWindowsSequential(
        nativeint handle,
        byte& buffer,
        uint32 count,
        uint32& bytesRead,
        nativeint overlapped
    )

    [<DllImport("kernel32.dll", EntryPoint = "WriteFile", ExactSpelling = true)>]
    extern int writeWindowsFile(
        nativeint handle,
        byte& buffer,
        uint32 count,
        uint32& bytesWritten,
        WindowsOverlapped& overlapped
    )

    [<DllImport("kernel32.dll", EntryPoint = "SetFileInformationByHandle", ExactSpelling = true)>]
    extern int setWindowsEndOfFile(
        nativeint handle,
        int informationClass,
        int64& endOfFile,
        uint32 size
    )

    let private arm64 = RuntimeInformation.ProcessArchitecture = Architecture.Arm64

    let mutable private available =
        OperatingSystem.IsMacOS()
        && (arm64 || RuntimeInformation.ProcessArchitecture = Architecture.X64)

    let mutable private windowsAvailable = OperatingSystem.IsWindows()

    let isAvailable () = available
    let isWindowsAvailable () = windowsAvailable

    let boostThread () =
        if available then
            try
                setQosClassSelf (0x21u, 0) |> ignore
            with
            | :? EntryPointNotFoundException
            | :? DllNotFoundException -> ()
        elif windowsAvailable then
            try
                Thread.CurrentThread.Priority <- ThreadPriority.AboveNormal
            with _ ->
                ()

    let private windowsLongPath (path: string) =
        if
            path.Length < 248
            || path.StartsWith(@"\\?\", StringComparison.Ordinal)
            || path.StartsWith(@"\\.\", StringComparison.Ordinal)
        then
            path
        else
            try
                let full = Path.GetFullPath path

                if full.StartsWith(@"\\", StringComparison.Ordinal) then
                    @"\\?\UNC\" + full.Substring 2
                elif full.Length >= 3 && full[1] = ':' && full[2] = '\\' then
                    @"\\?\" + full
                else
                    path
            with _ ->
                path

    let measure (path: string) =
        if available then
            let mutable buffer = Unchecked.defaultof<DarwinStat>

            let code =
                try
                    if arm64 then
                        stat64BitInode (path, &buffer)
                    else
                        statInode64 (path, &buffer)
                with
                | :? EntryPointNotFoundException
                | :? DllNotFoundException ->
                    available <- false
                    -1

            if code < 0 && not available then
                struct (false, 0L, 0)
            elif code <> 0 then
                struct (true, 0L, 0)
            else
                let format = buffer.Mode &&& formatMask

                struct (true,
                        (if format = directory then 0L else buffer.Size),
                        (if format = regular then int buffer.Links else 0))
        elif windowsAvailable then
            let mutable info = Unchecked.defaultof<WindowsByHandleFileInformation>

            let code =
                try
                    let handle =
                        openWindowsHandle (
                            windowsLongPath path,
                            0u,
                            7u,
                            0n,
                            3u,
                            windowsFileFlagBackupSemantics,
                            0n
                        )

                    if handle <> -1n && handle <> 0n then
                        try
                            if getWindowsFileInfo (handle, &info) <> 0 then 0 else 1
                        finally
                            closeWindowsHandle handle |> ignore
                    else
                        1
                with
                | :? EntryPointNotFoundException
                | :? DllNotFoundException ->
                    windowsAvailable <- false
                    -1

            if code < 0 then
                struct (false, 0L, 0)
            elif code <> 0 then
                struct (true, 0L, 0)
            else
                let isDir = (info.FileAttributes &&& windowsFileAttributeDirectory) <> 0u

                let isDevice = (info.FileAttributes &&& windowsFileAttributeDevice) <> 0u

                let size =
                    if isDir then
                        0L
                    else
                        (int64 info.FileSizeHigh <<< 32) ||| int64 info.FileSizeLow

                let links =
                    if not isDir && not isDevice then
                        if info.NumberOfLinks > uint32 Int32.MaxValue then
                            Int32.MaxValue
                        else
                            int info.NumberOfLinks
                    else
                        0

                struct (true, size, links)
        else
            struct (false, 0L, 0)

    let count (path: string) =
        let struct (read, _, links) = measure path
        if read then links else 0

    let openWindowsReadRaw (path: string) =
        if windowsAvailable then
            openWindowsHandle (windowsLongPath path, 0x80000000u, 1u, 0n, 3u, 0x08000080u, 0n)
        else
            -1n

    let openWindowsReadWriteRaw (path: string) =
        if windowsAvailable then
            openWindowsHandle (windowsLongPath path, 0xC0000000u, 0u, 0n, 3u, 0x80u, 0n)
        else
            -1n

    let readRawFdLinks (fd: int) =
        if not available || fd < 0 then
            0
        else
            let mutable buffer = Unchecked.defaultof<DarwinStat>

            let code =
                try
                    if arm64 then
                        fstat64BitInode (fd, &buffer)
                    else
                        fstatInode64 (fd, &buffer)
                with
                | :? EntryPointNotFoundException
                | :? DllNotFoundException ->
                    available <- false
                    -1

            if code = 0 && (buffer.Mode &&& formatMask) = regular then
                int buffer.Links
            else
                0

    let readRawHandleLinks (handle: nativeint) =
        if not windowsAvailable || handle = -1n || handle = 0n then
            0
        else
            let mutable info = Unchecked.defaultof<WindowsByHandleFileInformation>

            if getWindowsFileInfo (handle, &info) <> 0 then
                let isDir = (info.FileAttributes &&& windowsFileAttributeDirectory) <> 0u
                let isDevice = (info.FileAttributes &&& windowsFileAttributeDevice) <> 0u

                if not isDir && not isDevice then
                    if info.NumberOfLinks > uint32 Int32.MaxValue then
                        Int32.MaxValue
                    else
                        int info.NumberOfLinks
                else
                    0
            else
                0

    let inline private readUpToLoop
        (readChunk: byte array -> int -> int -> int)
        (buffer: byte array)
        (maxBytes: int)
        =
        let mutable total = 0
        let mutable reachedEof = false
        let mutable failed = false

        while total < maxBytes && not reachedEof && not failed do
            let n = readChunk buffer total (maxBytes - total)

            if n > 0 then
                total <- total + n
            elif n = 0 then
                reachedEof <- true
            elif n <> -2 then
                failed <- true

        if failed then -1 else total

    let readUpToWith
        (readChunk: byte array -> int -> int -> int)
        (buffer: byte array)
        (maxBytes: int)
        =
        readUpToLoop readChunk buffer maxBytes

    let preadAll (fd: int) (buffer: byte array) (maxBytes: int) =
        readUpToLoop
            (fun dst offset remaining ->
                let n = preadBytes (fd, &dst[offset], unativeint remaining, int64 offset)

                if n >= 0n then int n
                elif Marshal.GetLastPInvokeError() = 4 then -2
                else -1)
            buffer
            maxBytes

    let readWindowsAll (handle: nativeint) (buffer: byte array) (maxBytes: int) =
        readUpToLoop
            (fun dst offset remaining ->
                let mutable bytesRead = 0u

                if
                    readWindowsSequential (handle, &dst[offset], uint32 remaining, &bytesRead, 0n)
                    <> 0
                then
                    int bytesRead
                else
                    -1)
            buffer
            maxBytes

    let readHandleUpTo
        (handle: Microsoft.Win32.SafeHandles.SafeFileHandle)
        (buffer: byte array)
        (maxBytes: int)
        =
        readUpToLoop
            (fun dst offset remaining ->
                RandomAccess.Read(handle, dst.AsSpan(offset, remaining), int64 offset))
            buffer
            maxBytes

[<AllowNullLiteral>]
type internal FileAccessGate(roots: string array) =
    let selective = roots.Length = 1

    let sync = obj ()
    let stripes = Array.init 256 (fun _ -> obj ())

    let mutable activeReaders = 0
    let mutable activeWriters = 0
    let mutable gatedReads = 0
    let mutable gatedWrites = 0
    let mutable waitedReads = 0
    let mutable waitedWrites = 0
    let mutable ungatedReads = 0
    let mutable ungatedWrites = 0

    static member val Instrumented =
        not (String.IsNullOrEmpty(Environment.GetEnvironmentVariable "CSFF_GATE_STATISTICS"))

    member _.Selective = selective

    member _.EnterRead() =
        Monitor.Enter sync

        try
            gatedReads <- gatedReads + 1

            if activeWriters > 0 then
                waitedReads <- waitedReads + 1

                while activeWriters > 0 do
                    Monitor.Wait sync |> ignore

            activeReaders <- activeReaders + 1
        finally
            Monitor.Exit sync

    member _.ExitRead() =
        Monitor.Enter sync

        try
            activeReaders <- activeReaders - 1

            if activeReaders = 0 then
                Monitor.PulseAll sync
        finally
            Monitor.Exit sync

    member _.EnterWrite(stripe: int) =
        let stripeLock = stripes[stripe &&& 255]
        Monitor.Enter stripeLock
        let mutable entered = false

        try
            Monitor.Enter sync

            try
                gatedWrites <- gatedWrites + 1

                if activeReaders > 0 then
                    waitedWrites <- waitedWrites + 1

                    while activeReaders > 0 do
                        Monitor.Wait sync |> ignore

                activeWriters <- activeWriters + 1
                entered <- true
            finally
                Monitor.Exit sync
        finally
            if not entered then
                Monitor.Exit stripeLock

    member _.ExitWrite(stripe: int) =
        Monitor.Enter sync

        try
            activeWriters <- activeWriters - 1

            if activeWriters = 0 then
                Monitor.PulseAll sync
        finally
            Monitor.Exit sync

        Monitor.Exit stripes[stripe &&& 255]

    member _.Participates(links: int) =
        if not selective || links <> 1 then
            true
        else
            if FileAccessGate.Instrumented then
                Interlocked.Increment(&ungatedReads) |> ignore

            false

    member _.NoteUngatedWrite() =
        if FileAccessGate.Instrumented then
            Interlocked.Increment(&ungatedWrites) |> ignore

    member _.Statistics =
        if not FileAccessGate.Instrumented then
            null
        else
            Monitor.Enter sync

            try
                String.Format(
                    "csff: gate: reads {0} ({1} gated, {2} waited for a writer), writes {3} ({4} gated, {5} waited for a reader)",
                    gatedReads + ungatedReads,
                    gatedReads,
                    waitedReads,
                    gatedWrites + ungatedWrites,
                    gatedWrites,
                    waitedWrites
                )
            finally
                Monitor.Exit sync

module internal GeneratedPrefix =
    let window = 64 * 1024

    let lookahead = 8

module internal ReadBack =
    let limit = 1024 * 1024

[<Sealed; AllowNullLiteral>]
type internal CommitSlot(homeShard: CommitShard, buffers: ArrayPool<byte>) =
    let mutable snapshot: byte array = Array.Empty<byte>()
    let mutable formatted: byte array = Array.Empty<byte>()

    static let rentSlotBuffer (pool: ArrayPool<byte>) (target: int) =
        if obj.ReferenceEquals(pool, ArrayPool<byte>.Shared) then
            if target > PoolArray.maxPooledLength then
                GC.AllocateUninitializedArray<byte> target
            elif target >= 16384 then
                SharedBuckets<byte>.Rent target
            else
                pool.Rent target
        else
            pool.Rent target

    static let returnSlotBuffer (pool: ArrayPool<byte>) (buffer: byte array) =
        if not (isNull buffer) && buffer.Length > 0 then
            if obj.ReferenceEquals(pool, ArrayPool<byte>.Shared) then
                if buffer.Length < 16384 then
                    pool.Return buffer
                elif buffer.Length <= PoolArray.maxPooledLength then
                    SharedBuckets<byte>.Return buffer
            else
                pool.Return buffer

    static member val MaxBytes = 64 * 1024

    member _.HomeShard = homeShard

    member _.EnsureBuffers() =
        if isNull snapshot then
            snapshot <- Array.Empty<byte>()

    member _.EnsureSnapshotCapacity(snapLen: int) =
        if isNull snapshot then
            snapshot <- rentSlotBuffer buffers (max 16384 snapLen)
        elif snapshot.Length < snapLen then
            let replacement = rentSlotBuffer buffers (max 16384 snapLen)
            returnSlotBuffer buffers snapshot
            snapshot <- replacement

    member this.EnsureCapacity(snapLen: int, fmtLen: int) =
        this.EnsureSnapshotCapacity snapLen

        if isNull formatted then
            formatted <- rentSlotBuffer buffers (max 16384 fmtLen)
        elif formatted.Length < fmtLen then
            let replacement = rentSlotBuffer buffers (max 16384 fmtLen)
            returnSlotBuffer buffers formatted
            formatted <- replacement

    member _.ReleaseOversized() =
        if not (isNull snapshot) && snapshot.Length > CommitSlot.MaxBytes then
            returnSlotBuffer buffers snapshot
            snapshot <- Array.Empty<byte>()

        if not (isNull formatted) && formatted.Length > CommitSlot.MaxBytes then
            returnSlotBuffer buffers formatted
            formatted <- Array.Empty<byte>()

    member _.IsOversized =
        (not (isNull snapshot) && snapshot.Length > CommitSlot.MaxBytes)
        || (not (isNull formatted) && formatted.Length > CommitSlot.MaxBytes)

    member _.Snapshot
        with get () = snapshot
        and set v = snapshot <- v

    member _.Formatted
        with get () = formatted
        and set v = formatted <- v

    member val Index = 0 with get, set
    member val SnapshotLength = 0 with get, set
    member val FormattedLength = 0 with get, set
    member val Stripe = 0 with get, set
    member val Gated = false with get, set
    member val Key = Unchecked.defaultof<CacheKey> with get, set
    member val ReadError: exn = null with get, set

    member _.Dispose() =
        if not (isNull snapshot) && snapshot.Length > 0 then
            returnSlotBuffer buffers snapshot
            snapshot <- [||]

        if not (isNull formatted) && formatted.Length > 0 then
            returnSlotBuffer buffers formatted
            formatted <- [||]

and [<Sealed; AllowNullLiteral>] internal CommitShard
    (slotCount: int, buffers: ArrayPool<byte>, sharedWaitObj: obj, sharedWaiting: int ref) as this =
    let slots = Array.zeroCreate<CommitSlot> slotCount
    let free = ConcurrentStack<CommitSlot>()
    let readyMedium = ConcurrentQueue<CommitSlot>()
    let readyLarge = ConcurrentQueue<CommitSlot>()
    let ready = ConcurrentQueue<CommitSlot>()
    let pendingLarge = ConcurrentQueue<CommitSlot>()
    let pending = ConcurrentQueue<CommitSlot>()
    let freeWaitObj = obj ()
    let pendingWaitObj = obj ()
    let mutable readyMediumCount = 0
    let mutable readyLargeCount = 0
    let mutable readyCount = 0
    let mutable pendingCount = 0
    let mutable waitingFree = 0
    let mutable waitingPending = 0
    let mutable completed = false

    do
        try
            for i = 0 to slotCount - 1 do
                let slot = CommitSlot(this, buffers)
                slots[i] <- slot
                free.Push slot
        with _ ->
            this.Dispose()
            reraise ()

    member _.ReadyMediumCount = Volatile.Read(&readyMediumCount)
    member _.ReadyLargeCount = Volatile.Read(&readyLargeCount)
    member _.ReadyCount = Volatile.Read(&readyCount)
    member _.PendingCount = Volatile.Read(&pendingCount)

    member _.TryPopFree(slot: CommitSlot byref) =
        if free.TryPop(&slot) then
            slot.EnsureBuffers()
            true
        else
            false

    member this.PopOrCreateFree() =
        let mutable slot = Unchecked.defaultof<CommitSlot>

        if free.TryPop(&slot) then
            slot.EnsureBuffers()
            slot
        else
            CommitSlot(this, buffers)

    member _.PushFree(slot: CommitSlot) =
        slot.ReadError <- null
        slot.ReleaseOversized()
        free.Push slot

        if Volatile.Read(&waitingFree) > 0 then
            lock freeWaitObj (fun () ->
                if Volatile.Read(&waitingFree) > 0 then
                    Monitor.PulseAll freeWaitObj)

    member _.TryDequeueReadyMedium(slot: CommitSlot byref) =
        if readyMedium.TryDequeue(&slot) then
            Interlocked.Decrement(&readyMediumCount) |> ignore

            if Volatile.Read(&waitingFree) > 0 then
                lock freeWaitObj (fun () ->
                    if Volatile.Read(&waitingFree) > 0 then
                        Monitor.PulseAll freeWaitObj)

            true
        else
            false

    member _.EnqueueReadyMedium(slot: CommitSlot) =
        Interlocked.Increment(&readyMediumCount) |> ignore
        readyMedium.Enqueue slot

    member _.TryDequeueReadyLarge(slot: CommitSlot byref) =
        if readyLarge.TryDequeue(&slot) then
            Interlocked.Decrement(&readyLargeCount) |> ignore

            if Volatile.Read(&waitingFree) > 0 then
                lock freeWaitObj (fun () ->
                    if Volatile.Read(&waitingFree) > 0 then
                        Monitor.PulseAll freeWaitObj)

            true
        else
            false

    member _.EnqueueReadyLarge(slot: CommitSlot) =
        Interlocked.Increment(&readyLargeCount) |> ignore
        readyLarge.Enqueue slot

    member _.TryDequeueReady(slot: CommitSlot byref) =
        if ready.TryDequeue(&slot) then
            if Interlocked.Decrement(&readyCount) < 80 && Volatile.Read(&waitingFree) > 0 then
                lock freeWaitObj (fun () ->
                    if Volatile.Read(&waitingFree) > 0 then
                        Monitor.PulseAll freeWaitObj)

            true
        else
            false

    member _.EnqueueReady(slot: CommitSlot) =
        Interlocked.Increment(&readyCount) |> ignore
        ready.Enqueue slot

    member _.IsReadyEmpty = ready.IsEmpty && readyLarge.IsEmpty && readyMedium.IsEmpty

    member _.TryDequeuePending(slot: CommitSlot byref) =
        if pendingLarge.TryDequeue(&slot) || pending.TryDequeue(&slot) then
            Interlocked.Decrement(&pendingCount) |> ignore
            true
        else
            false

    member _.IsEmpty = pendingLarge.IsEmpty && pending.IsEmpty

    member _.EnqueuePending(slot: CommitSlot) =
        if slot.IsOversized then
            pendingLarge.Enqueue slot
        else
            pending.Enqueue slot

        Interlocked.Increment(&pendingCount) |> ignore

        if Volatile.Read(&waitingPending) > 0 then
            lock pendingWaitObj (fun () ->
                if Volatile.Read(&waitingPending) > 0 then
                    Monitor.Pulse pendingWaitObj)

        if Volatile.Read(&sharedWaiting.contents) > 0 then
            lock sharedWaitObj (fun () ->
                if Volatile.Read(&sharedWaiting.contents) > 0 then
                    Monitor.PulseAll sharedWaitObj)

    member _.WaitForFree() =
        if
            (Volatile.Read(&readyCount) >= 112
             || Volatile.Read(&readyLargeCount) >= 20
             || Volatile.Read(&readyMediumCount) >= 6
             || free.IsEmpty)
            && not (Volatile.Read(&completed))
        then
            lock freeWaitObj (fun () ->
                Interlocked.Increment(&waitingFree) |> ignore

                try
                    if
                        (Volatile.Read(&readyCount) >= 112
                         || Volatile.Read(&readyLargeCount) >= 20
                         || Volatile.Read(&readyMediumCount) >= 6
                         || free.IsEmpty)
                        && not (Volatile.Read(&completed))
                    then
                        Monitor.Wait(freeWaitObj, 1) |> ignore
                finally
                    Interlocked.Decrement(&waitingFree) |> ignore)

    member this.WaitForWork(_allEmpty: unit -> bool) =
        if this.IsEmpty && not (Volatile.Read(&completed)) then
            lock pendingWaitObj (fun () ->
                Interlocked.Increment(&waitingPending) |> ignore

                try
                    if this.IsEmpty && not (Volatile.Read(&completed)) then
                        Monitor.Wait(pendingWaitObj, 1) |> ignore
                finally
                    Interlocked.Decrement(&waitingPending) |> ignore)

    member _.Wake() =
        Volatile.Write(&completed, true)
        lock pendingWaitObj (fun () -> Monitor.PulseAll pendingWaitObj)
        lock sharedWaitObj (fun () -> Monitor.PulseAll sharedWaitObj)
        lock freeWaitObj (fun () -> Monitor.PulseAll freeWaitObj)

    member _.Dispose() =
        if Runtime.GCSettings.LatencyMode <> Runtime.GCLatencyMode.NoGCRegion then
            let mutable slot = Unchecked.defaultof<CommitSlot>

            while free.TryPop(&slot) do
                slot.Dispose()

            for i = 0 to slots.Length - 1 do
                if not (isNull slots[i]) then
                    slots[i].Dispose()

type internal Worker(?fileAccess: FileAccessGate, ?buffers: ArrayPool<byte>) =
    let fileAccess = defaultArg fileAccess null
    let buffers = defaultArg buffers ArrayPool<byte>.Shared
    let tree = SyntaxTree()
    let alternate = SyntaxTree()
    let document = new DocumentBuffer()
    let printer = new Printer()
    let verifier = SyntaxPreservation.Checker(alternate, tree)
    let syntax = new SyntaxDocumentBuilder(printer, alternate)
    let digest = Array.zeroCreate<byte> 32
    let mutable lastInputLength = 0
    let mutable needsReset = false
    let mutable disposed = false

    static let rentPoolBuffer (pool: ArrayPool<byte>) (target: int) =
        if obj.ReferenceEquals(pool, ArrayPool<byte>.Shared) then
            if target > PoolArray.maxPooledLength then
                GC.AllocateUninitializedArray<byte> target
            elif target >= 16384 then
                SharedBuckets<byte>.Rent target
            else
                pool.Rent target
        else
            pool.Rent target

    static let returnPoolBuffer (pool: ArrayPool<byte>) (buffer: byte array) =
        if not (isNull buffer) && buffer.Length > 0 then
            if obj.ReferenceEquals(pool, ArrayPool<byte>.Shared) then
                if buffer.Length < 16384 then
                    pool.Return buffer
                elif buffer.Length <= PoolArray.maxPooledLength then
                    SharedBuckets<byte>.Return buffer
            else
                pool.Return buffer

    static let growPoolBuffer (pool: ArrayPool<byte>) (buffer: byte array byref) length =
        if buffer.Length < length then
            let target =
                if length > PoolArray.maxPooledLength then
                    max length (buffer.Length + (buffer.Length >>> 1))
                elif obj.ReferenceEquals(pool, ArrayPool<byte>.Shared) then
                    max 16384 length
                else
                    max 4096 length

            let replacement = rentPoolBuffer pool target
            returnPoolBuffer pool buffer
            buffer <- replacement

    let mutable input = Array.empty<byte>
    let mutable output = Array.empty<byte>
    let mutable readBack = Array.empty<byte>
    let mutable printedChars = Array.empty<char>
    let mutable preloadedLength = -1
    let mutable preloadedGated = false
    let mutable preloadError: exn = null

    do
        try
            input <- rentPoolBuffer buffers (64 * 1024)
            output <- rentPoolBuffer buffers (64 * 1024)
            readBack <- rentPoolBuffer buffers (64 * 1024)
        with _ ->
            returnPoolBuffer buffers input
            returnPoolBuffer buffers output
            returnPoolBuffer buffers readBack
            input <- Array.empty<byte>
            output <- Array.empty<byte>
            readBack <- Array.empty<byte>
            reraise ()

    let grow (buffer: byte array byref) length = growPoolBuffer buffers &buffer length

    let maxVerifiedOutputLength (source: string) =
        max VerificationLimit.Characters source.Length

    let maxIntermediateOutputLength (source: string) =
        max (2 * VerificationLimit.Characters) source.Length

    let optionsForSource (settings: Settings) (source: string) =
        if not settings.AutoEndOfLine then
            settings.Printer
        else
            let newline = source.AsSpan().IndexOfAny('\r', '\n')

            let endOfLine =
                if newline >= 0 && source[newline] = '\r' then
                    if newline + 1 < source.Length && source[newline + 1] = '\n' then
                        EndOfLine.CrLf
                    else
                        EndOfLine.Cr
                else
                    EndOfLine.Lf

            if endOfLine = settings.Printer.EndOfLine then
                settings.Printer
            else
                { settings.Printer with
                    EndOfLine = endOfLine
                }

    let generated (source: string) =
        let mutable found = false

        if tree.LexerBuffer.TokenCount > 0 then
            let first = tree.LexerBuffer.Token 0

            for index = first.TriviaStart to first.TriviaStart + first.LeadingCount - 1 do
                let trivia = tree.LexerBuffer.Trivia index

                if
                    trivia.Kind = TriviaKind.SingleLineCommentTrivia
                    || trivia.Kind = TriviaKind.MultiLineCommentTrivia
                then
                    let text = source.AsSpan(trivia.Start, trivia.Length)

                    if
                        text.Contains("<auto-generated".AsSpan(), StringComparison.Ordinal)
                        || text.Contains("<autogenerated".AsSpan(), StringComparison.Ordinal)
                    then
                        found <- true

        found

    let incomplete () =
        if tree.IsComplete then
            null
        else

            let mutable message = null
            let mutable index = 0

            while isNull message && index < tree.TokenCount do
                let token = tree.Token index

                if
                    token.Kind = TokenKind.BadToken
                    || (token.Length = 0
                        && token.Kind <> TokenKind.EndOfFileToken
                        && token.Kind <> TokenKind.OmittedArraySizeExpressionToken
                        && token.Kind <> TokenKind.OmittedTypeArgumentToken)
                then
                    let kind = token.Kind

                    message <-
                        "Incomplete C# syntax at character "
                        + Convert.ToString(token.Start)
                        + " ("
                        + kind.ToString()
                        + ")."

                index <- index + 1

            index <- 0

            while isNull message && index < tree.NodeCount do
                if (tree.Node index).Kind = NodeKind.IncompleteMember then
                    message <- "Incomplete C# member."

                index <- index + 1

            if isNull message && tree.RecoveredTokens > 0 then
                message <-
                    "Unparsed C# syntax ("
                    + Convert.ToString(tree.RecoveredTokens)
                    + " tokens skipped by recovery)."

            message

    let requireCompleteParse (source: string) =
        let message = incomplete ()

        if isNull message then
            true
        else
            let sets = Preprocessor.symbolSets source tree
            let mutable complete = false
            let mutable index = 0

            while not complete && index < sets.Length do
                Parser.parseWith sets[index] source tree
                complete <- isNull (incomplete ())
                index <- index + 1

            if not complete then
                invalidOp message

            false

    let verifyChangedWith
        (retry: bool)
        (filePath: string)
        (source: string)
        (options: PrinterOptions)
        (defaultParseComplete: bool)
        (printed: string)
        : string =
        if max source.Length printed.Length > VerificationLimit.Characters then
            raise (VerificationLimitException(filePath + ": " + VerificationLimit.Message))
        else
            let witness = syntax.Transformations

            let checkedResult =
                verifier.DecideDirect(
                    options,
                    filePath,
                    source,
                    printed,
                    (if defaultParseComplete then
                         tree
                     else
                         Unchecked.defaultof<SyntaxTree>),
                    witness
                )

            match checkedResult with
            | SyntaxPreservation.Verification.Proven -> null
            | SyntaxPreservation.Verification.Violation message ->
                if retry then message else invalidOp message
            | SyntaxPreservation.Verification.Unprovable reason -> reason

    let verifyChanged filePath source options defaultParseComplete printed =
        verifyChangedWith false filePath source options defaultParseComplete printed

    let verify
        (filePath: string)
        (source: string)
        (options: PrinterOptions)
        (defaultParseComplete: bool)
        (printed: string)
        : string =
        if not (String.Equals(source, printed, StringComparison.Ordinal)) then
            verifyChanged filePath source options defaultParseComplete printed
        else
            null

    member _.Print(source: string, settings: Settings) =
        printer.MaxOutputLength <- Array.MaxLength
        syntax.MaxOutputLength <- Array.MaxLength
        Parser.parse source tree
        requireCompleteParse source |> ignore
        document.Reset()
        let options = optionsForSource settings source
        syntax.BuildAndPrint(source, tree, document, options)

    member _.PrintChecked
        (filePath: string, source: string, settings: Settings, ?secondPrint: bool)
        : string =
        if source.Length > VerificationLimit.Characters then
            raise (VerificationLimitException(filePath + ": " + VerificationLimit.Message))

        printer.MaxOutputLength <- maxVerifiedOutputLength source
        syntax.MaxOutputLength <- maxIntermediateOutputLength source
        let mutable defaultParseComplete = false

        try
            Parser.parse source tree
            defaultParseComplete <- requireCompleteParse source
            document.Reset()
            let options = optionsForSource settings source
            syntax.BuildAndPrint(source, tree, document, options)
        with :? VerificationLimitException as error when
            not (error.Message.StartsWith(filePath + ":", StringComparison.Ordinal)) ->
            raise (VerificationLimitException(filePath + ": " + error.Message))

        let options = optionsForSource settings source

        let unverified =
            verify filePath source options defaultParseComplete printer.OutputText

        let symSets = syntax.Transformations.SymbolSets

        if
            isNull unverified
            || isNull symSets
            || symSets.Length = 0
            || not (defaultArg secondPrint true)
        then
            unverified
        else
            try
                Parser.parse source tree
                document.Reset()
                syntax.WhitespaceOnly <- true

                try
                    syntax.BuildAndPrint(source, tree, document, options)
                finally
                    syntax.WhitespaceOnly <- false

                let printed = printer.OutputText

                if
                    String.Equals(source, printed, StringComparison.Ordinal)
                    || isNull (
                        verifyChangedWith true filePath source options defaultParseComplete printed
                    )
                then
                    null
                else
                    unverified
            with :? VerificationLimitException ->
                unverified

    member _.IsGenerated(source: string) =
        let window = min source.Length GeneratedPrefix.window
        Lexer.lexRange source 0 window tree.LexerBuffer
        let first = tree.LexerBuffer.Token 0

        if
            window < source.Length
            && (first.Kind = TokenKind.EndOfFileToken
                || first.Start > window - GeneratedPrefix.lookahead)
        then
            Lexer.lex source tree.LexerBuffer

        generated source

    member _.IsGeneratedPrefix
        (prefix: string, encoding: Encoding, bytes: byte array, offset: int, count: int)
        =
        Lexer.lexRange prefix 0 prefix.Length tree.LexerBuffer
        let first = tree.LexerBuffer.Token 0

        if
            first.Kind = TokenKind.EndOfFileToken
            || first.Start > prefix.Length - GeneratedPrefix.lookahead
        then
            let fullSource =
                try
                    encoding.GetString(bytes, offset, count)
                with :? DecoderFallbackException when offset = 0 ->
                    let struct (_, _, s) = SourceEncoding.decode bytes count
                    s

            Lexer.lex fullSource tree.LexerBuffer
            generated fullSource
        else
            generated prefix

    member _.OutputText = printer.OutputText
    member _.OutputBytes = printer.OutputBytes

    member this.Commit
        (
            path: string,
            snapshot: byte array,
            length: int,
            formatted: byte array,
            size: int,
            stripe: int,
            aliased: bool
        ) =
        this.CommitSpan(
            path,
            snapshot,
            length,
            ReadOnlySpan<byte>(formatted, 0, size),
            stripe,
            aliased
        )

    static member internal CheckCommitWindow
        (
            snapshot: byte array,
            length: int,
            formatted: ReadOnlySpan<byte>,
            window: byte array,
            currentLen: int
        ) =
        let size = formatted.Length

        if currentLen = length || currentLen = size then
            let matchesOutput =
                currentLen = size
                && (size = 0 || ReadOnlySpan<byte>(window, 0, size).SequenceEqual(formatted))

            if matchesOutput then
                -2
            else
                let matchesOriginal =
                    currentLen = length
                    && (length = 0
                        || ReadOnlySpan<byte>(window, 0, length)
                            .SequenceEqual(ReadOnlySpan<byte>(snapshot, 0, length)))

                if matchesOriginal then currentLen else -1
        else
            -1

    static member CommitSpanStatic
        (
            fileAccess: FileAccessGate,
            buffers: ArrayPool<byte>,
            readBack: byte array byref,
            path: string,
            snapshot: byte array,
            length: int,
            formatted: ReadOnlySpan<byte>,
            stripe: int,
            aliased: bool
        ) =
        let size = formatted.Length
        let gated = aliased && not (isNull fileAccess)

        if gated then
            fileAccess.EnterWrite stripe
        elif not (isNull fileAccess) then
            fileAccess.NoteUngatedWrite()

        try
            let maxLen = max length size
            let mutable fastCommitted = false

            if LinkCount.isAvailable () && maxLen < ReadBack.limit then
                growPoolBuffer buffers &readBack (maxLen + 1)
                let window = readBack
                let fd = LinkCount.openFile (path, 0x01000026)

                if fd >= 0 then
                    try
                        let currentLen = LinkCount.preadAll fd window (maxLen + 1)

                        match
                            Worker.CheckCommitWindow(
                                snapshot,
                                length,
                                formatted,
                                window,
                                currentLen
                            )
                        with
                        | -2 -> fastCommitted <- true
                        | currentLen when currentLen >= 0 ->
                            let mutable written = 0

                            while written < size do
                                let rest = formatted.Slice(written)

                                let w =
                                    LinkCount.pwriteBytes (
                                        fd,
                                        &MemoryMarshal.GetReference(rest),
                                        unativeint rest.Length,
                                        int64 written
                                    )

                                if w > 0n then
                                    written <- written + int w
                                elif w = 0n || Marshal.GetLastPInvokeError() <> 4 then
                                    raise (IOException "I/O error writing formatted output.")

                            if size < currentLen then
                                if LinkCount.ftruncateFd (fd, int64 size) <> 0 then
                                    raise (IOException "I/O error truncating formatted output.")

                            fastCommitted <- true
                        | _ -> ()
                    finally
                        LinkCount.closeFd fd |> ignore
            elif LinkCount.isWindowsAvailable () then
                growPoolBuffer buffers &readBack (min ReadBack.limit (maxLen + 1))
                let window = readBack
                let mutable h = LinkCount.openWindowsReadWriteRaw path

                if gated && (h = -1n || h = 0n) then
                    let mutable attempts = 0

                    while (h = -1n || h = 0n) && attempts < 64 do
                        attempts <- attempts + 1
                        Thread.Yield() |> ignore
                        h <- LinkCount.openWindowsReadWriteRaw path

                if h <> -1n && h <> 0n then
                    try
                        if maxLen < ReadBack.limit then
                            let currentLen = LinkCount.readWindowsAll h window (maxLen + 1)

                            match
                                Worker.CheckCommitWindow(
                                    snapshot,
                                    length,
                                    formatted,
                                    window,
                                    currentLen
                                )
                            with
                            | -2 -> fastCommitted <- true
                            | currentLen when currentLen >= 0 ->
                                let mutable written = 0

                                while written < size do
                                    let rest = formatted.Slice(written)

                                    let mutable ov =
                                        Unchecked.defaultof<LinkCount.WindowsOverlapped>

                                    ov.Offset <- uint32 written
                                    let mutable bw = 0u

                                    if
                                        LinkCount.writeWindowsFile (
                                            h,
                                            &MemoryMarshal.GetReference(rest),
                                            uint32 rest.Length,
                                            &bw,
                                            &ov
                                        )
                                            =
                                            0
                                        || bw = 0u
                                    then
                                        raise (IOException "I/O error writing formatted output.")

                                    written <- written + int bw

                                if size < currentLen then
                                    let mutable eof = int64 size

                                    if LinkCount.setWindowsEndOfFile (h, 6, &eof, 8u) = 0 then
                                        raise (IOException "I/O error truncating formatted output.")

                                fastCommitted <- true
                            | _ -> ()
                        else
                            let mutable offset = 0
                            let mutable matchesOriginal = true
                            let mutable matchesOutput = true
                            let mutable eofReached = false
                            let mutable readOk = true

                            while not eofReached
                                  && readOk
                                  && offset <= maxLen
                                  && (matchesOriginal || matchesOutput) do
                                let mutable bytesRead = 0u

                                if
                                    LinkCount.readWindowsSequential (
                                        h,
                                        &window[0],
                                        uint32 window.Length,
                                        &bytesRead,
                                        0n
                                    )
                                        =
                                        0
                                then
                                    readOk <- false
                                elif bytesRead = 0u then
                                    eofReached <- true
                                else
                                    let count = int bytesRead
                                    let chunk = ReadOnlySpan<byte>(window, 0, count)

                                    if
                                        matchesOriginal
                                        && (offset + count > length
                                            || not (
                                                chunk.SequenceEqual(
                                                    ReadOnlySpan<byte>(snapshot, offset, count)
                                                )
                                            ))
                                    then
                                        matchesOriginal <- false

                                    if
                                        matchesOutput
                                        && (offset + count > size
                                            || not (
                                                chunk.SequenceEqual(formatted.Slice(offset, count))
                                            ))
                                    then
                                        matchesOutput <- false

                                    offset <- offset + count

                            if readOk && eofReached then
                                if offset <> length then
                                    matchesOriginal <- false

                                if offset <> size then
                                    matchesOutput <- false

                                if matchesOutput then
                                    fastCommitted <- true
                                elif matchesOriginal then
                                    let mutable written = 0

                                    while written < size do
                                        let rest = formatted.Slice(written)

                                        let mutable ov =
                                            Unchecked.defaultof<LinkCount.WindowsOverlapped>

                                        ov.Offset <- uint32 written
                                        let mutable bw = 0u

                                        if
                                            LinkCount.writeWindowsFile (
                                                h,
                                                &MemoryMarshal.GetReference(rest),
                                                uint32 rest.Length,
                                                &bw,
                                                &ov
                                            )
                                                =
                                                0
                                            || bw = 0u
                                        then
                                            raise (
                                                IOException "I/O error writing formatted output."
                                            )

                                        written <- written + int bw

                                    if size < offset then
                                        let mutable eof = int64 size

                                        if LinkCount.setWindowsEndOfFile (h, 6, &eof, 8u) = 0 then
                                            raise (
                                                IOException "I/O error truncating formatted output."
                                            )

                                    fastCommitted <- true
                    finally
                        LinkCount.closeWindowsHandle h |> ignore

            if not fastCommitted then
                growPoolBuffer buffers &readBack (min ReadBack.limit maxLen)
                let window = readBack

                let openHandle () =
                    if not gated || not (OperatingSystem.IsWindows()) then
                        File.OpenHandle(path, FileMode.Open, FileAccess.ReadWrite, FileShare.None)
                    else
                        let mutable h =
                            Unchecked.defaultof<Microsoft.Win32.SafeHandles.SafeFileHandle>

                        let mutable attempts = 0

                        while isNull h do
                            try
                                h <-
                                    File.OpenHandle(
                                        path,
                                        FileMode.Open,
                                        FileAccess.ReadWrite,
                                        FileShare.None
                                    )
                            with :? IOException when attempts < 64 ->
                                attempts <- attempts + 1
                                Thread.Yield() |> ignore

                        h

                use handle = openHandle ()

                if not fastCommitted then
                    let currentLength = RandomAccess.GetLength handle

                    if currentLength <> int64 length && currentLength <> int64 size then
                        invalidOp "File changed before writing."

                    let total = int currentLength
                    let mutable offset = 0
                    let mutable matchesOriginal = currentLength = int64 length
                    let mutable matchesOutput = currentLength = int64 size

                    while offset < total && (matchesOriginal || matchesOutput) do
                        let count = min window.Length (total - offset)
                        let mutable read = 0

                        while read < count do
                            let n =
                                RandomAccess.Read(
                                    handle,
                                    window.AsSpan(read, count - read),
                                    int64 (offset + read)
                                )

                            if n = 0 then
                                invalidOp "File changed before writing."

                            read <- read + n

                        let chunk = ReadOnlySpan<byte>(window, 0, count)

                        if
                            matchesOriginal
                            && not (
                                chunk.SequenceEqual(ReadOnlySpan<byte>(snapshot, offset, count))
                            )
                        then
                            matchesOriginal <- false

                        if
                            matchesOutput
                            && not (chunk.SequenceEqual(formatted.Slice(offset, count)))
                        then
                            matchesOutput <- false

                        offset <- offset + count

                    if not matchesOutput then
                        if not matchesOriginal then
                            invalidOp "File changed before writing."

                        RandomAccess.Write(handle, formatted, 0L)

                        if int64 size < currentLength then
                            RandomAccess.SetLength(handle, int64 size)
        finally
            if gated then
                fileAccess.ExitWrite stripe

    member _.CommitSpan
        (
            path: string,
            snapshot: byte array,
            length: int,
            formatted: ReadOnlySpan<byte>,
            stripe: int,
            aliased: bool
        ) =
        Worker.CommitSpanStatic(
            fileAccess,
            buffers,
            &readBack,
            path,
            snapshot,
            length,
            formatted,
            stripe,
            aliased
        )

    static member private ReadFromOpenHandle
        (
            buffers: ArrayPool<byte>,
            buf: byte array byref,
            handle: Microsoft.Win32.SafeHandles.SafeFileHandle,
            hinted: int,
            hintLength: int64
        ) =
        if hinted > 0 && int64 hinted = hintLength && hinted < Array.MaxLength then
            growPoolBuffer buffers &buf (hinted + 1)

            let firstRead = LinkCount.readHandleUpTo handle buf (hinted + 1)

            if firstRead = hinted then
                hinted
            else
                let size = RandomAccess.GetLength handle

                if size > int64 Array.MaxLength then
                    invalidOp "File exceeds the formatter's buffer limit."

                let length = int size
                let mutable read = min firstRead length

                if buf.Length < length then
                    let target =
                        if length > 1024 * 1024 then
                            max length (buf.Length + (buf.Length >>> 1))
                        else
                            length

                    let replacement = rentPoolBuffer buffers target

                    if read > 0 then
                        Buffer.BlockCopy(buf, 0, replacement, 0, read)

                    returnPoolBuffer buffers buf
                    buf <- replacement

                while read < length do
                    let count =
                        RandomAccess.Read(handle, buf.AsSpan(read, length - read), int64 read)

                    if count = 0 then
                        raise (EndOfStreamException "File changed while reading.")

                    read <- read + count

                length
        else
            let size = RandomAccess.GetLength handle

            if size > int64 Array.MaxLength then
                invalidOp "File exceeds the formatter's buffer limit."

            let length = int size
            growPoolBuffer buffers &buf length
            let mutable read = 0

            while read < length do
                let count = RandomAccess.Read(handle, buf.AsSpan(read, length - read), int64 read)

                if count = 0 then
                    raise (EndOfStreamException "File changed while reading.")

                read <- read + count

            length

    static member ReadIntoBuffer
        (
            fileAccess: FileAccessGate,
            buffers: ArrayPool<byte>,
            buf: byte array byref,
            path: string,
            links: int,
            hintLength: int64
        ) : struct (int * bool) =
        let hinted = int hintLength
        let mutable fastWinRead = -1

        if
            links < 0
            && (isNull fileAccess || fileAccess.Selective)
            && hinted >= 0
            && int64 hinted = hintLength
            && hinted < Array.MaxLength
        then
            if LinkCount.isAvailable () then
                let fd = LinkCount.openFile (path, 0x01000014)

                if fd >= 0 then
                    try
                        let rawLinks = LinkCount.readRawFdLinks fd

                        if rawLinks >= 1 && (isNull fileAccess || rawLinks = 1) then
                            growPoolBuffer buffers &buf (hinted + 1)

                            if LinkCount.preadAll fd buf (hinted + 1) = hinted then
                                if not (isNull fileAccess) then
                                    fileAccess.Participates 1 |> ignore

                                fastWinRead <- hinted
                    finally
                        LinkCount.closeFd fd |> ignore
            elif LinkCount.isWindowsAvailable () then
                let h = LinkCount.openWindowsReadRaw path

                if h <> -1n && h <> 0n then
                    try
                        let rawLinks = LinkCount.readRawHandleLinks h

                        if rawLinks >= 1 && (isNull fileAccess || rawLinks = 1) then
                            growPoolBuffer buffers &buf (hinted + 1)

                            if LinkCount.readWindowsAll h buf (hinted + 1) = hinted then
                                if not (isNull fileAccess) then
                                    fileAccess.Participates 1 |> ignore

                                fastWinRead <- hinted
                    finally
                        LinkCount.closeWindowsHandle h |> ignore

        if fastWinRead >= 0 then
            struct (fastWinRead, false)
        else
            let resolvedLinks = if links < 0 then 0 else links
            let gated = not (isNull fileAccess) && fileAccess.Participates resolvedLinks

            let length =
                if gated then
                    fileAccess.EnterRead()

                try
                    let mutable fastRead = -1

                    if
                        not gated
                        && LinkCount.isAvailable ()
                        && resolvedLinks >= 1
                        && hinted >= 0
                        && int64 hinted = hintLength
                        && hinted < Array.MaxLength
                    then
                        growPoolBuffer buffers &buf (hinted + 1)
                        let fd = LinkCount.openFile (path, 0x01000014)

                        if fd >= 0 then
                            let n =
                                try
                                    LinkCount.preadAll fd buf (hinted + 1)
                                finally
                                    LinkCount.closeFd fd |> ignore

                            if n = hinted then
                                fastRead <- hinted

                    if fastRead >= 0 then
                        fastRead
                    else
                        use handle =
                            File.OpenHandle(path, FileMode.Open, FileAccess.Read, FileShare.Read)

                        Worker.ReadFromOpenHandle(buffers, &buf, handle, hinted, hintLength)
                finally
                    if gated then
                        fileAccess.ExitRead()

            struct (length, gated)

    member _.LastInputLength = lastInputLength
    member _.NeedsReset = needsReset

    member _.AdoptInput(buffer: byte array byref, length: int, gated: bool, error: exn) =
        let mine = input
        input <- buffer

        if mine.Length > CommitSlot.MaxBytes then
            returnPoolBuffer buffers mine
            buffer <- Array.Empty<byte>()
        else
            buffer <- mine

        preloadedLength <- if isNull error then length else -1
        preloadedGated <- gated
        preloadError <- error

    member this.FormatInto
        (
            index: int,
            file: InputFile,
            previous: HashSet<CacheKey>,
            check: bool,
            includeGenerated: bool,
            links: int,
            hintLength: int64,
            preReadSlot: CommitSlot,
            shard: CommitShard,
            results: FileResult array
        ) =
        let mutable ownedPreRead = preReadSlot
        lastInputLength <- 0
        let fileStart = RunStats.enter ()

        try
            try
                let readStart = RunStats.enter ()

                let struct (srcBuf, length, gated) =
                    if not (isNull ownedPreRead) then
                        if not (isNull ownedPreRead.ReadError) then
                            let err = ownedPreRead.ReadError
                            ownedPreRead.ReadError <- null
                            ExceptionDispatchInfo.Capture(err).Throw()

                        struct (ownedPreRead.Snapshot,
                                ownedPreRead.SnapshotLength,
                                ownedPreRead.Gated)
                    elif preloadedLength >= 0 || not (isNull preloadError) then
                        let err = preloadError
                        let len = preloadedLength
                        let g = preloadedGated
                        preloadError <- null
                        preloadedLength <- -1
                        preloadedGated <- false

                        if not (isNull err) then
                            ExceptionDispatchInfo.Capture(err).Throw()

                        struct (input, len, g)
                    else
                        let struct (len, g) =
                            Worker.ReadIntoBuffer(
                                fileAccess,
                                buffers,
                                &input,
                                file.Path,
                                links,
                                hintLength
                            )

                        struct (input, len, g)

                RunStats.lapse RunStats.tRead readStart
                lastInputLength <- length

                let mutable key = Unchecked.defaultof<CacheKey>

                if not (isNull previous) then
                    SHA256.HashData(srcBuf.AsSpan(0, length), digest.AsSpan()) |> ignore
                    key <- Cache.key (ReadOnlySpan<byte> digest) file.Settings includeGenerated

                if not (isNull previous) && previous.Contains key then
                    results[index] <-
                        {
                            Key = key
                            Cacheable = true
                            Changed = false
                            Cached = true
                            Skipped = false
                            Error = null
                            Unverified = null
                            Notice = null
                        }
                else
                    let preSkipped =
                        if
                            not includeGenerated
                            && length > GeneratedPrefix.window
                            && ReadOnlySpan<byte>(srcBuf, 0, min length GeneratedPrefix.window)
                                .IndexOf("<auto"B)
                               >= 0
                        then
                            let struct (enc, pre, prefix) =
                                SourceEncoding.decodePrefix srcBuf length GeneratedPrefix.window

                            this.IsGeneratedPrefix(prefix, enc, srcBuf, pre, length - pre)
                        else
                            false

                    if preSkipped then
                        results[index] <-
                            {
                                Key = key
                                Cacheable = true
                                Changed = false
                                Cached = false
                                Skipped = true
                                Error = null
                                Unverified = null
                                Notice = null
                            }
                    else
                        let maxVerified = maxVerifiedOutputLength ""
                        let decodeStart = RunStats.enter ()

                        let struct (encoding, preamble, source, oversized) =
                            SourceEncoding.decodeBounded
                                srcBuf
                                length
                                maxVerified
                                GeneratedPrefix.window

                        RunStats.lapse RunStats.tDecode decodeStart

                        let isSkipped =
                            if oversized then
                                if
                                    not includeGenerated
                                    && this.IsGeneratedPrefix(
                                        source,
                                        encoding,
                                        srcBuf,
                                        preamble,
                                        length - preamble
                                    )
                                then
                                    true
                                else
                                    raise (
                                        VerificationLimitException(
                                            file.Path + ": " + VerificationLimit.Message
                                        )
                                    )
                            else
                                let lexStart = RunStats.enter ()

                                let skipped =
                                    if includeGenerated then
                                        Parser.lexOnly source tree
                                        false
                                    else
                                        Parser.lexUnlessGenerated source tree

                                RunStats.lapse RunStats.tLex lexStart

                                if skipped then
                                    true
                                else
                                    let parseStart = RunStats.enter ()
                                    Parser.parseFromLexed source tree
                                    RunStats.lapse RunStats.tParse parseStart
                                    false

                        if isSkipped then
                            results[index] <-
                                {
                                    Key = key
                                    Cacheable = true
                                    Changed = false
                                    Cached = false
                                    Skipped = true
                                    Error = null
                                    Unverified = null
                                    Notice = null
                                }
                        else
                            let completeStart = RunStats.enter ()
                            let defaultParseComplete = requireCompleteParse source
                            RunStats.lapse RunStats.tComplete completeStart
                            let printStart = RunStats.enter ()
                            document.Reset()
                            let options = optionsForSource file.Settings source
                            let utf8Source = SourceEncoding.isUtf8 encoding

                            let knownAscii =
                                if utf8Source then
                                    ValueSome(source.Length = length - preamble)
                                else
                                    ValueNone

                            printer.MaxOutputLength <- maxVerifiedOutputLength source
                            syntax.MaxOutputLength <- maxIntermediateOutputLength source
                            syntax.BuildAndPrint(source, tree, document, options, knownAscii)
                            RunStats.lapse RunStats.tPrint printStart

                            if RunStats.digestEnabled then
                                RunStats.noteDigest index printer.OutputBytes

                            let compareStart = RunStats.enter ()
                            let symSets = syntax.Transformations.SymbolSets

                            let changed =
                                if printer.MatchesText source then
                                    false
                                elif
                                    printer.OutputUtf16Length <> source.Length
                                    || isNull symSets
                                    || symSets.Length = 0
                                then
                                    true
                                elif utf8Source then
                                    not (
                                        printer.OutputBytes.SequenceEqual(
                                            ReadOnlySpan<byte>(srcBuf, preamble, length - preamble)
                                        )
                                    )
                                else
                                    not (
                                        String.Equals(
                                            source,
                                            printer.OutputText,
                                            StringComparison.Ordinal
                                        )
                                    )

                            RunStats.lapse RunStats.tCompare compareStart
                            let verifyStart = RunStats.enter ()
                            let mutable printedLen = 0
                            let mutable printedStr: string = null

                            let unverified =
                                if not changed then
                                    null
                                elif printer.HasCachedText then
                                    let text = printer.OutputText
                                    printedStr <- text
                                    printedLen <- text.Length

                                    verifyChanged file.Path source options defaultParseComplete text
                                else
                                    let outChars = printer.OutputUtf16Length

                                    if
                                        max source.Length outChars > VerificationLimit.Characters
                                    then
                                        raise (
                                            VerificationLimitException(
                                                file.Path + ": " + VerificationLimit.Message
                                            )
                                        )

                                    if outChars > printedChars.Length then
                                        PoolArray.grow &printedChars 0 outChars

                                    let nChars =
                                        if outChars = 0 then
                                            0
                                        else
                                            printer.DecodeOutputTo(
                                                Span<char>(printedChars, 0, outChars)
                                            )

                                    printedLen <- nChars

                                    let checkedResult =
                                        verifier.DecideDirectSpan(
                                            options,
                                            file.Path,
                                            source,
                                            ReadOnlySpan<char>(printedChars, 0, nChars),
                                            (if defaultParseComplete then
                                                 tree
                                             else
                                                 Unchecked.defaultof<SyntaxTree>),
                                            syntax.Transformations
                                        )

                                    match checkedResult with
                                    | SyntaxPreservation.Verification.Proven -> null
                                    | SyntaxPreservation.Verification.Violation message ->
                                        invalidOp message
                                    | SyntaxPreservation.Verification.Unprovable reason -> reason

                            RunStats.lapse RunStats.tVerify verifyStart

                            let struct (changed, unverified) =
                                if isNull unverified || isNull symSets || symSets.Length = 0 then
                                    struct (changed, unverified)
                                else
                                    try
                                        Parser.parse source tree
                                        document.Reset()
                                        syntax.WhitespaceOnly <- true

                                        try
                                            syntax.BuildAndPrint(
                                                source,
                                                tree,
                                                document,
                                                options,
                                                knownAscii
                                            )
                                        finally
                                            syntax.WhitespaceOnly <- false

                                        let text = printer.OutputText

                                        if
                                            String.Equals(source, text, StringComparison.Ordinal)
                                        then
                                            struct (false, null)
                                        elif
                                            isNull (
                                                verifyChangedWith
                                                    true
                                                    file.Path
                                                    source
                                                    options
                                                    defaultParseComplete
                                                    text
                                            )
                                        then
                                            printedStr <- text
                                            printedLen <- text.Length
                                            struct (true, null)
                                        else
                                            struct (changed, unverified)
                                    with :? VerificationLimitException ->
                                        struct (changed, unverified)

                            let commitStart = RunStats.enter ()

                            let writeStripe =
                                if
                                    changed
                                    && isNull unverified
                                    && not check
                                    && gated
                                    && defaultParseComplete
                                then
                                    let mutable count = 0

                                    for i = 0 to tree.TokenCount - 1 do
                                        if (tree.Token i).Kind <> TokenKind.CommaToken then
                                            count <- count + 1

                                    int ((uint32 count * 2654435761u) >>> 24)
                                else
                                    0

                            let mutable formattedKey = key
                            let mutable queuedCommit = false

                            if changed && isNull unverified && not check then
                                if utf8Source && preamble = 0 then
                                    let formatted = printer.OutputBytes
                                    let size = formatted.Length

                                    if not (isNull previous) then
                                        SHA256.HashData(formatted, digest.AsSpan()) |> ignore

                                        formattedKey <-
                                            Cache.key
                                                (ReadOnlySpan<byte> digest)
                                                file.Settings
                                                includeGenerated

                                    let outBufLen = printer.OutputBufferLength

                                    let canSwapPrinterOutput =
                                        obj.ReferenceEquals(buffers, ArrayPool<byte>.Shared)
                                        && size >= 16384
                                        && outBufLen >= 16384
                                        && outBufLen <= CommitSlot.MaxBytes

                                    if
                                        not (isNull ownedPreRead)
                                        && length <= ReadBack.limit
                                        && size <= ReadBack.limit
                                    then
                                        let cSlot = ownedPreRead
                                        ownedPreRead <- null

                                        if canSwapPrinterOutput then
                                            cSlot.EnsureSnapshotCapacity length
                                            let prevFmt = cSlot.Formatted

                                            let replacement =
                                                if
                                                    not (isNull prevFmt)
                                                    && prevFmt.Length >= 16384
                                                    && prevFmt.Length <= CommitSlot.MaxBytes
                                                then
                                                    prevFmt
                                                else
                                                    if
                                                        not (isNull prevFmt) && prevFmt.Length > 0
                                                    then
                                                        returnPoolBuffer buffers prevFmt

                                                    SharedBuckets<byte>.Rent outBufLen

                                            let struct (taken, takenLen) =
                                                printer.SwapOutputBuffer replacement

                                            cSlot.Formatted <- taken
                                            cSlot.FormattedLength <- takenLen
                                        else
                                            cSlot.EnsureCapacity(length, size)
                                            formatted.CopyTo(cSlot.Formatted.AsSpan(0, size))
                                            cSlot.FormattedLength <- size

                                        cSlot.Index <- index
                                        cSlot.SnapshotLength <- length
                                        cSlot.Stripe <- writeStripe
                                        cSlot.Gated <- gated
                                        cSlot.Key <- formattedKey
                                        cSlot.HomeShard.EnqueuePending cSlot
                                        queuedCommit <- true
                                    elif
                                        not (isNull shard)
                                        && length <= ReadBack.limit
                                        && size <= ReadBack.limit
                                    then
                                        let cSlot = shard.PopOrCreateFree()

                                        if canSwapPrinterOutput then
                                            cSlot.EnsureSnapshotCapacity length

                                            if length > 0 then
                                                Buffer.BlockCopy(
                                                    srcBuf,
                                                    0,
                                                    cSlot.Snapshot,
                                                    0,
                                                    length
                                                )

                                            let prevFmt = cSlot.Formatted

                                            let replacement =
                                                if
                                                    not (isNull prevFmt)
                                                    && prevFmt.Length >= 16384
                                                    && prevFmt.Length <= CommitSlot.MaxBytes
                                                then
                                                    prevFmt
                                                else
                                                    if
                                                        not (isNull prevFmt) && prevFmt.Length > 0
                                                    then
                                                        returnPoolBuffer buffers prevFmt

                                                    SharedBuckets<byte>.Rent outBufLen

                                            let struct (taken, takenLen) =
                                                printer.SwapOutputBuffer replacement

                                            cSlot.Formatted <- taken
                                            cSlot.FormattedLength <- takenLen
                                        else
                                            cSlot.EnsureCapacity(length, size)

                                            if length > 0 then
                                                Buffer.BlockCopy(
                                                    srcBuf,
                                                    0,
                                                    cSlot.Snapshot,
                                                    0,
                                                    length
                                                )

                                            formatted.CopyTo(cSlot.Formatted.AsSpan(0, size))
                                            cSlot.FormattedLength <- size

                                        cSlot.Index <- index
                                        cSlot.SnapshotLength <- length
                                        cSlot.Stripe <- writeStripe
                                        cSlot.Gated <- gated
                                        cSlot.Key <- formattedKey
                                        shard.EnqueuePending cSlot
                                        queuedCommit <- true

                                    if not queuedCommit then
                                        this.CommitSpan(
                                            file.Path,
                                            srcBuf,
                                            length,
                                            formatted,
                                            writeStripe,
                                            gated
                                        )
                                else
                                    let charSpan =
                                        if not (isNull printedStr) then
                                            printedStr.AsSpan()
                                        else
                                            ReadOnlySpan<char>(printedChars, 0, printedLen)

                                    let size =
                                        if utf8Source then
                                            printer.OutputBytes.Length + preamble
                                        else
                                            encoding.GetByteCount charSpan + preamble

                                    grow &output size
                                    srcBuf.AsSpan(0, preamble).CopyTo(output.AsSpan())

                                    if utf8Source then
                                        printer.OutputBytes.CopyTo(output.AsSpan(preamble))
                                    else
                                        encoding.GetBytes(charSpan, output.AsSpan(preamble))
                                        |> ignore

                                    if not (isNull previous) then
                                        SHA256.HashData(output.AsSpan(0, size), digest.AsSpan())
                                        |> ignore

                                        formattedKey <-
                                            Cache.key
                                                (ReadOnlySpan<byte> digest)
                                                file.Settings
                                                includeGenerated

                                    if
                                        not (isNull ownedPreRead)
                                        && length <= ReadBack.limit
                                        && size <= ReadBack.limit
                                    then
                                        ownedPreRead.EnsureCapacity(length, size)
                                        let cSlot = ownedPreRead
                                        ownedPreRead <- null

                                        if size > 0 then
                                            Buffer.BlockCopy(output, 0, cSlot.Formatted, 0, size)

                                        cSlot.Index <- index
                                        cSlot.SnapshotLength <- length
                                        cSlot.FormattedLength <- size
                                        cSlot.Stripe <- writeStripe
                                        cSlot.Gated <- gated
                                        cSlot.Key <- formattedKey
                                        cSlot.HomeShard.EnqueuePending cSlot
                                        queuedCommit <- true
                                    elif
                                        not (isNull shard)
                                        && length <= ReadBack.limit
                                        && size <= ReadBack.limit
                                    then
                                        let cSlot = shard.PopOrCreateFree()
                                        let mutable handed = false

                                        try
                                            cSlot.EnsureCapacity(length, size)

                                            if length > 0 then
                                                Buffer.BlockCopy(
                                                    srcBuf,
                                                    0,
                                                    cSlot.Snapshot,
                                                    0,
                                                    length
                                                )

                                            if size > 0 then
                                                Buffer.BlockCopy(
                                                    output,
                                                    0,
                                                    cSlot.Formatted,
                                                    0,
                                                    size
                                                )

                                            cSlot.Index <- index
                                            cSlot.SnapshotLength <- length
                                            cSlot.FormattedLength <- size
                                            cSlot.Stripe <- writeStripe
                                            cSlot.Gated <- gated
                                            cSlot.Key <- formattedKey
                                            shard.EnqueuePending cSlot
                                            handed <- true
                                            queuedCommit <- true
                                        finally
                                            if not handed then
                                                shard.PushFree cSlot

                                    if not queuedCommit then
                                        this.CommitSpan(
                                            file.Path,
                                            srcBuf,
                                            length,
                                            ReadOnlySpan<byte>(output, 0, size),
                                            writeStripe,
                                            gated
                                        )

                            RunStats.lapse RunStats.tCommit commitStart

                            if not queuedCommit then
                                results[index] <-
                                    {
                                        Key = formattedKey
                                        Cacheable = isNull unverified && (not changed || not check)
                                        Changed = changed && isNull unverified
                                        Cached = false
                                        Skipped = false
                                        Error = null
                                        Unverified = unverified
                                        Notice = null
                                    }
            with
            | :? VerificationLimitException as error ->
                let reason =
                    if error.Message.StartsWith(file.Path + ":", StringComparison.Ordinal) then
                        error.Message
                    else
                        file.Path + ": " + error.Message

                results[index] <-
                    { Unchecked.defaultof<FileResult> with
                        Skipped = true
                        Notice = reason + "; the file is unchanged."
                    }
            | error ->
                if error :? OutOfMemoryException then
                    needsReset <- true

                let message =
                    if error.Message.StartsWith(file.Path + ":", StringComparison.Ordinal) then
                        error.Message
                    else
                        file.Path + ": " + error.Message

                results[index] <-
                    { Unchecked.defaultof<FileResult> with
                        Error = message
                    }
        finally
            if not (isNull ownedPreRead) then
                ownedPreRead.HomeShard.PushFree ownedPreRead

            RunStats.fileDone fileStart file.Path

    member this.Format(file: InputFile, previous: HashSet<CacheKey>, check, includeGenerated) =
        this.Format(file, previous, check, includeGenerated, 0, 0L)

    member this.Format
        (file: InputFile, previous: HashSet<CacheKey>, check, includeGenerated, links: int)
        =
        this.Format(file, previous, check, includeGenerated, links, 0L)

    member this.Format
        (
            file: InputFile,
            previous: HashSet<CacheKey>,
            check,
            includeGenerated,
            links: int,
            hintLength: int64
        ) =
        let singleResult = Array.zeroCreate<FileResult> 1

        this.FormatInto(
            0,
            file,
            previous,
            check,
            includeGenerated,
            links,
            hintLength,
            null,
            null,
            singleResult
        )

        singleResult[0]

    static member StackSize = 256 * 1024 * 1024

    static member private JoinStarted(threads: Thread array, started: int) =
        for index = 0 to started - 1 do
            threads[index].Join()

    static member Parallel
        (
            count: int,
            (cancellationToken: CancellationToken): CancellationToken,
            body: unit -> unit,
            ?startThread: Thread -> unit
        ) =
        let failures = ConcurrentQueue<exn>()
        let startThread = defaultArg startThread (fun thread -> thread.Start())

        let threads =
            Array.init count (fun _ ->
                let thread =
                    Thread(
                        ThreadStart(fun () ->
                            try
                                LinkCount.boostThread ()
                                body ()
                            with error ->
                                failures.Enqueue error),
                        Worker.StackSize
                    )

                thread.IsBackground <- true
                thread)

        let mutable started = 0

        try
            for thread in threads do
                startThread thread
                started <- started + 1
        finally
            Worker.JoinStarted(threads, started)

        (cancellationToken: CancellationToken).ThrowIfCancellationRequested()

        match failures.TryPeek() with
        | true, error -> ExceptionDispatchInfo.Capture(error).Throw()
        | _ -> ()

    static member Run(body: unit -> 'T) : 'T =
        let result = ref Unchecked.defaultof<'T>
        Worker.Parallel(1, CancellationToken.None, fun () -> result.Value <- body ())
        result.Value

    static member internal RentPoolBuffer(pool: ArrayPool<byte>, target: int) =
        rentPoolBuffer pool target

    static member internal ReturnPoolBuffer(pool: ArrayPool<byte>, buffer: byte array) =
        returnPoolBuffer pool buffer

    member _.ReleaseBuffers() =
        if not disposed then
            disposed <- true
            (syntax :> IDisposable).Dispose()
            (document :> IDisposable).Dispose()
            (printer :> IDisposable).Dispose()
            verifier.ReleasePooledBuffers()
            tree.ReleasePooledBuffers()
            alternate.ReleasePooledBuffers()
            returnPoolBuffer buffers input
            returnPoolBuffer buffers output
            returnPoolBuffer buffers readBack
            PoolArray.release &printedChars

    interface IDisposable with
        member this.Dispose() =
            if Runtime.GCSettings.LatencyMode <> Runtime.GCLatencyMode.NoGCRegion then
                this.ReleaseBuffers()

[<Sealed; AllowNullLiteral>]
type internal PrefetchRing(capacity: int, buffers: ArrayPool<byte>) =
    let states = Array.init capacity (fun index -> int64 index * 4L)
    let data = Array.init capacity (fun _ -> Array.Empty<byte>())
    let lengths = Array.zeroCreate<int> capacity
    let gatedFlags = Array.zeroCreate<bool> capacity
    let errors = Array.zeroCreate<exn> capacity
    let mutable cursor = -1
    let mutable stopped = false
    let mutable abandoned = false

    static let free (position: int) = int64 position * 4L
    static let reading (position: int) = int64 position * 4L + 1L
    static let ready (position: int) = int64 position * 4L + 2L

    static member NotRead = -2

    member _.Buffers = data

    member _.NextPosition() = Interlocked.Increment(&cursor)

    member _.Stopped = Volatile.Read(&stopped)

    member _.Stop() = Volatile.Write(&stopped, true)

    member _.Abandon() = Volatile.Write(&abandoned, true)

    member _.Abandoned = Volatile.Read(&abandoned)

    member _.TryBeginRead(position: int) =
        let slot = position % capacity
        let target = free position
        let mutable spinner = SpinWait()
        let mutable state = Volatile.Read(&states[slot])

        while state < target
              && not (Volatile.Read(&stopped))
              && not (Volatile.Read(&abandoned)) do
            spinner.SpinOnce()
            state <- Volatile.Read(&states[slot])

        if
            state = target
            && Interlocked.CompareExchange(&states[slot], reading position, target) = target
        then
            slot
        else
            -1

    member _.Publish(slot: int, position: int, length: int, gated: bool, error: exn) =
        lengths[slot] <- length
        gatedFlags[slot] <- gated
        errors[slot] <- error
        Volatile.Write(&states[slot], ready position)

    member this.PublishRead(slot: int, position: int, length: int, gated: bool, error: exn) =
        if data[slot].Length > CommitSlot.MaxBytes then
            Worker.ReturnPoolBuffer(buffers, data[slot])
            data[slot] <- Array.Empty<byte>()
            this.Publish(slot, position, PrefetchRing.NotRead, false, null)
        else
            this.Publish(slot, position, length, gated, error)

    member _.Take(position: int, worker: Worker, cancellationToken: CancellationToken) =
        let slot = position % capacity
        let mutable spinner = SpinWait()
        let mutable looping = true
        let waitStart = RunStats.enter ()

        while looping do
            let state = Volatile.Read(&states[slot])

            if state = ready position then
                let length = lengths[slot]

                if length <> PrefetchRing.NotRead then
                    worker.AdoptInput(&data[slot], length, gatedFlags[slot], errors[slot])
                    RunStats.count RunStats.cAdopted

                errors[slot] <- null
                Volatile.Write(&states[slot], free (position + capacity))
                looping <- false
            elif state = free position then
                if
                    Interlocked.CompareExchange(&states[slot], free (position + capacity), state) =
                        state
                then
                    RunStats.count RunStats.cSelfRead
                    looping <- false
            elif state > ready position then
                looping <- false
            elif Volatile.Read(&abandoned) || cancellationToken.IsCancellationRequested then
                looping <- false
            else
                if state < free position then
                    RunStats.count RunStats.cOlderOccupant

                spinner.SpinOnce()

        RunStats.lapse RunStats.tTake waitStart

    member _.Dispose() =
        if Runtime.GCSettings.LatencyMode <> Runtime.GCLatencyMode.NoGCRegion then
            for index = 0 to data.Length - 1 do
                Worker.ReturnPoolBuffer(buffers, data[index])
                data[index] <- Array.Empty<byte>()

module internal Formatter =
    [<Literal>]
    let private largeFileThreshold = 512 * 1024

    let private checkPrefetchReaders =
        match Int32.TryParse(Environment.GetEnvironmentVariable "CSFF_PREFETCH") with
        | true, n when n >= 0 -> n
        | _ -> 2

    let private retireLargeWorker fileAccess (buffers: ArrayPool<byte>) (worker: Worker) =
        if worker.NeedsReset || worker.LastInputLength >= largeFileThreshold then
            worker.ReleaseBuffers()
            new Worker(fileAccess, buffers)
        else
            worker

    let private measureFiles (files: InputFile array) workerCount (links: int array) =
        let lengths = Array.zeroCreate<int64> files.Length
        let mutable cursor = 0
        let chunk = 128

        let body () =
            LinkCount.boostThread ()
            let mutable looping = true

            while looping do
                let endExclusive = Interlocked.Add(&cursor, chunk)
                let startIdx = endExclusive - chunk

                if startIdx >= files.Length then
                    looping <- false
                else
                    let stop = min endExclusive files.Length

                    for index = startIdx to stop - 1 do
                        let path = files[index].Path
                        let struct (read, size, count) = LinkCount.measure path

                        lengths[index] <-
                            if read then
                                size
                            else
                                try
                                    FileInfo(path).Length
                                with _ ->
                                    0L

                        if not (isNull links) then
                            links[index] <- count

        if workerCount <= 1 || files.Length <= chunk then
            body ()
        else
            let mutable firstError: exn = null

            let safeBody () =
                try
                    body ()
                with ex ->
                    Interlocked.CompareExchange(&firstError, ex, null) |> ignore

            let threads = Array.zeroCreate<Thread>(workerCount - 1)

            for w = 0 to workerCount - 2 do
                let t = Thread(ThreadStart(safeBody))
                t.IsBackground <- true
                t.Start()
                threads[w] <- t

            safeBody ()

            for w = 0 to workerCount - 2 do
                threads[w].Join()

            if not (isNull firstError) then
                ExceptionDispatchInfo.Capture(firstError).Throw()

        lengths

    let claimOrderWithLengths (files: InputFile array) workerCount (links: int array) =
        let order = Array.init files.Length id

        if workerCount > 1 then
            let lengths = measureFiles files workerCount links

            Array.sortInPlaceWith
                (fun a b ->
                    let longest = compare lengths[b] lengths[a]

                    if longest <> 0 then longest else compare a b)
                order

            struct (order, lengths)
        else
            struct (order, null)

    let claimOrder (files: InputFile array) workerCount (links: int array) =
        let struct (order, _) = claimOrderWithLengths files workerCount links
        order

    let scheduleOrderWithKnownLengths
        (files: InputFile array)
        workerCount
        (links: int array)
        (knownLengths: int64 array)
        =
        if workerCount <= 1 then
            struct (Array.init files.Length id, null, 0)
        else
            let lengths =
                if
                    not (isNull knownLengths)
                    && knownLengths.Length = files.Length
                    && (OperatingSystem.IsWindows() || LinkCount.isAvailable ())
                then
                    if not (isNull links) then
                        Array.fill links 0 links.Length -1

                    knownLengths
                else
                    measureFiles files workerCount links

            let threshold = if files.Length >= 512 then 49152L else 16384L
            let mutable largeCount = 0

            for i = 0 to files.Length - 1 do
                if lengths[i] > threshold then
                    largeCount <- largeCount + 1

            let order = Array.zeroCreate<int> files.Length
            let mutable lPos = 0
            let mutable sPos = largeCount

            for i = 0 to files.Length - 1 do
                if lengths[i] > threshold then
                    order[lPos] <- i
                    lPos <- lPos + 1
                else
                    order[sPos] <- i
                    sPos <- sPos + 1

            if largeCount > 1 then
                Array.Sort(
                    order,
                    0,
                    largeCount,
                    Comparer<int>.Create(fun a b ->
                        let longest = compare lengths[b] lengths[a]
                        if longest <> 0 then longest else compare a b)
                )

            struct (order, lengths, largeCount)

    let scheduleOrderWithLengths (files: InputFile array) workerCount (links: int array) =
        scheduleOrderWithKnownLengths files workerCount links null

    let cacheDirectory (root: string) =
        let root = Path.GetFullPath root

        let mutable directory =
            DirectoryInfo(
                if Directory.Exists root then
                    root
                else
                    Path.GetDirectoryName root
            )

        let mutable found = None

        while not (isNull directory) && found.IsNone do
            if Path.Exists(Path.Combine(directory.FullName, ".git")) then
                found <- Some directory.FullName
            else
                directory <- directory.Parent

        match found with
        | Some repository -> Path.Combine(repository, "out", "csff", "cache")
        | None ->
            Path.Combine(
                (if Directory.Exists root then
                     root
                 else
                     Path.GetDirectoryName root),
                ".cache",
                "csff"
            )

    let private wakeShards (shards: CommitShard array) (count: int) =
        for s = 0 to count - 1 do
            if not (isNull shards[s]) then
                shards[s].Wake()

    let private joinLive (threads: Thread array) (count: int) =
        for i = 0 to count - 1 do
            let t = threads[i]

            if not (isNull t) && t.IsAlive then
                t.Join()

    let private freeReadySlots (shards: CommitShard array) (count: int) =
        let mutable slot = Unchecked.defaultof<CommitSlot>

        for s = 0 to count - 1 do
            if not (isNull shards[s]) then
                while shards[s].TryDequeueReady(&slot) do
                    shards[s].PushFree slot

                while shards[s].TryDequeueReadyLarge(&slot) do
                    shards[s].PushFree slot

                while shards[s].TryDequeueReadyMedium(&slot) do
                    shards[s].PushFree slot

    let private freePendingSlots (shards: CommitShard array) (count: int) =
        let mutable slot = Unchecked.defaultof<CommitSlot>

        for s = 0 to count - 1 do
            if not (isNull shards[s]) then
                while shards[s].TryDequeuePending(&slot) do
                    shards[s].PushFree slot

    let private disposeShards (shards: CommitShard array) (count: int) =
        for s = 0 to count - 1 do
            if not (isNull shards[s]) then
                shards[s].Dispose()

    let private drainCommits
        (drainOne: int -> byte array -> struct (bool * byte array))
        (readBack: byref<byte array>)
        =
        let mutable draining = true

        while draining do
            let struct (drained, nextReadBack) = drainOne 0 readBack
            readBack <- nextReadBack
            draining <- drained

    let runWithLengthsAndOptions
        (roots: string array)
        (files: InputFile array)
        (knownLengths: int64 array)
        check
        noCache
        includeGenerated
        jobs
        cachePath
        (buffers: ArrayPool<byte>)
        (largeFileLimitOverride: int voption)
        (cancellationToken: CancellationToken)
        =
        let paths =
            if noCache then
                [||]
            else
                let spellings = Discovery.Spellings()

                roots
                |> Array.map (fun root ->
                    Cache.pathWithSpellings
                        spellings
                        (cachePath |> Option.defaultWith (fun () -> cacheDirectory root))
                        root)

        let previous = Dictionary<string, HashSet<CacheKey>>(StringComparer.Ordinal)

        let caches =
            if noCache then
                Array.zeroCreate<HashSet<CacheKey>> roots.Length
            else
                paths
                |> Array.map (fun path ->
                    match previous.TryGetValue path with
                    | true, entries -> entries
                    | _ ->
                        let entries = Cache.read path
                        previous[path] <- entries
                        entries)

        let workerCount = min jobs files.Length

        let availGiB =
            GC.GetGCMemoryInfo().TotalAvailableMemoryBytes / (1024L * 1024L * 1024L)

        let largeFileLimit =
            match largeFileLimitOverride with
            | ValueSome limit -> max 1 limit
            | ValueNone ->
                if availGiB >= 16L then
                    min 4 (max 2 (workerCount / 3))
                else
                    max 1 (min 2 (int availGiB))

        use largeFileGate = new SemaphoreSlim(largeFileLimit, largeFileLimit)

        let maxGiantRetained =
            if GC.GetGCMemoryInfo().TotalAvailableMemoryBytes < 4L * 1024L * 1024L * 1024L then
                1
            else
                largeFileLimit

        let giantWorkers = ConcurrentStack<Worker>()
        let mutable giantRetained = 0

        use _giantLifetime =
            { new IDisposable with
                member _.Dispose() =
                    let mutable w = Unchecked.defaultof<Worker>

                    while giantWorkers.TryPop(&w) do
                        (w :> IDisposable).Dispose()
            }

        let fileAccess =
            if check || workerCount <= 1 then
                null
            else
                FileAccessGate roots

        let inline runGatedLarge
            (wait: bool)
            index
            (file: InputFile)
            (cache: HashSet<CacheKey>)
            checkMode
            incGen
            linkCount
            hintLength
            (rSlot: CommitSlot)
            (shardObj: CommitShard)
            (outResults: FileResult array)
            =
            let mutable unhandedSlot = rSlot
            let mutable gateEntered = false
            let mutable workerAssigned = false
            let mutable gWorker = Unchecked.defaultof<Worker>

            try
                if wait then
                    let gateStart = RunStats.enter ()
                    largeFileGate.Wait cancellationToken
                    RunStats.lapse RunStats.tLargeGate gateStart
                    gateEntered <- true
                else
                    gateEntered <- largeFileGate.Wait 0

                if gateEntered then
                    if giantWorkers.TryPop(&gWorker) then
                        Interlocked.Decrement(&giantRetained) |> ignore
                    else
                        gWorker <- new Worker(fileAccess, buffers)

                    workerAssigned <- true
                    unhandedSlot <- null

                    gWorker.FormatInto(
                        index,
                        file,
                        cache,
                        checkMode,
                        incGen,
                        linkCount,
                        hintLength,
                        rSlot,
                        shardObj,
                        outResults
                    )
            finally
                try
                    if not (isNull unhandedSlot) then
                        unhandedSlot.HomeShard.PushFree unhandedSlot
                finally
                    try
                        if workerAssigned then
                            if gWorker.NeedsReset then
                                gWorker.ReleaseBuffers()
                            elif Interlocked.Increment(&giantRetained) <= maxGiantRetained then
                                giantWorkers.Push gWorker
                            else
                                Interlocked.Decrement(&giantRetained) |> ignore
                                gWorker.ReleaseBuffers()
                    finally
                        if gateEntered then
                            largeFileGate.Release() |> ignore

            gateEntered

        let results = Array.zeroCreate<FileResult> files.Length
        RunStats.prepareDigests files.Length

        let links =
            if workerCount <= 1 then
                null
            else
                Array.zeroCreate<int> files.Length

        let mutable cancelled = false
        let mutable workerIdSeq = -1

        let useDirect =
            not (String.IsNullOrEmpty(Environment.GetEnvironmentVariable "CSFF_DIRECT_WORKERS"))

        if check || workerCount <= 1 || files.Length < 32 || useDirect then
            let struct (order, lengths, singleClaimLimit) =
                if workerCount > 1 && files.Length >= 32 then
                    let struct (o, l, lc) =
                        scheduleOrderWithKnownLengths files workerCount links knownLengths

                    struct (o, l, max 256 lc)
                else
                    let struct (o, l) = claimOrderWithLengths files workerCount links
                    struct (o, l, 4500)

            let mutable nextClaim = 0

            let claimWorkerBatch () =
                if workerCount <= 1 then
                    let c = Interlocked.Increment(&nextClaim) - 1

                    if c < order.Length then
                        struct (c, c)
                    else
                        struct (order.Length, order.Length - 1)
                else
                    let mutable startIdx = order.Length
                    let mutable endIdx = order.Length - 1
                    let mutable looping = true

                    while looping do
                        let current = Volatile.Read(&nextClaim)
                        let avail = order.Length - current

                        if avail <= 0 then
                            looping <- false
                        else
                            let take =
                                if current < singleClaimLimit || avail <= workerCount * 4 then
                                    1
                                else
                                    min 32 avail

                            if
                                Interlocked.CompareExchange(&nextClaim, current + take, current) =
                                    current
                            then
                                startIdx <- current
                                endIdx <- current + take - 1
                                looping <- false

                    struct (startIdx, endIdx)

            let prefetchCount =
                if
                    check
                    && workerCount > 1
                    && files.Length >= 32
                    && GC.GetGCMemoryInfo().TotalAvailableMemoryBytes >= 4L * 1024L * 1024L * 1024L
                then
                    min checkPrefetchReaders (workerCount - 1)
                else
                    0

            let ring =
                if prefetchCount > 0 then
                    PrefetchRing(min order.Length (max 256 (workerCount * 128)), buffers)
                else
                    null

            let prefetchThreads = Array.zeroCreate<Thread> prefetchCount

            let deferredLarge = ConcurrentQueue<int>()

            let runDeferredLarge (wait: bool) =
                let mutable looping = true
                let mutable item = 0

                while looping
                      && not cancellationToken.IsCancellationRequested
                      && (wait || largeFileGate.CurrentCount > 0)
                      && deferredLarge.TryDequeue(&item) do
                    let linkCount = if isNull links then 0 else links[item]
                    let hintLength = if isNull lengths then 0L else lengths[item]

                    if
                        not (
                            runGatedLarge
                                wait
                                item
                                files[item]
                                caches[files[item].Root]
                                check
                                includeGenerated
                                linkCount
                                hintLength
                                null
                                null
                                results
                        )
                    then
                        deferredLarge.Enqueue item
                        looping <- false

            let prefetchBody () =
                LinkCount.boostThread ()

                try
                    let slots = ring.Buffers
                    let mutable position = ring.NextPosition()

                    while position < order.Length && not ring.Stopped && not ring.Abandoned do
                        let slot = ring.TryBeginRead position
                        RunStats.count RunStats.cReaderPositions

                        if slot < 0 then
                            RunStats.count RunStats.cReaderSkipped
                        else
                            RunStats.count RunStats.cReaderClaimed

                            try
                                let index = order[position]
                                let hintLength = if isNull lengths then 0L else lengths[index]

                                if
                                    hintLength < 0L || hintLength + 1L > int64 CommitSlot.MaxBytes
                                then
                                    ring.Publish(slot, position, PrefetchRing.NotRead, false, null)
                                else
                                    let linkCount = if isNull links then 0 else links[index]

                                    let struct (length, gated) =
                                        Worker.ReadIntoBuffer(
                                            fileAccess,
                                            buffers,
                                            &slots[slot],
                                            files[index].Path,
                                            linkCount,
                                            hintLength
                                        )

                                    ring.PublishRead(slot, position, length, gated, null)
                            with error ->
                                ring.PublishRead(slot, position, 0, false, error)

                        position <- ring.NextPosition()
                with error ->
                    RunStats.count RunStats.cReaderFailed

                    if RunStats.enabled then
                        Console.Error.WriteLine("prefetch reader failed: " + error.ToString())

            try
                try
                    for reader = 0 to prefetchCount - 1 do
                        let thread = Thread(ThreadStart prefetchBody)
                        thread.IsBackground <- true
                        prefetchThreads[reader] <- thread
                        thread.Start()

                    Worker.Parallel(
                        workerCount,
                        (cancellationToken: CancellationToken),
                        fun () ->
                            let mutable worker = new Worker(fileAccess, buffers)

                            use _lifetime =
                                { new IDisposable with
                                    member _.Dispose() = (worker :> IDisposable).Dispose()
                                }

                            let mutable struct (startIdx, endIdx) = claimWorkerBatch ()
                            let mutable finished = false

                            try
                                while startIdx <= endIdx
                                      && not cancellationToken.IsCancellationRequested do
                                    let mutable claim = startIdx

                                    while claim <= endIdx
                                          && not cancellationToken.IsCancellationRequested do
                                        let index = order[claim]
                                        let linkCount = if isNull links then 0 else links[index]

                                        let hintLength =
                                            if isNull lengths then 0L else lengths[index]

                                        if not (isNull ring) then
                                            ring.Take(claim, worker, cancellationToken)

                                        if hintLength >= int64 largeFileThreshold then
                                            if
                                                not (
                                                    runGatedLarge
                                                        (workerCount <= 1)
                                                        index
                                                        files[index]
                                                        caches[files[index].Root]
                                                        check
                                                        includeGenerated
                                                        linkCount
                                                        hintLength
                                                        null
                                                        null
                                                        results
                                                )
                                            then
                                                RunStats.count RunStats.cLargeDeferred
                                                deferredLarge.Enqueue index
                                        else
                                            try
                                                worker.FormatInto(
                                                    index,
                                                    files[index],
                                                    caches[files[index].Root],
                                                    check,
                                                    includeGenerated,
                                                    linkCount,
                                                    hintLength,
                                                    null,
                                                    null,
                                                    results
                                                )
                                            finally
                                                worker <-
                                                    retireLargeWorker fileAccess buffers worker

                                        if
                                            not deferredLarge.IsEmpty
                                            && not cancellationToken.IsCancellationRequested
                                        then
                                            runDeferredLarge false

                                        claim <- claim + 1

                                    let struct (nextStart, nextEnd) = claimWorkerBatch ()
                                    startIdx <- nextStart
                                    endIdx <- nextEnd

                                if not cancellationToken.IsCancellationRequested then
                                    runDeferredLarge true

                                finished <- not cancellationToken.IsCancellationRequested
                            finally
                                if not finished && not (isNull ring) then
                                    ring.Abandon()
                    )
                with :? OperationCanceledException when cancellationToken.IsCancellationRequested ->
                    cancelled <- true
            finally
                if not (isNull ring) then
                    ring.Stop()
                    joinLive prefetchThreads prefetchCount
                    ring.Dispose()
        else
            let struct (order, lengths, largeCount) =
                scheduleOrderWithKnownLengths files workerCount links knownLengths

            let ioShards =
                if OperatingSystem.IsWindows() then
                    max 2 (min 8 (workerCount / 3))
                else
                    max 2 (min 3 (workerCount / 4))

            let slotsPerShard =
                if OperatingSystem.IsWindows() then
                    min 192 (max 16 ((files.Length + ioShards - 1) / ioShards))
                else
                    min 320 (max 16 ((files.Length + ioShards - 1) / ioShards))

            let readerDrainThreshold = max 64 (slotsPerShard - 96)

            let readerThreadCount =
                if OperatingSystem.IsWindows() then
                    ioShards
                else
                    let desired = max ioShards (min 9 ((workerCount * 3 + 3) / 4))
                    min desired (max ioShards ((files.Length + 15) / 16))

            let shards = Array.zeroCreate<CommitShard> ioShards

            let smallWorkers =
                if OperatingSystem.IsWindows() then
                    if workerCount >= 4 then max 1 (workerCount * 2 / 3) else 0
                else if workerCount >= 4 then
                    max 1 (workerCount / 6)
                else
                    0

            let largeWorkers = workerCount - smallWorkers

            let mutable giantCount = 0

            if not (isNull lengths) then
                while giantCount < largeCount
                      && lengths[order[giantCount]] >= int64 largeFileThreshold do
                    giantCount <- giantCount + 1

            let mutable mediumCount = giantCount

            if not (isNull lengths) then
                while mediumCount < largeCount && lengths[order[mediumCount]] >= 131072L do
                    mediumCount <- mediumCount + 1

            let mediumWorkers = max largeFileLimit (min largeWorkers 4)
            let mutable gCursor = 0
            let mutable mCursor = giantCount
            let mutable lCursor = mediumCount
            let smallTotal = max 0 (order.Length - largeCount)
            let sPartitions = readerThreadCount

            let sCursors =
                Array.init sPartitions (fun p -> largeCount + (p * smallTotal) / sPartitions)

            let sLimits =
                Array.init sPartitions (fun p -> largeCount + ((p + 1) * smallTotal) / sPartitions)

            let mutable remainingSmall = smallTotal
            let mutable inFlightReads = 0
            let mutable workersDone = false
            let mutable ioAborted = false
            let ioFailures = ConcurrentQueue<exn>()

            let signalAbort () =
                Volatile.Write(&ioAborted, true)
                Volatile.Write(&workersDone, true)

                for s = 0 to ioShards - 1 do
                    if not (isNull shards[s]) then
                        shards[s].Wake()

            let claimGiantOne () =
                let c = Interlocked.Increment(&gCursor) - 1

                if c < giantCount then
                    struct (c, c)
                else
                    struct (order.Length, order.Length - 1)

            let claimMediumOne () =
                let c = Interlocked.Increment(&mCursor) - 1

                if c < mediumCount then
                    struct (c, c)
                else
                    struct (order.Length, order.Length - 1)

            let claimLargeOne () =
                let c = Interlocked.Increment(&lCursor) - 1

                if c < largeCount then
                    struct (c, c)
                else
                    struct (order.Length, order.Length - 1)

            let claimLargeBatch (maxTake: int) =
                let mutable startIdx = order.Length
                let mutable endIdx = order.Length - 1
                let mutable looping = true

                while looping do
                    let current = Volatile.Read(&lCursor)
                    let avail = largeCount - current

                    if avail <= 0 then
                        looping <- false
                    else
                        let take = if avail <= workerCount * 2 then 1 else min maxTake avail

                        if
                            Interlocked.CompareExchange(&lCursor, current + take, current) = current
                        then
                            startIdx <- current
                            endIdx <- current + take - 1
                            looping <- false

                struct (startIdx, endIdx)

            let claimSmallFromPartition (startPart: int) (maxTake: int) =
                let mutable startIdx = order.Length
                let mutable endIdx = order.Length - 1
                let mutable offset = 0

                while startIdx > endIdx && offset < sPartitions do
                    let p = (startPart + offset) % sPartitions
                    let limit = sLimits[p]
                    let mutable looping = true

                    while looping do
                        let current = Volatile.Read(&sCursors[p])
                        let avail = limit - current

                        if avail <= 0 then
                            looping <- false
                        else
                            let rem = Volatile.Read(&remainingSmall)

                            let take =
                                if rem <= workerCount * 8 then 1
                                elif rem <= workerCount * 32 then min 4 (min maxTake avail)
                                else min maxTake avail

                            if
                                Interlocked.CompareExchange(&sCursors[p], current + take, current) =
                                    current
                            then
                                Interlocked.Add(&remainingSmall, -take) |> ignore
                                startIdx <- current
                                endIdx <- current + take - 1
                                looping <- false

                    offset <- offset + 1

                struct (startIdx, endIdx)

            let tryDequeueReadyMedium (homeShard: int) =
                let mutable rSlot = Unchecked.defaultof<CommitSlot>
                let mutable found = false
                let mutable offset = 0

                while not found && offset < ioShards do
                    let s = (homeShard + offset) % ioShards

                    if shards[s].TryDequeueReadyMedium(&rSlot) then
                        found <- true

                    offset <- offset + 1

                if found then rSlot else null

            let tryDequeueReadyLarge (homeShard: int) =
                let mutable rSlot = Unchecked.defaultof<CommitSlot>
                let mutable found = false
                let mutable offset = 0

                while not found && offset < ioShards do
                    let s = (homeShard + offset) % ioShards

                    if shards[s].TryDequeueReadyLarge(&rSlot) then
                        found <- true

                    offset <- offset + 1

                if found then rSlot else null

            let tryDequeueReady (homeShard: int) =
                let mutable rSlot = Unchecked.defaultof<CommitSlot>
                let mutable found = false
                let mutable offset = 0

                while not found && offset < ioShards do
                    let s = (homeShard + offset) % ioShards

                    if shards[s].TryDequeueReady(&rSlot) then
                        found <- true

                    offset <- offset + 1

                if found then rSlot else null

            let tryDequeueAnyReady (homeShard: int) =
                let s0 = tryDequeueReady homeShard

                if not (isNull s0) then
                    s0
                else
                    let s1 = tryDequeueReadyLarge homeShard

                    if not (isNull s1) then
                        s1
                    else
                        tryDequeueReadyMedium homeShard

            let allPendingEmpty () =
                let mutable empty = true

                for s = 0 to ioShards - 1 do
                    if not (isNull shards[s]) && not shards[s].IsEmpty then
                        empty <- false

                empty

            let tryDrainOneCommit (homeShard: int) (readBackIn: byte array) =
                let mutable cSlot = Unchecked.defaultof<CommitSlot>
                let mutable found = false
                let mutable offset = 0
                let isDone = Volatile.Read(&workersDone)

                while not found && offset < ioShards do
                    let s = (homeShard + offset) % ioShards

                    if
                        (offset = 0 || isDone || shards[s].PendingCount > 64)
                        && shards[s].TryDequeuePending(&cSlot)
                    then
                        found <- true

                    offset <- offset + 1

                if found then
                    let mutable readBack = readBackIn
                    let index = cSlot.Index
                    let path = files[index].Path

                    try
                        try
                            if
                                not (Volatile.Read(&ioAborted))
                                && not cancellationToken.IsCancellationRequested
                            then
                                Worker.CommitSpanStatic(
                                    fileAccess,
                                    buffers,
                                    &readBack,
                                    path,
                                    cSlot.Snapshot,
                                    cSlot.SnapshotLength,
                                    ReadOnlySpan<byte>(cSlot.Formatted, 0, cSlot.FormattedLength),
                                    cSlot.Stripe,
                                    cSlot.Gated
                                )

                                results[index] <-
                                    {
                                        Key = cSlot.Key
                                        Cacheable = true
                                        Changed = true
                                        Cached = false
                                        Skipped = false
                                        Error = null
                                        Unverified = null
                                        Notice = null
                                    }
                        with error ->
                            let message =
                                if
                                    error.Message.StartsWith(path + ":", StringComparison.Ordinal)
                                then
                                    error.Message
                                else
                                    path + ": " + error.Message

                            results[index] <-
                                { Unchecked.defaultof<FileResult> with
                                    Error = message
                                }
                    finally
                        cSlot.HomeShard.PushFree cSlot

                    struct (true, readBack)
                else
                    struct (false, readBackIn)

            let commitThreadCount =
                if OperatingSystem.IsWindows() then
                    max ioShards (min 8 (workerCount / 3))
                elif files.Length >= 512 && workerCount >= 8 then
                    min 6 (ioShards * 2)
                else
                    ioShards

            let readerThreads = Array.zeroCreate<Thread> readerThreadCount
            let commitThreads = Array.zeroCreate<Thread> commitThreadCount
            let sharedWaitObj = obj ()
            let sharedWaiting = ref 0
            let mutable activeFormattingWorkers = workerCount

            let readClaimedIntoSlot (rSlot: CommitSlot) (index: int) =
                rSlot.Index <- index
                let linkCount = if isNull links then 0 else links[index]
                let hintLength = if isNull lengths then 0L else lengths[index]
                let mutable snap = rSlot.Snapshot

                try
                    try
                        let struct (len, gated) =
                            Worker.ReadIntoBuffer(
                                fileAccess,
                                buffers,
                                &snap,
                                files[index].Path,
                                linkCount,
                                hintLength
                            )

                        rSlot.SnapshotLength <- len
                        rSlot.Gated <- gated
                        rSlot.ReadError <- null
                    with error ->
                        rSlot.SnapshotLength <- 0
                        rSlot.Gated <- false
                        rSlot.ReadError <- error
                finally
                    rSlot.Snapshot <- snap

            try
                for s = 0 to ioShards - 1 do
                    shards[s] <- CommitShard(slotsPerShard, buffers, sharedWaitObj, sharedWaiting)

                for rid = 0 to readerThreadCount - 1 do
                    let shard = rid % ioShards
                    let myShard = shards[shard]

                    let t =
                        Thread(
                            ThreadStart(fun () ->
                                LinkCount.boostThread ()
                                let mutable readBack: byte array = null
                                let mutable localSlots: CommitSlot array = null

                                try
                                    try
                                        localSlots <- Array.zeroCreate<CommitSlot> 8
                                        let mutable reading = true

                                        while reading
                                              && not (Volatile.Read(&workersDone))
                                              && not (Volatile.Read(&ioAborted))
                                              && not cancellationToken.IsCancellationRequested do
                                            let hasMoreSmall = Volatile.Read(&remainingSmall) > 0
                                            let hasMoreLarge = Volatile.Read(&lCursor) < largeCount

                                            let hasMoreMedium =
                                                Volatile.Read(&mCursor) < mediumCount

                                            if
                                                not hasMoreSmall
                                                && not hasMoreLarge
                                                && not hasMoreMedium
                                            then
                                                reading <- false
                                            else
                                                let mutable tier = 0
                                                let mutable popCount = 0

                                                if
                                                    (rid < ioShards || not hasMoreSmall)
                                                    && hasMoreMedium
                                                    && myShard.ReadyMediumCount < 6
                                                then
                                                    let mutable freeSlot =
                                                        Unchecked.defaultof<CommitSlot>

                                                    if myShard.TryPopFree(&freeSlot) then
                                                        localSlots[0] <- freeSlot
                                                        popCount <- 1
                                                        tier <- 1

                                                if
                                                    popCount = 0
                                                    && (rid < ioShards * 2 || not hasMoreSmall)
                                                    && hasMoreLarge
                                                    && myShard.ReadyLargeCount < 20
                                                then
                                                    let mutable popping = true

                                                    while popping && popCount < 4 do
                                                        let mutable freeSlot =
                                                            Unchecked.defaultof<CommitSlot>

                                                        if myShard.TryPopFree(&freeSlot) then
                                                            localSlots[popCount] <- freeSlot
                                                            popCount <- popCount + 1
                                                        else
                                                            popping <- false

                                                    if popCount > 0 then
                                                        tier <- 2

                                                if
                                                    popCount = 0
                                                    && hasMoreSmall
                                                    && myShard.ReadyCount < 112
                                                then
                                                    let mutable popping = true

                                                    while popping && popCount < 8 do
                                                        let mutable freeSlot =
                                                            Unchecked.defaultof<CommitSlot>

                                                        if myShard.TryPopFree(&freeSlot) then
                                                            localSlots[popCount] <- freeSlot
                                                            popCount <- popCount + 1
                                                        else
                                                            popping <- false

                                                    if popCount > 0 then
                                                        tier <- 3

                                                if popCount = 0 then
                                                    if
                                                        Volatile.Read(&workersDone)
                                                        || Volatile.Read(&ioAborted)
                                                        || (Volatile.Read(&remainingSmall) <= 0
                                                            && Volatile.Read(&lCursor)
                                                               >= largeCount
                                                            && Volatile.Read(&mCursor)
                                                               >= mediumCount)
                                                    then
                                                        reading <- false
                                                    else
                                                        let mutable drained = false

                                                        if
                                                            myShard.PendingCount >
                                                                readerDrainThreshold
                                                        then
                                                            if isNull readBack then
                                                                readBack <-
                                                                    Worker.RentPoolBuffer(
                                                                        buffers,
                                                                        64 * 1024
                                                                    )

                                                            let struct (d, nextReadBack) =
                                                                tryDrainOneCommit shard readBack

                                                            readBack <- nextReadBack
                                                            drained <- d

                                                        if not drained then
                                                            myShard.WaitForFree()
                                                else
                                                    let mutable remainingInFlight = popCount

                                                    Interlocked.Add(&inFlightReads, popCount)
                                                    |> ignore

                                                    try
                                                        let struct (startIdx, endIdx) =
                                                            if tier = 1 then
                                                                claimMediumOne ()
                                                            elif tier = 2 then
                                                                claimLargeBatch popCount
                                                            else
                                                                claimSmallFromPartition
                                                                    rid
                                                                    popCount

                                                        let actual =
                                                            if startIdx <= endIdx then
                                                                endIdx - startIdx + 1
                                                            else
                                                                0

                                                        if actual < popCount then
                                                            let unused = popCount - actual

                                                            Interlocked.Add(
                                                                &inFlightReads,
                                                                -unused
                                                            )
                                                            |> ignore

                                                            remainingInFlight <- actual

                                                            for i = actual to popCount - 1 do
                                                                myShard.PushFree localSlots[i]
                                                                localSlots[i] <- null

                                                        for i = 0 to actual - 1 do
                                                            let rSlot = localSlots[i]
                                                            localSlots[i] <- null
                                                            let index = order[startIdx + i]
                                                            readClaimedIntoSlot rSlot index

                                                            if tier = 1 then
                                                                myShard.EnqueueReadyMedium rSlot
                                                            elif tier = 2 then
                                                                myShard.EnqueueReadyLarge rSlot
                                                            else
                                                                myShard.EnqueueReady rSlot

                                                            Interlocked.Decrement(&inFlightReads)
                                                            |> ignore

                                                            remainingInFlight <-
                                                                remainingInFlight - 1

                                                        if
                                                            actual = 0
                                                            && Volatile.Read(&remainingSmall) <= 0
                                                            && Volatile.Read(&lCursor)
                                                               >= largeCount
                                                            && Volatile.Read(&mCursor)
                                                               >= mediumCount
                                                        then
                                                            reading <- false
                                                    finally
                                                        if remainingInFlight > 0 then
                                                            Interlocked.Add(
                                                                &inFlightReads,
                                                                -remainingInFlight
                                                            )
                                                            |> ignore

                                        if rid < ioShards then
                                            if isNull readBack then
                                                readBack <-
                                                    Worker.RentPoolBuffer(buffers, 64 * 1024)

                                            let mutable spinning = true

                                            while spinning
                                                  && not (Volatile.Read(&ioAborted))
                                                  && not cancellationToken.IsCancellationRequested do
                                                let struct (drained, nextReadBack) =
                                                    tryDrainOneCommit shard readBack

                                                readBack <- nextReadBack

                                                if not drained then
                                                    if
                                                        Volatile.Read(&workersDone)
                                                        && allPendingEmpty ()
                                                    then
                                                        spinning <- false
                                                    else
                                                        myShard.WaitForWork allPendingEmpty
                                        else
                                            let mutable drainingTail = myShard.PendingCount > 32

                                            while drainingTail
                                                  && not (Volatile.Read(&ioAborted))
                                                  && not cancellationToken.IsCancellationRequested do
                                                if isNull readBack then
                                                    readBack <-
                                                        Worker.RentPoolBuffer(buffers, 64 * 1024)

                                                let struct (drained, nextReadBack) =
                                                    tryDrainOneCommit shard readBack

                                                readBack <- nextReadBack

                                                drainingTail <-
                                                    drained && myShard.PendingCount > 32
                                    with error ->
                                        ioFailures.Enqueue error
                                        signalAbort ()
                                finally
                                    if not (isNull localSlots) then
                                        for i = 0 to localSlots.Length - 1 do
                                            if not (isNull localSlots[i]) then
                                                myShard.PushFree localSlots[i]
                                                localSlots[i] <- null

                                    if not (isNull readBack) && readBack.Length > 0 then
                                        Worker.ReturnPoolBuffer(buffers, readBack))
                        )

                    t.IsBackground <- true
                    readerThreads[rid] <- t

                for cid = 0 to commitThreadCount - 1 do
                    let shard = cid % ioShards
                    let myShard = shards[shard]

                    let t =
                        Thread(
                            ThreadStart(fun () ->
                                LinkCount.boostThread ()
                                let mutable readBack: byte array = null

                                try
                                    try
                                        readBack <- Worker.RentPoolBuffer(buffers, 64 * 1024)
                                        let mutable spinning = true

                                        while spinning
                                              && not (Volatile.Read(&ioAborted))
                                              && not cancellationToken.IsCancellationRequested do
                                            let struct (drained, nextReadBack) =
                                                tryDrainOneCommit shard readBack

                                            readBack <- nextReadBack

                                            if not drained then
                                                if
                                                    Volatile.Read(&workersDone)
                                                    && allPendingEmpty ()
                                                then
                                                    spinning <- false
                                                else
                                                    myShard.WaitForWork allPendingEmpty
                                    with error ->
                                        ioFailures.Enqueue error
                                        signalAbort ()
                                finally
                                    if not (isNull readBack) && readBack.Length > 0 then
                                        Worker.ReturnPoolBuffer(buffers, readBack))
                        )

                    t.IsBackground <- true
                    commitThreads[cid] <- t

                for t in readerThreads do
                    t.Start()

                for t in commitThreads do
                    t.Start()

                try
                    Worker.Parallel(
                        workerCount,
                        (cancellationToken: CancellationToken),
                        fun () ->
                            try
                                let wid = Interlocked.Increment(&workerIdSeq)
                                let preferGiant = wid < largeFileLimit
                                let preferMedium = wid < mediumWorkers
                                let preferLarge = wid < largeWorkers
                                let homeShard = wid % ioShards
                                let homePart = wid % sPartitions
                                let shardObj = shards[homeShard]
                                let mutable worker = new Worker(fileAccess, buffers)

                                use _lifetime =
                                    { new IDisposable with
                                        member _.Dispose() = (worker :> IDisposable).Dispose()
                                    }

                                let mutable readBack: byte array = null

                                try
                                    let formatDirectIndex index (rSlot: CommitSlot) =
                                        let linkCount = if isNull links then 0 else links[index]

                                        let hintLength =
                                            if isNull lengths then 0L else lengths[index]

                                        if hintLength >= int64 largeFileThreshold then
                                            runGatedLarge
                                                true
                                                index
                                                files[index]
                                                caches[files[index].Root]
                                                check
                                                includeGenerated
                                                linkCount
                                                hintLength
                                                rSlot
                                                shardObj
                                                results
                                            |> ignore
                                        else
                                            try
                                                worker.FormatInto(
                                                    index,
                                                    files[index],
                                                    caches[files[index].Root],
                                                    check,
                                                    includeGenerated,
                                                    linkCount,
                                                    hintLength,
                                                    rSlot,
                                                    shardObj,
                                                    results
                                                )
                                            finally
                                                worker <-
                                                    retireLargeWorker fileAccess buffers worker

                                    let mutable keepWorking = true
                                    let mutable tailSpins = 0

                                    while keepWorking
                                          && not (Volatile.Read(&ioAborted))
                                          && not cancellationToken.IsCancellationRequested do
                                        let mutable didStep = false

                                        if preferGiant && Volatile.Read(&gCursor) < giantCount then
                                            let struct (s, e) = claimGiantOne ()

                                            if s <= e then
                                                formatDirectIndex order[s] null
                                                didStep <- true

                                        if not didStep && preferMedium then
                                            let mSlot = tryDequeueReadyMedium homeShard

                                            if not (isNull mSlot) then
                                                formatDirectIndex mSlot.Index mSlot
                                                didStep <- true

                                        if not didStep && preferLarge then
                                            let lSlot = tryDequeueReadyLarge homeShard

                                            if not (isNull lSlot) then
                                                formatDirectIndex lSlot.Index lSlot
                                                didStep <- true

                                        if not didStep then
                                            let rSlot = tryDequeueReady homeShard

                                            if not (isNull rSlot) then
                                                formatDirectIndex rSlot.Index rSlot
                                                didStep <- true

                                        if not didStep then
                                            let lSlot = tryDequeueReadyLarge homeShard

                                            if not (isNull lSlot) then
                                                formatDirectIndex lSlot.Index lSlot
                                                didStep <- true

                                        if
                                            not didStep
                                            && preferMedium
                                            && Volatile.Read(&mCursor) < mediumCount
                                        then
                                            let struct (s, e) = claimMediumOne ()

                                            if s <= e then
                                                formatDirectIndex order[s] null
                                                didStep <- true

                                        if not didStep && Volatile.Read(&lCursor) < largeCount then
                                            let struct (s, e) = claimLargeOne ()

                                            if s <= e then
                                                formatDirectIndex order[s] null
                                                didStep <- true

                                        if not didStep && Volatile.Read(&remainingSmall) > 0 then
                                            let struct (s, e) = claimSmallFromPartition homePart 1

                                            if s <= e then
                                                for c = s to e do
                                                    if
                                                        not (Volatile.Read(&ioAborted))
                                                        && not
                                                            cancellationToken
                                                                .IsCancellationRequested
                                                    then
                                                        formatDirectIndex order[c] null

                                                didStep <- true

                                        if not didStep && not (allPendingEmpty ()) then
                                            if isNull readBack then
                                                readBack <-
                                                    Worker.RentPoolBuffer(buffers, 64 * 1024)

                                            let struct (drained, nextReadBack) =
                                                tryDrainOneCommit homeShard readBack

                                            readBack <- nextReadBack

                                            if drained then
                                                didStep <- true

                                        if not didStep then
                                            let rSlot = tryDequeueAnyReady homeShard

                                            if not (isNull rSlot) then
                                                formatDirectIndex rSlot.Index rSlot
                                                tailSpins <- 0
                                            elif Volatile.Read(&lCursor) < largeCount then
                                                let struct (s, e) = claimLargeOne ()

                                                if s <= e then
                                                    formatDirectIndex order[s] null
                                                    tailSpins <- 0
                                            elif Volatile.Read(&mCursor) < mediumCount then
                                                let struct (s, e) = claimMediumOne ()

                                                if s <= e then
                                                    formatDirectIndex order[s] null
                                                    tailSpins <- 0
                                            elif Volatile.Read(&gCursor) < giantCount then
                                                let struct (s, e) = claimGiantOne ()

                                                if s <= e then
                                                    formatDirectIndex order[s] null
                                                    tailSpins <- 0
                                            elif Volatile.Read(&inFlightReads) > 0 then
                                                Thread.SpinWait 64
                                                tailSpins <- tailSpins + 1

                                                if tailSpins &&& 15 = 0 then
                                                    Thread.Sleep 0
                                            else
                                                let lateSlot = tryDequeueAnyReady homeShard

                                                if not (isNull lateSlot) then
                                                    formatDirectIndex lateSlot.Index lateSlot
                                                    tailSpins <- 0
                                                else
                                                    keepWorking <- false
                                        else
                                            tailSpins <- 0

                                    if Interlocked.Decrement(&activeFormattingWorkers) = 0 then
                                        Volatile.Write(&workersDone, true)

                                        for s = 0 to ioShards - 1 do
                                            if not (isNull shards[s]) then
                                                shards[s].Wake()

                                    if not (allPendingEmpty ()) then
                                        if isNull readBack then
                                            readBack <- Worker.RentPoolBuffer(buffers, 64 * 1024)

                                        let mutable draining = true

                                        while draining
                                              && not (Volatile.Read(&ioAborted))
                                              && not cancellationToken.IsCancellationRequested do
                                            let struct (drained, nextReadBack) =
                                                tryDrainOneCommit homeShard readBack

                                            readBack <- nextReadBack
                                            draining <- drained

                                        if Volatile.Read(&workersDone) && allPendingEmpty () then
                                            for s = 0 to ioShards - 1 do
                                                if not (isNull shards[s]) then
                                                    shards[s].Wake()
                                finally
                                    if not (isNull readBack) && readBack.Length > 0 then
                                        Worker.ReturnPoolBuffer(buffers, readBack)
                            with _ ->
                                signalAbort ()
                                reraise ()
                    )
                with :? OperationCanceledException when cancellationToken.IsCancellationRequested ->
                    cancelled <- true
            finally
                Volatile.Write(&workersDone, true)
                wakeShards shards ioShards
                joinLive readerThreads readerThreadCount
                joinLive commitThreads commitThreadCount

                if cancellationToken.IsCancellationRequested then
                    cancelled <- true

                try
                    freeReadySlots shards ioShards

                    if not cancelled && not (Volatile.Read(&ioAborted)) then
                        let mutable readBack: byte array = null

                        try
                            try
                                readBack <- Worker.RentPoolBuffer(buffers, 64 * 1024)
                                drainCommits tryDrainOneCommit &readBack
                            with error ->
                                ioFailures.Enqueue error
                        finally
                            if not (isNull readBack) && readBack.Length > 0 then
                                Worker.ReturnPoolBuffer(buffers, readBack)

                        if cancellationToken.IsCancellationRequested then
                            cancelled <- true
                    else
                        freePendingSlots shards ioShards
                finally
                    disposeShards shards ioShards

            match ioFailures.TryPeek() with
            | true, error -> ExceptionDispatchInfo.Capture(error).Throw()
            | _ -> ()

        if not (isNull fileAccess) && FileAccessGate.Instrumented then
            Console.Error.WriteLine fileAccess.Statistics

        if not noCache then
            let pending = Dictionary<string, HashSet<CacheKey>>(StringComparer.Ordinal)

            let current =
                paths
                |> Array.mapi (fun index path ->
                    match pending.TryGetValue path with
                    | true, entries -> entries
                    | _ ->
                        let entries =
                            if cancelled then
                                HashSet<CacheKey>(caches[index])
                            else
                                HashSet<CacheKey>()

                        pending[path] <- entries
                        entries)

            for index = 0 to results.Length - 1 do
                let result = results[index]
                let cache = current[files[index].Root]

                if result.Cacheable && cache.Count < Cache.MaximumEntries then
                    cache.Add result.Key |> ignore

            for entry in pending do
                try
                    Cache.save entry.Key previous[entry.Key] entry.Value
                with
                | :? IOException as error ->
                    Console.Error.WriteLine("csff: cache unavailable: " + error.Message)
                | :? UnauthorizedAccessException as error ->
                    Console.Error.WriteLine("csff: cache unavailable: " + error.Message)

        if cancelled then
            (cancellationToken: CancellationToken).ThrowIfCancellationRequested()

        results

    let runWithLengths
        (roots: string array)
        (files: InputFile array)
        (knownLengths: int64 array)
        check
        noCache
        includeGenerated
        jobs
        cachePath
        (cancellationToken: CancellationToken)
        =
        runWithLengthsAndOptions
            roots
            files
            knownLengths
            check
            noCache
            includeGenerated
            jobs
            cachePath
            ArrayPool<byte>.Shared
            ValueNone
            (cancellationToken: CancellationToken)

    let run
        (roots: string array)
        (files: InputFile array)
        check
        noCache
        includeGenerated
        jobs
        cachePath
        (cancellationToken: CancellationToken)
        =
        runWithLengths
            roots
            files
            null
            check
            noCache
            includeGenerated
            jobs
            cachePath
            (cancellationToken: CancellationToken)
