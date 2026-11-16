namespace Csff.Cli

open System
open System.Buffers.Binary
open System.Collections.Generic
open System.IO
open System.Security.Cryptography
open System.Text
open Csff.Parser
open Csff.Printer

[<Struct; CustomEquality; CustomComparison>]
type internal CacheKey =
    {
        A: uint64
        B: uint64
        C: uint64
        D: uint64
        Width: int
        Indent: int
        Flags: int
    }

    member this.Equals(other: CacheKey) =
        this.A = other.A
        && this.B = other.B
        && this.C = other.C
        && this.D = other.D
        && this.Width = other.Width
        && this.Indent = other.Indent
        && this.Flags = other.Flags

    member this.CompareTo(other: CacheKey) =
        let c = this.A.CompareTo other.A

        if c <> 0 then
            c
        else
            let c = this.B.CompareTo other.B

            if c <> 0 then
                c
            else
                let c = this.C.CompareTo other.C

                if c <> 0 then
                    c
                else
                    let c = this.D.CompareTo other.D

                    if c <> 0 then
                        c
                    else
                        let c = this.Width.CompareTo other.Width

                        if c <> 0 then
                            c
                        else
                            let c = this.Indent.CompareTo other.Indent
                            if c <> 0 then c else this.Flags.CompareTo other.Flags

    override this.Equals(obj: obj) =
        match obj with
        | :? CacheKey as other -> this.Equals other
        | _ -> false

    override this.GetHashCode() =
        int this.A
        ^^^ int (this.A >>> 32)
        ^^^ (this.Width <<< 16)
        ^^^ (this.Indent <<< 8)
        ^^^ this.Flags

    interface IEquatable<CacheKey> with
        member this.Equals other = this.Equals other

    interface IComparable<CacheKey> with
        member this.CompareTo other = this.CompareTo other

    interface IComparable with
        member this.CompareTo obj =
            match obj with
            | :? CacheKey as other -> this.CompareTo other
            | null -> 1
            | _ -> invalidArg (nameof obj) "Object is not a CacheKey."

module internal Cache =
    [<Literal>]
    let MaximumEntries = 8192

    let private recordSize = 44

    let private header =
        let cliId = typeof<CacheKey>.Assembly.ManifestModule.ModuleVersionId
        let printerId = typeof<Printer>.Assembly.ManifestModule.ModuleVersionId
        let parserId = typeof<SyntaxTree>.Assembly.ManifestModule.ModuleVersionId
        let lexerId = typeof<Csff.Lexer.TokenBuffer>.Assembly.ManifestModule.ModuleVersionId

        let conformanceId =
            typeof<Csff.Conformance.SyntaxPreservation.Checker>
                .Assembly.ManifestModule.ModuleVersionId

        let version =
            "csff-cache-v1\n"
            + cliId.ToString()
            + "\n"
            + printerId.ToString()
            + "\n"
            + parserId.ToString()
            + "\n"
            + lexerId.ToString()
            + "\n"
            + conformanceId.ToString()
            + "\n"

        SHA256.HashData(Encoding.UTF8.GetBytes version)

    let key (digest: ReadOnlySpan<byte>) (settings: Settings) includeGenerated =
        let options = settings.Printer

        {
            A = BinaryPrimitives.ReadUInt64LittleEndian(digest)
            B = BinaryPrimitives.ReadUInt64LittleEndian(digest.Slice 8)
            C = BinaryPrimitives.ReadUInt64LittleEndian(digest.Slice 16)
            D = BinaryPrimitives.ReadUInt64LittleEndian(digest.Slice 24)
            Width = options.Width
            Indent = options.IndentSize
            Flags =
                (if options.UseTabs then 1 else 0)
                ||| (if options.EndOfLine = EndOfLine.CrLf then 2 else 0)
                ||| (if includeGenerated then 4 else 0)
                ||| (if settings.AutoEndOfLine then 8 else 0)
                ||| (if options.EndOfLine = EndOfLine.Cr then 16 else 0)
        }

    let pathWithSpellings (spellings: Discovery.Spellings) directory (root: string) =
        let identity = spellings.Identity root

        Path.Combine(
            spellings.Identity directory,
            Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes identity)) + ".cache"
        )

    let path directory root =
        pathWithSpellings (Discovery.Spellings()) directory root

    let read path =
        let entries = HashSet<CacheKey>()

        try
            use stream = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read)

            if stream.Length < 68L || stream.Length > int64 (68 + MaximumEntries * recordSize) then
                raise (InvalidDataException "Invalid cache size.")

            let bytes = Array.zeroCreate<byte>(int stream.Length)
            stream.ReadExactly bytes

            if not (bytes.AsSpan(0, 32).SequenceEqual header) then
                raise (InvalidDataException "Stale cache version.")

            let payload = ReadOnlySpan<byte>(bytes, 0, bytes.Length - 32)

            if
                not (
                    (SHA256.HashData payload)
                        .AsSpan()
                        .SequenceEqual(ReadOnlySpan<byte>(bytes, bytes.Length - 32, 32))
                )
            then
                raise (InvalidDataException "Invalid cache checksum.")

            let count = BinaryPrimitives.ReadInt32LittleEndian(ReadOnlySpan<byte>(bytes, 32, 4))

            if count < 0 || count > MaximumEntries || bytes.Length <> 68 + count * recordSize then
                raise (InvalidDataException "Invalid cache count.")

            for index = 0 to count - 1 do
                let record = ReadOnlySpan<byte>(bytes, 36 + index * recordSize, recordSize)

                let key =
                    {
                        A = BinaryPrimitives.ReadUInt64LittleEndian record
                        B = BinaryPrimitives.ReadUInt64LittleEndian(record.Slice 8)
                        C = BinaryPrimitives.ReadUInt64LittleEndian(record.Slice 16)
                        D = BinaryPrimitives.ReadUInt64LittleEndian(record.Slice 24)
                        Width = BinaryPrimitives.ReadInt32LittleEndian(record.Slice 32)
                        Indent = BinaryPrimitives.ReadInt32LittleEndian(record.Slice 36)
                        Flags = BinaryPrimitives.ReadInt32LittleEndian(record.Slice 40)
                    }

                if key.Width <= 0 || key.Indent <= 0 || key.Flags < 0 || key.Flags > 31 then
                    raise (InvalidDataException "Invalid cache options.")

                entries.Add key |> ignore
        with
        | :? IOException
        | :? InvalidDataException
        | :? UnauthorizedAccessException -> entries.Clear()

        entries

    let save (path: string) (previous: HashSet<CacheKey>) (current: HashSet<CacheKey>) =
        if current.Count > MaximumEntries then
            invalidArg (nameof current) "Formatting cache exceeds its entry limit."

        if not (previous.SetEquals current) then
            let bytes = Array.zeroCreate<byte>(68 + current.Count * recordSize)
            header.CopyTo(bytes, 0)
            BinaryPrimitives.WriteInt32LittleEndian(bytes.AsSpan(32), current.Count)
            let sorted = Array.zeroCreate<CacheKey> current.Count
            current.CopyTo sorted
            Array.Sort sorted

            for index = 0 to sorted.Length - 1 do
                let key = sorted[index]
                let record = bytes.AsSpan(36 + index * recordSize, recordSize)
                BinaryPrimitives.WriteUInt64LittleEndian(record, key.A)
                BinaryPrimitives.WriteUInt64LittleEndian(record.Slice 8, key.B)
                BinaryPrimitives.WriteUInt64LittleEndian(record.Slice 16, key.C)
                BinaryPrimitives.WriteUInt64LittleEndian(record.Slice 24, key.D)
                BinaryPrimitives.WriteInt32LittleEndian(record.Slice 32, key.Width)
                BinaryPrimitives.WriteInt32LittleEndian(record.Slice 36, key.Indent)
                BinaryPrimitives.WriteInt32LittleEndian(record.Slice 40, key.Flags)

            SHA256.HashData(bytes.AsSpan(0, bytes.Length - 32), bytes.AsSpan(bytes.Length - 32))
            |> ignore

            Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
            let pending = path + "." + Guid.NewGuid().ToString("N") + ".tmp"

            try
                do
                    use stream =
                        new FileStream(pending, FileMode.Create, FileAccess.Write, FileShare.None)

                    stream.Write bytes

                File.Move(pending, path, true)
            finally
                if File.Exists pending then
                    File.Delete pending
