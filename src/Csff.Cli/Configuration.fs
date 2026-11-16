namespace Csff.Cli

open System
open System.Collections.Generic
open System.Globalization
open System.IO
open System.Text
open System.Text.Json
open System.Text.RegularExpressions
open Csff.Printer

[<Struct>]
type internal Settings =
    {
        Printer: PrinterOptions
        AutoEndOfLine: bool
    }

    static member Default =
        {
            Printer = PrinterOptions.Default
            AutoEndOfLine = true
        }

[<NoEquality; NoComparison>]
type internal Config =
    {
        Directory: string
        Settings: Settings
        Overrides: (Regex * FastGlob * Settings) array
    }

[<NoEquality; NoComparison>]
type internal EditorSection =
    {
        Directory: string
        mutable Regex: Regex
        Fast: FastGlob
        CanMatchCs: bool
        AlwaysMatchesCs: bool
        Values: (string * string) array
    }

    member this.Pattern = Glob.ensureRegex &this.Regex this.Fast

[<NoEquality; NoComparison>]
type internal EditorGroup =
    {
        Sections: EditorSection array
        Parent: EditorGroup option
    }

module internal Configuration =
    let yamlJson (path: string) (content: string) =
        let documents = Yaml.parse path content
        use bytes = new MemoryStream()
        use writer = new Utf8JsonWriter(bytes)
        let mutable nodes = 0

        let tagged (tag: string) standard =
            if tag.Length > 0 && tag <> standard then
                invalidArg "config" ("Unsupported YAML tag: " + tag)

        let rec write depth (node: YamlNode) =
            if depth > 64 then
                invalidArg "config" "YAML configuration nesting exceeds 64 levels."

            nodes <- nodes + 1

            if nodes > 100000 then
                invalidArg "config" "YAML configuration expands to more than 100000 nodes."

            match node with
            | YamlNode.Mapping(tag, entries) ->
                tagged tag "tag:yaml.org,2002:map"
                writer.WriteStartObject()

                for key, value in entries do
                    match key with
                    | YamlNode.Scalar(keyTag, name, _) ->
                        tagged keyTag "tag:yaml.org,2002:str"
                        writer.WritePropertyName name
                    | _ -> invalidArg "config" "YAML configuration keys must be scalars."

                    write (depth + 1) value

                writer.WriteEndObject()
            | YamlNode.Sequence(tag, items) ->
                tagged tag "tag:yaml.org,2002:seq"
                writer.WriteStartArray()

                for item in items do
                    write (depth + 1) item

                writer.WriteEndArray()
            | YamlNode.Scalar(tag, value, style) ->
                let quoted = style <> YamlStyle.Plain

                if tag = "tag:yaml.org,2002:str" || (quoted && tag.Length = 0) then
                    writer.WriteStringValue value
                elif tag = "tag:yaml.org,2002:bool" then
                    match value.Trim().ToLowerInvariant() with
                    | "true"
                    | "y"
                    | "yes"
                    | "on" -> writer.WriteBooleanValue true
                    | "false"
                    | "n"
                    | "no"
                    | "off" -> writer.WriteBooleanValue false
                    | _ -> invalidArg "config" "Invalid YAML Boolean."
                elif tag = "tag:yaml.org,2002:int" then
                    let number = value.Trim().Replace("_", "")
                    let negative = number.StartsWith('-')

                    let unsigned =
                        if negative || number.StartsWith('+') then
                            number.Substring(1)
                        else
                            number

                    let magnitude =
                        if unsigned.StartsWith("0x", StringComparison.OrdinalIgnoreCase) then
                            Convert.ToUInt64(unsigned.Substring(2), 16)
                        elif unsigned.StartsWith("0b", StringComparison.Ordinal) then
                            Convert.ToUInt64(unsigned.Substring(2), 2)
                        elif unsigned.Length > 1 && unsigned[0] = '0' then
                            Convert.ToUInt64(unsigned.Substring(1), 8)
                        else
                            unsigned.Split(':')
                            |> Array.fold
                                (fun total group ->
                                    Checked.(+)
                                        (Checked.(*) total 60UL)
                                        (UInt64.Parse(
                                            group,
                                            NumberStyles.None,
                                            CultureInfo.InvariantCulture
                                        )))
                                0UL

                    if negative && magnitude <= 9223372036854775808UL then
                        writer.WriteNumberValue(
                            if magnitude = 0UL then
                                0L
                            else
                                -(int64 (magnitude - 1UL)) - 1L
                        )
                    elif not negative && magnitude <= uint64 Int64.MaxValue then
                        writer.WriteNumberValue(int64 magnitude)
                    else
                        invalidArg "config" "YAML integer out of range."
                elif tag = "tag:yaml.org,2002:float" then
                    match
                        Double.TryParse(
                            value.Replace("_", ""),
                            NumberStyles.Float,
                            CultureInfo.InvariantCulture
                        )
                    with
                    | true, number when Double.IsFinite number -> writer.WriteNumberValue number
                    | _ -> invalidArg "config" "Invalid YAML float."
                elif tag = "tag:yaml.org,2002:null" then
                    match value.Trim() with
                    | ""
                    | "~"
                    | "null"
                    | "Null"
                    | "NULL" -> writer.WriteNullValue()
                    | _ -> invalidArg "config" "Invalid YAML null."
                elif tag.Length > 0 then
                    invalidArg "config" ("Unsupported YAML tag: " + tag)
                elif
                    String.IsNullOrEmpty value
                    || value = "~"
                    || value = "null"
                    || value = "Null"
                    || value = "NULL"
                then
                    writer.WriteNullValue()
                elif value = "true" || value = "True" || value = "TRUE" then
                    writer.WriteBooleanValue true
                elif value = "false" || value = "False" || value = "FALSE" then
                    writer.WriteBooleanValue false
                else
                    let hex = value.StartsWith("0x", StringComparison.OrdinalIgnoreCase)
                    let number = if hex then value.Substring(2) else value

                    let style =
                        if hex then
                            NumberStyles.AllowHexSpecifier
                        else
                            NumberStyles.Integer

                    match Int64.TryParse(number, style, CultureInfo.InvariantCulture) with
                    | true, number when not hex -> writer.WriteNumberValue number
                    | _ ->
                        match UInt64.TryParse(number, style, CultureInfo.InvariantCulture) with
                        | true, number -> writer.WriteNumberValue number
                        | _ ->
                            match
                                Double.TryParse(
                                    value,
                                    NumberStyles.Float,
                                    CultureInfo.InvariantCulture
                                )
                            with
                            | true, number when Double.IsFinite number ->
                                writer.WriteNumberValue number
                            | _ -> writer.WriteStringValue value

        if documents.Length = 0 then
            writer.WriteStartObject()
            writer.WriteEndObject()
        elif documents.Length > 1 then
            invalidArg "config" "A YAML configuration must hold a single document."
        else
            write 0 documents[0]

        writer.Flush()
        Encoding.UTF8.GetString(bytes.ToArray())

    let private positive name value =
        if value <= 0 then
            invalidArg name (name + " must be positive.")

        value

    let private eol (value: string) (settings: Settings) =
        match value.ToLowerInvariant() with
        | "auto" ->
            { settings with
                AutoEndOfLine = true
                Printer =
                    { settings.Printer with
                        EndOfLine = EndOfLine.Lf
                    }
            }
        | "lf" ->
            { settings with
                AutoEndOfLine = false
                Printer =
                    { settings.Printer with
                        EndOfLine = EndOfLine.Lf
                    }
            }
        | "crlf" ->
            { settings with
                AutoEndOfLine = false
                Printer =
                    { settings.Printer with
                        EndOfLine = EndOfLine.CrLf
                    }
            }
        | "cr" ->
            { settings with
                AutoEndOfLine = false
                Printer =
                    { settings.Printer with
                        EndOfLine = EndOfLine.Cr
                    }
            }
        | _ -> invalidArg "endOfLine" "endOfLine must be auto, lf, crlf or cr."

    let private stringSetting name (element: JsonElement) =
        if element.ValueKind <> JsonValueKind.String then
            invalidArg "config" (name + " must be a string.")

        element.GetString()

    let private tryGetPropertyIgnoreCase
        (element: JsonElement)
        (name: string)
        (value: outref<JsonElement>)
        =
        let mutable found = false

        for property in element.EnumerateObject() do
            if not found && property.Name.Equals(name, StringComparison.OrdinalIgnoreCase) then
                value <- property.Value
                found <- true

        found

    let private jsonSettings (start: Settings) (element: JsonElement) =
        if element.ValueKind <> JsonValueKind.Object then
            invalidArg "config" "A csff configuration must be an object."

        let mutable settings = start

        for property in element.EnumerateObject() do
            match property.Name.ToLowerInvariant() with
            | "printwidth" ->
                settings <-
                    { settings with
                        Printer =
                            { settings.Printer with
                                Width = positive "printWidth" (property.Value.GetInt32())
                            }
                    }
            | "indentsize" ->
                settings <-
                    { settings with
                        Printer =
                            { settings.Printer with
                                IndentSize = positive "indentSize" (property.Value.GetInt32())
                            }
                    }
            | "usetabs" ->
                settings <-
                    { settings with
                        Printer =
                            { settings.Printer with
                                UseTabs = property.Value.GetBoolean()
                            }
                    }
            | "endofline" -> settings <- eol (stringSetting "endOfLine" property.Value) settings
            | "overrides"
            | "files"
            | "formatter"
            | "xmlwhitespacesensitivity" -> ()
            | name -> invalidArg "config" ("Unknown csff setting: " + name)

        settings

    let read path =
        let content = File.ReadAllText path

        let json =
            if String.IsNullOrWhiteSpace content then
                "{}"
            elif content.TrimStart().StartsWith('{') then
                try
                    use document = JsonDocument.Parse content
                    document.RootElement |> ignore
                    content
                with :? JsonException ->
                    yamlJson path content
            else
                yamlJson path content

        use document = JsonDocument.Parse json
        let root = document.RootElement
        let pending = Stack<JsonElement>()
        pending.Push root

        while pending.Count > 0 do
            let item = pending.Pop()

            if item.ValueKind = JsonValueKind.Object then
                let names = HashSet<string>(StringComparer.OrdinalIgnoreCase)

                for property in item.EnumerateObject() do
                    if not (names.Add property.Name) then
                        invalidArg "config" ("Duplicate configuration key " + property.Name + ".")

                    pending.Push property.Value
            elif item.ValueKind = JsonValueKind.Array then
                for value in item.EnumerateArray() do
                    pending.Push value

        let settings = jsonSettings Settings.Default root
        let overrides = ResizeArray<Regex * FastGlob * Settings>()

        for property in root.EnumerateObject() do
            if property.Name.Equals("overrides", StringComparison.OrdinalIgnoreCase) then
                if property.Value.ValueKind <> JsonValueKind.Array then
                    invalidArg "config" "overrides must be an array."

                for item in property.Value.EnumerateArray() do
                    if item.ValueKind <> JsonValueKind.Object then
                        invalidArg "config" "overrides must contain objects."

                    let mutable files = Unchecked.defaultof<JsonElement>

                    if not (tryGetPropertyIgnoreCase item "files" &files) then
                        invalidArg "config" "Each override requires a files pattern."

                    let pattern = stringSetting "overrides.files" files
                    let mutable formatter = Unchecked.defaultof<JsonElement>

                    if
                        tryGetPropertyIgnoreCase item "formatter" &formatter
                        && not (
                            (stringSetting "overrides.formatter" formatter)
                                .Equals("csharp", StringComparison.OrdinalIgnoreCase)
                        )
                    then
                        invalidArg "config" "csff overrides support only the csharp formatter."

                    let regex, fast = Glob.filePatternWithFast pattern
                    overrides.Add(regex, fast, jsonSettings settings item)

        {
            Directory = Path.GetDirectoryName(Path.GetFullPath path)
            Settings = settings
            Overrides = overrides.ToArray()
        }

    let find directory =
        [ ".csffrc.json"; ".csffrc.yaml"; ".csffrc.yml" ]
        |> List.tryPick (fun name ->
            let path = Path.Combine(directory, name)
            if File.Exists path then Some(read path) else None)

    let forFile (config: Config option) path =
        match config with
        | None -> Settings.Default
        | Some config ->
            let overrides = config.Overrides

            if overrides.Length = 0 then
                config.Settings
            else
                let relative =
                    match Glob.relative config.Directory path with
                    | Some rel -> rel
                    | None -> Path.GetRelativePath(config.Directory, path) |> Glob.normalize

                let newline = Glob.hasNewline relative
                let mutable index = overrides.Length - 1
                let mutable matched = ValueNone

                while matched.IsNone && index >= 0 do
                    let pattern, fast, settings = overrides[index]
                    let mutable rx = pattern

                    if Glob.isMatchScanned newline fast &rx relative then
                        matched <- ValueSome settings

                    index <- index - 1

                match matched with
                | ValueSome settings -> settings
                | ValueNone -> config.Settings

    let private isRelevantEditorKey (name: string) =
        name = "indent_style"
        || name = "indent_size"
        || name = "tab_width"
        || name = "max_line_length"
        || name = "end_of_line"
        || name = "csff_formatter"

    let readEditor directory =
        let path = Path.Combine(directory, ".editorconfig")
        let sections = ResizeArray<EditorSection>()
        let values = ResizeArray<string * string>()
        let mutable rawPattern: string = null
        let mutable root = false

        let flush () =
            if not (isNull rawPattern) && values.Count > 0 then
                let regex, fast = Glob.editorConfigPatternWithFast rawPattern
                let canMatchCs = Glob.canMatchLowercaseCs fast

                sections.Add
                    {
                        Directory = directory
                        Regex = regex
                        Fast = fast
                        CanMatchCs = canMatchCs
                        AlwaysMatchesCs = canMatchCs && Glob.alwaysMatchesLowercaseCs fast
                        Values = values.ToArray()
                    }

            values.Clear()

        let trySectionHeader (text: string) =
            let mutable i = 1
            let mutable escaped = false
            let mutable inClass = false
            let mutable classFirst = -1
            let mutable braces = 0
            let mutable result: string = null

            while isNull result && i < text.Length do
                let ch = text[i]

                if escaped then
                    escaped <- false
                elif ch = '\\' then
                    escaped <- true
                elif inClass then
                    if ch = ']' && i > classFirst then
                        inClass <- false
                elif ch = '[' then
                    inClass <- true

                    let negated = i + 1 < text.Length && (text[i + 1] = '!' || text[i + 1] = '^')

                    classFirst <- if negated then i + 2 else i + 1
                elif ch = '{' then
                    braces <- braces + 1
                elif ch = '}' && braces > 0 then
                    braces <- braces - 1
                elif ch = ']' && braces = 0 then
                    let after = text.AsSpan(i + 1)

                    if after.IsEmpty then
                        result <- text.Substring(1, i - 1)
                    elif Char.IsWhiteSpace after[0] then
                        let suffix = after.TrimStart()

                        if suffix.IsEmpty || suffix[0] = '#' || suffix[0] = ';' then
                            result <- text.Substring(1, i - 1)

                i <- i + 1

            result

        let mutable seenSection = false

        if File.Exists path then
            for line in File.ReadAllLines path do
                let text = line.Trim()

                if text.Length > 0 && not (text.StartsWith('#') || text.StartsWith(';')) then
                    if text.StartsWith('[') then
                        flush ()
                        seenSection <- true
                        rawPattern <- trySectionHeader text
                    else
                        let separator = text.IndexOf('=')

                        if separator > 0 then
                            let name = text.Substring(0, separator).Trim().ToLowerInvariant()

                            if not seenSection && name = "root" then
                                let value = text.Substring(separator + 1).Trim().ToLowerInvariant()
                                root <- value = "true"
                            elif not (isNull rawPattern) && isRelevantEditorKey name then
                                let value = text.Substring(separator + 1).Trim().ToLowerInvariant()
                                values.Add(name, value)

            flush ()

        root, sections.ToArray()

    let private editorWithSections groups (path: string) (segOffset: int) =
        let mutable indentStyle: string = null
        let mutable indentSize: string = null
        let mutable tabWidth: string = null
        let mutable maxLineLength: string = null
        let mutable endOfLine: string = null
        let mutable csffFormatter: string = null
        let isLowerCs = path.EndsWith(".cs", StringComparison.Ordinal)
        let sep = Path.DirectorySeparatorChar

        let rec apply =
            function
            | None -> ()
            | Some group ->
                apply group.Parent

                let dir = group.Sections[0].Directory

                if
                    segOffset > 0
                    && dir.Length > 1
                    && dir[dir.Length - 1] <> sep
                    && path.Length > dir.Length + 1
                    && path[dir.Length] = sep
                    && path.StartsWith(dir, StringComparison.Ordinal)
                then
                    let relSpan = path.AsSpan(dir.Length + 1)
                    let segSpan = path.AsSpan(segOffset)

                    for section in group.Sections do
                        if
                            section.Values.Length > 0
                            && (not isLowerCs || section.CanMatchCs)
                            && (if isLowerCs && section.AlwaysMatchesCs then
                                    true
                                else
                                    Glob.isMatchSpan section.Fast &section.Regex relSpan segSpan)
                        then
                            for name, value in section.Values do
                                let stored = if value = "unset" then null else value

                                match name with
                                | "indent_style" -> indentStyle <- stored
                                | "indent_size" -> indentSize <- stored
                                | "tab_width" -> tabWidth <- stored
                                | "max_line_length" -> maxLineLength <- stored
                                | "end_of_line" -> endOfLine <- stored
                                | "csff_formatter" -> csffFormatter <- stored
                                | _ -> ()
                else
                    match Glob.relative dir path with
                    | Some relative ->
                        let newline = Glob.hasNewline relative
                        let filterCs = isLowerCs && not newline

                        for section in group.Sections do
                            if
                                section.Values.Length > 0
                                && (not filterCs || section.CanMatchCs)
                                && (if filterCs && section.AlwaysMatchesCs then
                                        true
                                    else
                                        Glob.isMatchScanned
                                            newline
                                            section.Fast
                                            &section.Regex
                                            relative)
                            then
                                for name, value in section.Values do
                                    let stored = if value = "unset" then null else value

                                    match name with
                                    | "indent_style" -> indentStyle <- stored
                                    | "indent_size" -> indentSize <- stored
                                    | "tab_width" -> tabWidth <- stored
                                    | "max_line_length" -> maxLineLength <- stored
                                    | "end_of_line" -> endOfLine <- stored
                                    | "csff_formatter" -> csffFormatter <- stored
                                    | _ -> ()
                    | None -> ()

        apply groups

        if not (isNull csffFormatter) && csffFormatter <> "csharp" then
            None
        else
            let parsePositive (text: string) =
                if isNull text then
                    ValueNone
                else
                    match Int32.TryParse text with
                    | true, number when number > 0 -> ValueSome number
                    | _ -> ValueNone

            let tabs = indentStyle = "tab"
            let parsedTabWidth = parsePositive tabWidth

            let parsedIndentSize =
                if indentSize = "tab" then
                    parsedTabWidth
                else
                    parsePositive indentSize

            let indent =
                if tabs then
                    match parsedTabWidth with
                    | ValueSome width -> width
                    | ValueNone ->
                        match parsedIndentSize with
                        | ValueSome size -> size
                        | ValueNone -> 4
                else
                    match parsedIndentSize with
                    | ValueSome size -> size
                    | ValueNone -> 4

            let width =
                match parsePositive maxLineLength with
                | ValueSome w -> w
                | ValueNone -> 100

            let settings =
                { Settings.Default with
                    Printer =
                        { PrinterOptions.Default with
                            Width = width
                            IndentSize = indent
                            UseTabs = tabs
                        }
                }

            let settings =
                match endOfLine with
                | "auto"
                | "lf"
                | "crlf"
                | "cr" -> eol endOfLine settings
                | _ -> settings

            Some settings

    let editorForFile groups path =
        match groups with
        | None -> Some Settings.Default
        | Some _ -> editorWithSections groups path 0

    let editorForCanonicalFile groups path segOffset =
        match groups with
        | None -> Some Settings.Default
        | Some _ -> editorWithSections groups path segOffset

    let tryUniformCsSettings (groups: EditorGroup option) (directory: string) =
        let probeSuffix =
            if Path.DirectorySeparatorChar = '\\' then
                "\\_.cs"
            else
                "/_.cs"

        let rec isUniform =
            function
            | None -> true
            | Some group ->
                let dir = group.Sections[0].Directory

                let dirOk =
                    (String.Equals(dir, directory, StringComparison.Ordinal)
                     && Glob.isCanonicalChildPath dir (directory + probeSuffix))
                    || Glob.isCanonicalChildPath dir directory

                if not dirOk then
                    false
                else
                    let mutable ok = true
                    let mutable i = 0

                    while ok && i < group.Sections.Length do
                        let s = group.Sections[i]

                        if s.Values.Length > 0 && s.CanMatchCs && not s.AlwaysMatchesCs then
                            ok <- false

                        i <- i + 1

                    ok && isUniform group.Parent

        match groups with
        | None -> ValueSome(Some Settings.Default)
        | Some _ when not (Glob.hasNewline directory) && isUniform groups ->
            ValueSome(editorWithSections groups (directory + probeSuffix) (directory.Length + 1))
        | _ -> ValueNone
