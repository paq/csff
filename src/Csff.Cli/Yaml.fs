namespace Csff.Cli

open System
open System.Collections.Generic
open System.Text

[<RequireQualifiedAccess>]
type internal YamlStyle =
    | Plain
    | SingleQuoted
    | DoubleQuoted
    | Literal
    | Folded

[<RequireQualifiedAccess>]
type internal YamlNode =
    | Scalar of tag: string * value: string * style: YamlStyle
    | Sequence of tag: string * items: YamlNode array
    | Mapping of tag: string * entries: (YamlNode * YamlNode) array

module internal Yaml =
    type private Node(position: int) =
        member _.Position = position
        member val Tag = "" with get, set
        member val Value = Atom("", YamlStyle.Plain) with get, set

    and [<NoComparison>] private Value =
        | Atom of string * YamlStyle
        | Items of Node array
        | Pairs of (Node * Node) array
        | Alias of string * Node option

    type private Reader(path: string, input: string) =
        let text = input.Replace("\r\n", "\n").Replace('\r', '\n').Replace('\u0085', '\n')
        let starts = ResizeArray<int>()
        let anchors = Dictionary<string, Node>(StringComparer.Ordinal)
        let handles = Dictionary<string, string>(StringComparer.Ordinal)
        let declaredHandles = HashSet<string>(StringComparer.Ordinal)
        let mutable cursor = 0

        do
            starts.Add(if text.StartsWith('\ufeff') then 1 else 0)

            for index = 0 to text.Length - 1 do
                if text[index] = '\n' then
                    starts.Add(index + 1)

        let fail position message =
            let mutable low = 0
            let mutable high = starts.Count - 1

            while low < high do
                let middle = (low + high + 1) / 2

                if starts[middle] <= position then
                    low <- middle
                else
                    high <- middle - 1

            raise (FormatException($"{path}:{low + 1}:{position - starts[low] + 1}: {message}"))

        let peek () =
            if cursor < text.Length then text[cursor] else '\000'

        let blank c = c = ' ' || c = '\t'
        let separator c = blank c || c = '\n' || c = '\000'
        let flowEnd c = c = ',' || c = ']' || c = '}'

        let decodeTag position (value: string) =
            let mutable index = 0

            while index < value.Length do
                if value[index] = '%' then
                    if
                        index + 2 >= value.Length
                        || not (Char.IsAsciiHexDigit value[index + 1])
                        || not (Char.IsAsciiHexDigit value[index + 2])
                    then
                        fail position "Invalid YAML tag escape"

                    index <- index + 3
                else
                    index <- index + 1

            try
                Uri.UnescapeDataString value
            with :? UriFormatException ->
                fail position "Invalid YAML tag escape"

        let lineStart position =
            let mutable low = 0
            let mutable high = starts.Count - 1

            while low < high do
                let middle = (low + high + 1) / 2

                if starts[middle] <= position then
                    low <- middle
                else
                    high <- middle - 1

            starts[low]

        let column position = position - lineStart position

        let lineEnd (position: int) =
            let finish = text.IndexOf('\n', position)
            if finish < 0 then text.Length else finish

        let skipSpaces () =
            while blank (peek ()) do
                cursor <- cursor + 1

        let skipComment () =
            if peek () = '#' then
                cursor <- lineEnd cursor

        let skipTrivia () =
            let mutable more = true

            while more do
                skipSpaces ()
                skipComment ()

                if peek () = '\n' then
                    cursor <- cursor + 1
                else
                    more <- false

        let marker (value: string) =
            column cursor = 0
            && cursor + 3 <= text.Length
            && text.AsSpan(cursor, 3).SequenceEqual(value.AsSpan())
            && (cursor + 3 = text.Length || separator text[cursor + 3])

        let indicator c =
            peek () = c && (cursor + 1 = text.Length || separator text[cursor + 1])

        let colon flow =
            peek () = ':'
            && (cursor + 1 = text.Length
                || separator text[cursor + 1]
                || (flow
                    && (flowEnd text[cursor + 1] || text[cursor + 1] = '[' || text[cursor + 1] = '{')))

        let empty position = Node(position)

        let reset () =
            anchors.Clear()
            handles.Clear()
            declaredHandles.Clear()
            handles["!"] <- "!"
            handles["!!"] <- "tag:yaml.org,2002:"

        let foldBreaks count =
            if count = 1 then " " else String('\n', count - 1)

        member private _.Quoted(parent: int) =
            let position = cursor
            let quote = peek ()
            cursor <- cursor + 1
            let result = StringBuilder()
            let mutable closed = false
            let mutable literalSpaces = 0

            let unicode digits escapePosition =
                if cursor + digits > text.Length then
                    fail escapePosition "Invalid Unicode escape in a double-quoted YAML string"

                let mutable number = 0u

                for offset = 0 to digits - 1 do
                    let c = text[cursor + offset]

                    let digit =
                        if c >= '0' && c <= '9' then
                            int c - int '0'
                        elif c >= 'a' && c <= 'f' then
                            int c - int 'a' + 10
                        elif c >= 'A' && c <= 'F' then
                            int c - int 'A' + 10
                        else
                            fail
                                escapePosition
                                "Invalid Unicode escape in a double-quoted YAML string"

                    number <- number * 16u + uint32 digit

                cursor <- cursor + digits
                number

            let breaks escaped =
                let mutable count = 0
                literalSpaces <- 0

                while peek () = '\n' do
                    cursor <- cursor + 1
                    count <- count + 1
                    skipSpaces ()

                if cursor < text.Length && column cursor <= parent then
                    fail cursor "Unexpected indentation in a quoted YAML string"

                if escaped then
                    if count > 1 then
                        result.Append(String('\n', count - 1)) |> ignore
                else
                    result.Append(foldBreaks count) |> ignore

            while not closed do
                match peek () with
                | '\000' -> fail position "Unterminated quoted YAML string"
                | c when c = quote ->
                    cursor <- cursor + 1

                    if quote = '\'' && peek () = '\'' then
                        result.Append('\'') |> ignore
                        literalSpaces <- 0
                        cursor <- cursor + 1
                    else
                        closed <- true
                | '\n' ->
                    result.Length <- result.Length - literalSpaces
                    breaks false
                | '\\' when quote = '"' ->
                    literalSpaces <- 0
                    let escapePosition = cursor
                    cursor <- cursor + 1
                    let code = peek ()
                    cursor <- cursor + 1

                    match code with
                    | '\n' ->
                        cursor <- cursor - 1
                        breaks true
                    | 'x'
                    | 'u'
                    | 'U' ->
                        let digits =
                            if code = 'x' then 2
                            elif code = 'u' then 4
                            else 8

                        let number = unicode digits escapePosition

                        if number >= 0xd800u && number <= 0xdbffu then
                            if
                                peek () <> '\\'
                                || cursor + 1 >= text.Length
                                || (text[cursor + 1] <> 'u' && text[cursor + 1] <> 'U')
                            then
                                fail
                                    escapePosition
                                    "Invalid surrogate escape in a double-quoted YAML string"

                            let lowDigits = if text[cursor + 1] = 'u' then 4 else 8
                            cursor <- cursor + 2
                            let low = unicode lowDigits escapePosition

                            if low < 0xdc00u || low > 0xdfffu then
                                fail
                                    escapePosition
                                    "Invalid surrogate escape in a double-quoted YAML string"

                            result.Append(
                                Char.ConvertFromUtf32(
                                    int (0x10000u + (number - 0xd800u) * 0x400u + low - 0xdc00u)
                                )
                            )
                            |> ignore
                        elif number >= 0xdc00u && number <= 0xdfffu then
                            fail
                                escapePosition
                                "Invalid surrogate escape in a double-quoted YAML string"
                        elif code <> 'U' then
                            result.Append(char number) |> ignore
                        elif
                            number <= 0x10ffffu && not (number >= 0xd800u && number <= 0xdfffu)
                        then
                            result.Append(Char.ConvertFromUtf32(int number)) |> ignore
                        else
                            fail
                                escapePosition
                                "Invalid Unicode escape in a double-quoted YAML string"
                    | _ ->
                        let decoded =
                            match code with
                            | '0' -> '\000'
                            | 'a' -> '\007'
                            | 'b' -> '\b'
                            | 't'
                            | '\t' -> '\t'
                            | 'n' -> '\n'
                            | 'v' -> '\011'
                            | 'f' -> '\012'
                            | 'r' -> '\r'
                            | 'e' -> '\027'
                            | ' ' -> ' '
                            | '"' -> '"'
                            | '/' -> '/'
                            | '\\' -> '\\'
                            | 'N' -> '\u0085'
                            | '_' -> '\u00a0'
                            | 'L' -> '\u2028'
                            | 'P' -> '\u2029'
                            | _ ->
                                fail
                                    escapePosition
                                    "Unknown escape sequence in a double-quoted YAML string"

                        result.Append decoded |> ignore
                | c ->
                    result.Append c |> ignore
                    literalSpaces <- if blank c then literalSpaces + 1 else 0
                    cursor <- cursor + 1

            result.ToString(),
            (if quote = '\'' then
                 YamlStyle.SingleQuoted
             else
                 YamlStyle.DoubleQuoted)

        member private _.Plain(parent: int, flow: bool) =
            let result = StringBuilder()
            let mutable scanning = true

            while scanning do
                let start = cursor

                while (cursor < text.Length
                       && peek () <> '\n'
                       && not (flow && flowEnd (peek ()))
                       && not (colon flow)
                       && not (peek () = '#' && (cursor = start || blank text[cursor - 1]))) do
                    cursor <- cursor + 1

                result.Append(text.Substring(start, cursor - start).TrimEnd(' ', '\t'))
                |> ignore

                if peek () = '\n' || peek () = '#' then
                    let saved = cursor
                    let hadComment = peek () = '#'
                    skipComment ()
                    let mutable breaks = 0

                    while peek () = '\n' do
                        cursor <- cursor + 1
                        breaks <- breaks + 1
                        skipSpaces ()

                    if
                        cursor < text.Length
                        && not hadComment
                        && not (marker "---" || marker "...")
                        && (flow || column cursor > parent)
                        && not (flow && (flowEnd (peek ()) || peek () = ':'))
                        && peek () <> '#'
                    then
                        result.Append(foldBreaks breaks) |> ignore
                    elif flow && hadComment && peek () = ':' then
                        scanning <- false
                    else
                        cursor <- saved
                        scanning <- false
                else
                    scanning <- false

            result.ToString()

        member private _.Properties(flow: bool) =
            let mutable tag = ""
            let mutable anchor = None
            let mutable reading = true

            while reading do
                let position = cursor

                match peek () with
                | '&' ->
                    if anchor.IsSome then
                        fail position "A YAML node can have only one anchor"

                    cursor <- cursor + 1
                    let start = cursor

                    while not (separator (peek ()) || flowEnd (peek ())) do
                        if peek () = '[' || peek () = '{' then
                            fail cursor "A YAML anchor name cannot contain a flow opener"

                        cursor <- cursor + 1

                    if cursor = start then
                        fail position "A YAML anchor needs a name"

                    anchor <- Some(text.Substring(start, cursor - start))
                | '!' ->
                    if tag <> "" then
                        fail position "A YAML node can have only one tag"

                    cursor <- cursor + 1

                    if peek () = '<' then
                        cursor <- cursor + 1
                        let start = cursor

                        while peek () <> '>' && not (separator (peek ())) do
                            cursor <- cursor + 1

                        if peek () <> '>' then
                            fail position "Unterminated YAML tag"

                        tag <- decodeTag position (text.Substring(start, cursor - start))
                        cursor <- cursor + 1
                    else
                        let start = position

                        while not (separator (peek ())) && not (flow && flowEnd (peek ())) do
                            cursor <- cursor + 1

                        let spelling = text.Substring(start, cursor - start)
                        let last = spelling.LastIndexOf('!')

                        let handle, suffix =
                            if last > 0 then
                                spelling.Substring(0, last + 1), spelling.Substring(last + 1)
                            else
                                "!", spelling.Substring(1)

                        match handles.TryGetValue handle with
                        | true, prefix -> tag <- prefix + decodeTag position suffix
                        | _ -> fail position ("Undefined YAML tag handle " + handle)

                        if spelling.IndexOfAny([| '['; ']'; '{'; '}'; ',' |]) >= 0 then
                            fail position ("Invalid YAML tag " + tag)
                | _ -> reading <- false

                if reading then
                    if flow then skipTrivia () else skipSpaces ()

            tag, anchor

        member private _.BlockScalar(parent: int) =
            let folded = peek () = '>'
            let header = cursor
            cursor <- cursor + 1
            let mutable chomp = ' '
            let mutable explicitIndent = 0

            while peek () = '+' || peek () = '-' || (peek () >= '1' && peek () <= '9') do
                if peek () = '+' || peek () = '-' then
                    if chomp <> ' ' then
                        fail cursor "Invalid YAML block scalar header"

                    chomp <- peek ()
                else
                    if explicitIndent <> 0 then
                        fail cursor "Invalid YAML block scalar header"

                    explicitIndent <- int (peek ()) - int '0'

                cursor <- cursor + 1

            skipSpaces ()
            skipComment ()

            if peek () <> '\n' && cursor < text.Length then
                fail header "Invalid YAML block scalar header"

            if peek () = '\n' then
                cursor <- cursor + 1

            let lines = ResizeArray<string * bool>()

            let mutable indent =
                if explicitIndent = 0 then
                    -1
                else
                    max 0 parent + explicitIndent

            let mutable leadingSpaces = 0
            let mutable reading = true

            while reading && cursor < text.Length do
                let start = cursor
                let finish = lineEnd start
                let mutable first = start

                while first < finish && text[first] = ' ' do
                    first <- first + 1

                let spaces = first - start
                let isEmpty = first = finish

                if not isEmpty && indent < 0 then
                    if spaces <= parent && not (parent < 0 && spaces = 0) then
                        reading <- false
                    elif leadingSpaces > spaces then
                        fail first "The first line of a YAML literal block has extra spaces"
                    else
                        indent <- spaces

                if
                    reading
                    && not isEmpty
                    && (spaces < indent || (spaces = 0 && (marker "---" || marker "...")))
                then
                    reading <- false

                if reading then
                    if indent < 0 then
                        leadingSpaces <- max leadingSpaces spaces

                    let offset = if indent < 0 then finish else min finish (start + indent)
                    lines.Add(text.Substring(offset, finish - offset), finish < text.Length)
                    cursor <- if finish < text.Length then finish + 1 else finish

            let result = StringBuilder()
            let mutable lastContent = lines.Count - 1

            while lastContent >= 0 && fst lines[lastContent] = "" do
                lastContent <- lastContent - 1

            for index = 0 to lines.Count - 1 do
                let value, terminated = lines[index]
                result.Append value |> ignore

                if terminated then
                    let next = if index + 1 < lines.Count then fst lines[index + 1] else ""
                    let moreIndented (s: string) = s.Length > 0 && blank s[0]
                    let mutable afterEmpty = index + 1

                    if value.Length > 0 && next.Length = 0 then
                        while afterEmpty < lines.Count && (fst lines[afterEmpty]).Length = 0 do
                            afterEmpty <- afterEmpty + 1

                    let beforeIndented =
                        value.Length > 0
                        && next.Length = 0
                        && afterEmpty < lines.Count
                        && moreIndented (fst lines[afterEmpty])

                    if
                        not folded
                        || index >= lastContent
                        || moreIndented value
                        || moreIndented next
                        || beforeIndented
                    then
                        result.Append('\n') |> ignore
                    elif value <> "" && next <> "" then
                        result.Append(' ') |> ignore
                    elif value = "" then
                        result.Append('\n') |> ignore

            let value = result.ToString()
            let stripped = value.TrimEnd('\n')

            let value =
                if chomp = '+' then value
                elif chomp = '-' then stripped
                elif value.EndsWith('\n') then stripped + "\n"
                else stripped

            value, (if folded then YamlStyle.Folded else YamlStyle.Literal)

        member private this.Node
            (
                parent: int,
                flow: bool,
                allowMapping: bool,
                depth: int,
                keyMode: bool,
                ?indentless: bool,
                ?compact: bool,
                ?inheritedProperties: bool * bool
            ) : Node =
            let position = cursor

            if depth >= 256 then
                fail position "YAML nesting exceeds 256 levels"

            let mutable node = Node(position)
            let tag, anchor = this.Properties flow
            let inheritedTag, inheritedAnchor = defaultArg inheritedProperties (false, false)
            let duplicateTag = inheritedTag && tag <> ""
            let duplicateAnchor = inheritedAnchor && anchor.IsSome
            let mutable implicitMapping = false
            let mutable alias = false
            node.Tag <- tag

            let checkProperties () =
                if duplicateTag then
                    fail position "A YAML node can have only one tag"

                if duplicateAnchor then
                    fail position "A YAML node can have only one anchor"

            match anchor with
            | Some name -> anchors[name] <- node
            | None -> ()

            let propertiesOnPreviousLine =
                not flow && (peek () = '\n' || peek () = '#') && (tag <> "" || anchor.IsSome)

            if propertiesOnPreviousLine then
                checkProperties ()
                skipTrivia ()

            let contentPosition = cursor

            if
                defaultArg compact false
                && not propertiesOnPreviousLine
                && (tag <> "" || anchor.IsSome)
                && (indicator '-' || indicator '?')
            then
                fail cursor "A YAML compact block collection cannot have leading properties"

            if propertiesOnPreviousLine then
                if
                    cursor < text.Length
                    && not (marker "---" || marker "...")
                    && (column cursor > parent
                        || (defaultArg indentless false && column cursor = parent && indicator '-'))
                then
                    let content =
                        this.Node(
                            parent,
                            false,
                            true,
                            depth + 1,
                            keyMode,
                            ?indentless = indentless,
                            inheritedProperties =
                                (inheritedTag || tag <> "", inheritedAnchor || anchor.IsSome)
                        )

                    if content.Tag = "" then
                        content.Tag <- node.Tag

                    node.Value <- content.Value

                    if node.Tag = "" then
                        node.Tag <- content.Tag
            elif not flow && allowMapping && indicator '-' then
                this.Sequence(node, column cursor, depth)
            elif not flow && not allowMapping && indicator '-' then
                fail cursor "A YAML block sequence cannot start on this line"
            elif not flow && allowMapping && indicator '?' then
                this.Mapping(node, column cursor, depth)
            else
                let mutable quoted = false

                match peek () with
                | '['
                | '{' -> this.Flow(node, depth)
                | '*' ->
                    if tag <> "" || anchor.IsSome then
                        fail cursor "A YAML alias cannot have properties"

                    alias <- true
                    cursor <- cursor + 1
                    let start = cursor

                    while not (separator (peek ()) || flowEnd (peek ())) do
                        if peek () = '[' || peek () = '{' then
                            fail cursor "A YAML alias name cannot contain a flow opener"

                        cursor <- cursor + 1

                    let name = text.Substring(start, cursor - start)

                    let target =
                        match anchors.TryGetValue name with
                        | true, target -> Some target
                        | _ -> None

                    node.Value <- Alias(name, target)
                | '\''
                | '"' ->
                    let value, style = this.Quoted parent
                    node.Value <- Atom(value, style)
                    quoted <- true
                | '|'
                | '>' when not flow ->
                    let value, style = this.BlockScalar parent
                    node.Value <- Atom(value, style)
                | '\000'
                | '\n'
                | '#' -> ()
                | c when flowEnd c ->
                    if not flow then
                        fail cursor "A YAML value cannot start with a flow delimiter"
                | ':' when colon flow -> ()
                | ':' -> fail cursor "A plain YAML value cannot start with ':'; quote it"
                | '%' -> fail cursor "A YAML value cannot start with '%'"
                | _ ->
                    let value = this.Plain(parent, flow)
                    node.Value <- Atom(value, YamlStyle.Plain)

                skipSpaces ()

                if allowMapping && (colon flow || (quoted && peek () = ':')) then
                    if flow then
                        ()
                    elif lineStart contentPosition <> lineStart cursor then
                        if not keyMode then
                            fail cursor "A YAML mapping key must stay on one line"
                    else
                        node <- this.MappingFrom(node, column position, depth)
                        implicitMapping <- true
                elif not allowMapping && not flow && not keyMode && colon false then
                    if lineStart contentPosition <> lineStart cursor then
                        fail cursor "A YAML mapping key must stay on one line"
                    else
                        fail cursor "A YAML mapping cannot start on this line"

            if not implicitMapping then
                checkProperties ()

                if alias && (inheritedTag || inheritedAnchor) then
                    fail position "A YAML alias cannot have properties"

            node

        member private this.ValueAfter(parent: int, depth: int, indentless: bool, ?compact: bool) =
            skipSpaces ()
            let position = cursor

            if peek () = '\n' || peek () = '#' || cursor = text.Length then
                skipTrivia ()

                if
                    cursor < text.Length
                    && not (marker "---" || marker "...")
                    && (column cursor > parent
                        || (indentless && column cursor = parent && indicator '-'))
                then
                    this.Node(parent, false, true, depth, false, indentless = indentless)
                else
                    empty position
            else
                this.Node(
                    parent,
                    false,
                    defaultArg compact false,
                    depth,
                    false,
                    indentless = indentless,
                    compact = defaultArg compact false
                )

        member private this.Sequence(node: Node, indent: int, depth: int) =
            let items = ResizeArray<Node>()
            let mutable reading = true

            while reading && indicator '-' && column cursor = indent do
                cursor <- cursor + 1
                skipSpaces ()

                if peek () = '\n' || peek () = '#' || cursor = text.Length then
                    items.Add(this.ValueAfter(indent, depth + 1, false))
                else
                    items.Add(this.Node(indent, false, true, depth + 1, false))

                skipTrivia ()
                reading <- cursor < text.Length && not (marker "---" || marker "...")

            node.Value <- Items(items.ToArray())

        member private this.MappingFrom(first: Node, indent: int, depth: int) =
            let mapping = Node(first.Position)
            this.MappingEntries(mapping, indent, depth, Some first)
            mapping

        member private this.Mapping(node: Node, indent: int, depth: int) =
            this.MappingEntries(node, indent, depth, None)

        member private this.MappingEntries
            (node: Node, indent: int, depth: int, initial: Node option)
            =
            let entries = ResizeArray<Node * Node>()
            let mutable first = initial
            let mutable reading = true

            while reading do
                let keyPosition = cursor
                let explicitKey = first.IsNone && indicator '?'

                let key =
                    match first with
                    | Some key ->
                        first <- None
                        key
                    | None ->
                        if explicitKey then
                            cursor <- cursor + 1
                            skipSpaces ()

                        if
                            explicitKey && (peek () = '\n' || peek () = '#' || cursor = text.Length)
                        then
                            skipTrivia ()

                            if
                                cursor < text.Length
                                && column cursor > indent
                                && not (marker "---" || marker "...")
                            then
                                this.Node(indent, false, true, depth + 1, true)
                            else
                                empty keyPosition
                        else
                            this.Node(
                                indent,
                                false,
                                explicitKey,
                                depth + 1,
                                true,
                                compact = explicitKey
                            )

                skipSpaces ()

                if explicitKey then
                    skipTrivia ()

                let value =
                    if colon false then
                        if explicitKey && column cursor <> indent then
                            fail cursor "Unexpected indentation in a YAML mapping"

                        if not explicitKey && lineStart key.Position <> lineStart cursor then
                            fail cursor "A YAML mapping key must stay on one line"

                        if not explicitKey && cursor - key.Position > 1024 then
                            fail key.Position "An implicit YAML key cannot exceed 1024 characters"

                        match key.Value with
                        | Atom("", _) when not explicitKey ->
                            fail keyPosition "A YAML mapping key cannot be empty"
                        | _ -> ()

                        cursor <- cursor + 1
                        this.ValueAfter(indent, depth + 1, true, compact = explicitKey)
                    elif explicitKey then
                        empty cursor
                    else
                        fail cursor "Expected ':' in a YAML mapping"

                entries.Add(key, value)
                skipTrivia ()

                if
                    cursor = text.Length || marker "---" || marker "..." || column cursor < indent
                then
                    reading <- false
                elif column cursor > indent then
                    fail cursor "Unexpected indentation in a YAML mapping"
                elif indicator '-' then
                    reading <- false

            node.Value <- Pairs(entries.ToArray())

        member private this.Flow(node: Node, depth: int) =
            let position = cursor
            let mapping = peek () = '{'
            let closing = if mapping then '}' else ']'
            cursor <- cursor + 1
            skipTrivia ()
            let items = ResizeArray<Node>()
            let entries = ResizeArray<Node * Node>()
            let mutable finished = false

            let expected () =
                fail cursor ($"Expected ',' or '{closing}' in a YAML flow collection")

            while not finished do
                if cursor = text.Length then
                    fail position "Unterminated YAML flow collection"

                if peek () = closing then
                    finished <- true
                    cursor <- cursor + 1
                else
                    let explicitKey = indicator '?'

                    if explicitKey then
                        cursor <- cursor + 1
                        skipTrivia ()

                    let keyPosition = cursor
                    let hasProperties = peek () = '&' || peek () = '!'
                    let key = this.Node(-1, true, false, depth + 1, true)
                    let keyFinish = cursor

                    let quoted =
                        match key.Value with
                        | Atom(_, YamlStyle.SingleQuoted)
                        | Atom(_, YamlStyle.DoubleQuoted) -> true
                        | _ -> false

                    let comment = peek () = '#'
                    skipTrivia ()
                    let sameLine = lineStart keyFinish = lineStart cursor
                    let inlinePair = colon true || (quoted && peek () = ':')

                    let permitsPair =
                        (sameLine && (not hasProperties || lineStart keyPosition = lineStart cursor))
                        || explicitKey
                        || (mapping && quoted)
                        || (mapping && comment && not hasProperties)

                    if inlinePair && not permitsPair then
                        expected ()

                    if inlinePair then
                        if not explicitKey && keyFinish - keyPosition > 1024 then
                            fail keyPosition "An implicit YAML key cannot exceed 1024 characters"

                        match key.Value with
                        | Atom("", _) when not hasProperties && not explicitKey ->
                            fail keyPosition "A YAML mapping key cannot be empty"
                        | _ -> ()

                        cursor <- cursor + 1
                        skipTrivia ()
                        let value = this.Node(-1, true, false, depth + 1, false)

                        if mapping then
                            entries.Add(key, value)
                        else
                            let pair = Node(keyPosition)
                            pair.Value <- Pairs [| key, value |]
                            items.Add pair
                    elif mapping then
                        entries.Add(key, empty cursor)
                    else
                        items.Add key

                    skipTrivia ()

                    if peek () = ',' then
                        cursor <- cursor + 1
                        skipTrivia ()
                    elif peek () <> closing then
                        if cursor = text.Length then
                            fail position "Unterminated YAML flow collection"

                        expected ()

            node.Value <-
                if mapping then
                    Pairs(entries.ToArray())
                else
                    Items(items.ToArray())

            if peek () = '#' then
                fail cursor ($"A comment after '{closing}' needs a blank before it")

        member private _.Resolve(root: Node) =
            let memo = Dictionary<Node, YamlNode>()
            let visiting = HashSet<Node>()

            let rec resolve depth aliases (node: Node) =
                match memo.TryGetValue node with
                | true, result -> result
                | _ ->
                    match node.Value with
                    | Alias(name, target) ->
                        if depth >= 256 || aliases >= 256 then
                            fail node.Position "YAML aliases nest deeper than 256 levels"

                        visiting.Add node |> ignore

                        let target =
                            match target with
                            | Some target -> target
                            | None ->
                                match anchors.TryGetValue name with
                                | true, target -> target
                                | _ ->
                                    fail
                                        node.Position
                                        ("The YAML alias *" + name + " has no anchor")

                        if visiting.Contains target then
                            fail
                                node.Position
                                ("The YAML alias *" + name + " refers to its own node")

                        let result = resolve depth (aliases + 1) target
                        visiting.Remove node |> ignore
                        memo[node] <- result
                        result
                    | value ->
                        visiting.Add node |> ignore

                        let result =
                            match value with
                            | Atom(value, style) -> YamlNode.Scalar(node.Tag, value, style)
                            | Items items ->
                                YamlNode.Sequence(
                                    node.Tag,
                                    Array.map (fun item -> resolve (depth + 1) aliases item) items
                                )
                            | Pairs entries ->
                                let pairs =
                                    entries
                                    |> Array.map (fun (key, value) ->
                                        resolve (depth + 1) aliases key,
                                        resolve (depth + 1) aliases value)

                                let seen = HashSet<YamlNode>()

                                let forward (key: Node) =
                                    match key.Value with
                                    | Alias(_, None) -> true
                                    | _ -> false

                                for deferred in [ false; true ] do
                                    for index = 0 to entries.Length - 1 do
                                        let key, _ = entries[index]

                                        if forward key = deferred then
                                            let resolved, _ = pairs[index]

                                            let comparable =
                                                match resolved with
                                                | YamlNode.Scalar(_, value, _) ->
                                                    YamlNode.Scalar("", value, YamlStyle.Plain)
                                                | _ -> resolved

                                            if not (seen.Add comparable) then
                                                let name =
                                                    match comparable with
                                                    | YamlNode.Scalar(_, value, _) -> value
                                                    | _ -> ""

                                                fail
                                                    key.Position
                                                    ("Duplicate YAML mapping key " + name)

                                YamlNode.Mapping(node.Tag, pairs)
                            | Alias _ -> invalidOp "Alias handled separately."

                        visiting.Remove node |> ignore
                        memo[node] <- result
                        result

            resolve 0 0 root

        member private _.Directives() =
            let mutable directives = false
            let mutable version = false

            while peek () = '%' && column cursor = 0 do
                directives <- true
                let position = cursor
                let finish = lineEnd cursor

                let parts =
                    text
                        .Substring(cursor + 1, finish - cursor - 1)
                        .Split([| ' '; '\t' |], StringSplitOptions.RemoveEmptyEntries)
                    |> Array.takeWhile (fun part -> not (part.StartsWith('#')))

                match parts with
                | [| "YAML"; number |] ->
                    if version then
                        fail position "Duplicate YAML version directive"

                    version <- true

                    let versionParts = number.Split('.')

                    let digits (value: string) =
                        value.Length > 0 && (value |> Seq.forall Char.IsAsciiDigit)

                    let valid =
                        versionParts.Length = 2
                        && Array.forall digits versionParts
                        && (match
                                Int32.TryParse versionParts[0], Int32.TryParse versionParts[1]
                            with
                            | (true, 1), (true, minor) -> minor <= 3
                            | _ -> false)

                    if not valid then
                        fail position ("Unsupported YAML version " + number)
                | parts when parts.Length >= 3 && parts[0] = "TAG" ->
                    if not (declaredHandles.Add parts[1]) then
                        fail position "Duplicate YAML tag directive"

                    handles[parts[1]] <- decodeTag position parts[2]
                | parts when parts.Length > 0 && (parts[0] = "YAML" || parts[0] = "TAG") ->
                    fail position "Invalid YAML directive"
                | _ -> ()

                cursor <- finish
                skipTrivia ()

            if directives && not (marker "---") then
                fail cursor "Expected '---' after YAML directives"

        member this.Parse() =
            for index = 0 to text.Length - 1 do
                let c = text[index]

                if (c < ' ' && c <> '\n' && c <> '\t') || (c >= '\u007f' && c <= '\u009f') then
                    fail index ($"YAML cannot contain the control character U+{int c:X4}")

            if peek () = '\ufeff' then
                cursor <- cursor + 1

            let documents = ResizeArray<YamlNode>()
            skipTrivia ()

            while cursor < text.Length do
                reset ()
                this.Directives()

                if marker "..." then
                    cursor <- cursor + 3
                    skipTrivia ()
                else
                    let explicitDocument = marker "---"

                    if explicitDocument then
                        cursor <- cursor + 3
                        skipTrivia ()

                    let node =
                        if cursor = text.Length || marker "---" || marker "..." then
                            empty cursor
                        else
                            this.Node(-1, false, true, 1, false)

                    skipTrivia ()

                    if cursor < text.Length && not (marker "---" || marker "...") then
                        fail cursor "Unexpected content after a YAML document"

                    documents.Add(this.Resolve node)

            documents.ToArray()

    let parse path content = Reader(path, content).Parse()
