module Csff.Tests.CorpusComparison

open System
open System.Collections.Generic
open System.IO
open System.Text
open System.Threading
open Csff.Lexer

let usage =
    String.concat
        "\n"
        [
            "usage: --compare-corpus <reference-dir> <candidate-dir> [options]"
            ""
            "  --clusters N   how many clusters to report, largest first (default 20)"
            "  --examples N   examples to show per cluster (default 1)"
            "  --context N    lines of context around each example (default 0)"
            "  --json <path>  write every cluster, with its sites, as JSON"
            ""
            "Both directories hold the same relative paths, each already formatted by"
            "one build. Files present in only one are reported separately. Exit status"
            "is 0 when the two agree, 1 when they differ and 2 on a usage error."
        ]

[<Struct>]
type Hunk =
    {
        File: string
        Name: string
        Line: int
        Mirror: int
        Span: int
        Dropped: int
        Added: int
        Delta: int
        IndentOnly: bool
        Approximate: bool
        Reference: string
        Candidate: string
        Before: string
        After: string
    }

let absent = "(nothing)"

let private tokenMarker (text: string) (token: Token) =
    match token.Kind with
    | TokenKind.IdentifierToken
    | TokenKind.NumericLiteralToken
    | TokenKind.CharacterLiteralToken
    | TokenKind.StringLiteralToken
    | TokenKind.InterpolatedStringToken
    | TokenKind.InterpolatedStringTextToken
    | TokenKind.SingleLineRawStringLiteralToken
    | TokenKind.MultiLineRawStringLiteralToken
    | TokenKind.Utf8StringLiteralToken
    | TokenKind.Utf8SingleLineRawStringLiteralToken
    | TokenKind.Utf8MultiLineRawStringLiteralToken
    | TokenKind.XmlEntityLiteralToken
    | TokenKind.XmlTextLiteralToken -> "x"
    | _ ->
        let spelling = text.Substring(token.Start, token.Length)

        if Char.IsLetter spelling[0] || spelling[0] = '_' then
            "x"
        else
            spelling

let private triviaMarker (text: string) (trivia: Trivia) =
    match trivia.Kind with
    | TriviaKind.WhitespaceTrivia
    | TriviaKind.EndOfLineTrivia -> ""
    | TriviaKind.SingleLineCommentTrivia -> "//x"
    | TriviaKind.MultiLineCommentTrivia -> "/*x*/"
    | TriviaKind.SingleLineDocumentationCommentTrivia -> "///x"
    | TriviaKind.MultiLineDocumentationCommentTrivia -> "/**x*/"
    | TriviaKind.DocumentationCommentExteriorTrivia -> ""
    | TriviaKind.DisabledTextTrivia -> "(disabled)"
    | _ ->
        let span = text.AsSpan(trivia.Start, trivia.Length).TrimStart()

        if span.Length > 0 && span[0] = '#' then
            let mutable length = 1

            while length < span.Length && (Char.IsLetter span[length] || span[length] = '_') do
                length <- length + 1

            String(span.Slice(0, length))
        else
            "x"

let private ownsItsBlanks (kind: TokenKind) =
    match kind with
    | TokenKind.StringLiteralToken
    | TokenKind.InterpolatedStringToken
    | TokenKind.MultiLineRawStringLiteralToken
    | TokenKind.Utf8StringLiteralToken
    | TokenKind.Utf8MultiLineRawStringLiteralToken -> true
    | _ -> false

let private carriesItsBlanks (kind: TokenKind) =
    match kind with
    | TokenKind.CharacterLiteralToken
    | TokenKind.StringLiteralToken
    | TokenKind.InterpolatedStringToken
    | TokenKind.InterpolatedStringTextToken
    | TokenKind.SingleLineRawStringLiteralToken
    | TokenKind.MultiLineRawStringLiteralToken
    | TokenKind.Utf8StringLiteralToken
    | TokenKind.Utf8SingleLineRawStringLiteralToken
    | TokenKind.Utf8MultiLineRawStringLiteralToken
    | TokenKind.XmlTextLiteralToken -> true
    | _ -> false

let collapseOutside (value: bool array) (text: string) =
    let opaque index = index < value.Length && value[index]

    let mutable first = 0
    let mutable last = text.Length - 1

    while first <= last && not (opaque first) && Char.IsWhiteSpace text[first] do
        first <- first + 1

    while last >= first && not (opaque last) && Char.IsWhiteSpace text[last] do
        last <- last - 1

    let builder = StringBuilder()
    let mutable blank = false

    for index in first..last do
        let ch = text[index]

        if not (opaque index) && (ch = ' ' || ch = '\t') then
            blank <- true
        else
            if blank && builder.Length > 0 then
                builder.Append ' ' |> ignore

            blank <- false
            builder.Append ch |> ignore

    builder.ToString()

let private buffers = new ThreadLocal<TokenBuffer>(fun () -> TokenBuffer())

let shapesOf (text: string) (lines: string array) =
    let builders = Array.init lines.Length (fun _ -> StringBuilder())
    let inside = Array.zeroCreate<bool> lines.Length

    let value =
        Array.init lines.Length (fun index -> Array.zeroCreate<bool> lines[index].Length)

    let starts = Array.zeroCreate<int> lines.Length
    let ends = Array.zeroCreate<int> lines.Length
    let cursors = Array.zeroCreate<int> lines.Length
    let mutable offset = 0

    for index in 0 .. lines.Length - 1 do
        starts[index] <- offset
        ends[index] <- offset + lines[index].Length
        cursors[index] <- offset
        offset <- offset + lines[index].Length + 1

    let lineOf position =
        let mutable low = 0
        let mutable high = lines.Length - 1

        while low < high do
            let middle = (low + high + 1) / 2

            if starts[middle] <= position then
                low <- middle
            else
                high <- middle - 1

        low

    let emit (start: int) (length: int) (owned: bool) (marker: string) =
        if marker <> "" && lines.Length > 0 then
            let first = lineOf start
            let last = lineOf (max start (start + length - 1))

            if owned then
                for line in first + 1 .. min last (lines.Length - 1) do
                    inside[line] <- true

            for line in first .. min last (lines.Length - 1) do
                let builder = builders[line]
                let from = max start starts[line]

                if from > cursors[line] && builder.Length > 0 then
                    builder.Append ' ' |> ignore

                builder.Append marker |> ignore
                cursors[line] <- min (start + length) ends[line]

    let buffer = buffers.Value
    buffer.Reset()
    Lexer.lex text buffer

    for index in 0 .. buffer.TokenCount - 1 do
        let token = buffer.Token index
        let leading = token.TriviaStart + token.LeadingCount

        for slot in token.TriviaStart .. leading - 1 do
            let trivia = buffer.Trivia slot
            emit trivia.Start trivia.Length false (triviaMarker text trivia)

        if token.Length > 0 then
            emit token.Start token.Length (ownsItsBlanks token.Kind) (tokenMarker text token)

            if carriesItsBlanks token.Kind && lines.Length > 0 then
                let first = lineOf token.Start
                let last = lineOf (max token.Start (token.Start + token.Length - 1))

                if first = last then
                    let from = max token.Start starts[first]
                    let upto = min (token.Start + token.Length) ends[first]

                    for position in from .. upto - 1 do
                        value[first][position - starts[first]] <- true

        for slot in leading .. leading + token.TrailingCount - 1 do
            let trivia = buffer.Trivia slot
            emit trivia.Start trivia.Length false (triviaMarker text trivia)

    let shapes =
        Array.init lines.Length (fun index ->
            if builders[index].Length > 0 then
                builders[index].ToString()
            elif lines[index].Trim().Length = 0 then
                "(blank)"
            else
                "(unlexed)")

    let collapsed =
        Array.init lines.Length (fun index -> collapseOutside value[index] lines[index])

    struct (shapes, inside, collapsed)

let shape (text: string) =
    if text = absent then
        absent
    else
        let struct (shapes, _, _) = shapesOf text [| text |]
        shapes[0]

let tabWidth = 4

let private indentOf (text: string) =
    let mutable column = 0
    let mutable index = 0

    while index < text.Length && (text[index] = ' ' || text[index] = '\t') do
        column <-
            if text[index] = '\t' then
                (column / tabWidth + 1) * tabWidth
            else
                column + 1

        index <- index + 1

    column

let private indentTextOf (text: string) =
    let mutable index = 0

    while index < text.Length && (text[index] = ' ' || text[index] = '\t') do
        index <- index + 1

    text.Substring(0, index)

let private indentStyleOf (text: string) =
    let indent = indentTextOf text

    if indent.Length = 0 then
        "none"
    elif indent.Contains '\t' && indent.Contains ' ' then
        "mixed"
    elif indent.Contains '\t' then
        "tabs"
    else
        "spaces"

let key (hunk: Hunk) =
    let name =
        if hunk.Name <> "" then
            hunk.Name
        elif hunk.IndentOnly then
            $"indentation %+d{hunk.Delta}"
        else
            let shift =
                if hunk.Delta = 0 then
                    ""
                else
                    $", indentation %+d{hunk.Delta}"

            if hunk.Before = hunk.After then
                if hunk.Delta <> 0 then
                    hunk.Before + shift
                else
                    let collapsed (text: string) =
                        let builder = StringBuilder()
                        let mutable blank = false

                        for ch in text.Trim() do
                            if ch = ' ' || ch = '\t' then
                                blank <- true
                            else
                                if blank && builder.Length > 0 then
                                    builder.Append ' ' |> ignore

                                blank <- false
                                builder.Append ch |> ignore

                        builder.ToString()

                    if
                        hunk.Reference.Trim() <> hunk.Candidate.Trim()
                        && collapsed hunk.Reference = collapsed hunk.Candidate
                    then
                        "internal whitespace: " + hunk.Before
                    else
                        "text, not layout: " + hunk.Before
            else
                hunk.Before + "  ==>  " + hunk.After + shift

    if hunk.Approximate then name + "   [approximate]" else name

let private named (relative: string) label line mirror before after =
    {
        File = relative
        Name = label + " " + before + "  ==>  " + after
        Line = line
        Mirror = mirror
        Span = 1
        Dropped = 1
        Added = 1
        Delta = 0
        IndentOnly = false
        Approximate = false
        Reference = before
        Candidate = after
        Before = before
        After = after
    }

let private wholeFile (relative: string) label before after = named relative label 1 1 before after

type Alignment =
    | Exact
    | Approximate

[<NoComparison; NoEquality>]
type Side =
    {
        Lines: string array
        Shapes: string array
        Inside: bool array
        Collapsed: string array
    }

let sideOf (lines: string array) =
    let struct (shapes, inside, collapsed) = shapesOf (String.Join('\n', lines)) lines

    {
        Lines = lines
        Shapes = shapes
        Inside = inside
        Collapsed = collapsed
    }

let fromLines (lines: string array) =
    {
        Lines = lines
        Shapes = lines |> Array.map shape
        Inside = Array.zeroCreate lines.Length
        Collapsed = lines |> Array.map (fun line -> collapseOutside Array.empty line)
    }

[<NoComparison; NoEquality>]
type Comparison =
    {
        Hunks: ResizeArray<Hunk>
        Alignment: Alignment
        Paired: ResizeArray<struct (int * int)>
    }

let private script (reference: string array) (candidate: string array) (limit: int) =
    let n = reference.Length
    let m = candidate.Length
    let furthest = n + m
    let offset = furthest + 1
    let v = Array.create (2 * furthest + 3) 0
    let trace = ResizeArray<int array>()
    let mutable depth = 0
    let mutable complete = false
    let mutable abandoned = false

    while not complete && not abandoned do
        if depth > limit then
            abandoned <- true
        else

            trace.Add(Array.sub v (offset - depth - 1) (2 * depth + 3))
            let mutable k = -depth

            while k <= depth && not complete do
                let mutable x =
                    if k = -depth || (k <> depth && v[k - 1 + offset] < v[k + 1 + offset]) then
                        v[k + 1 + offset]
                    else
                        v[k - 1 + offset] + 1

                let mutable y = x - k

                while x < n && y < m && reference[x] = candidate[y] do
                    x <- x + 1
                    y <- y + 1

                v[k + offset] <- x

                if x >= n && y >= m then
                    complete <- true

                k <- k + 2

            if not complete then
                depth <- depth + 1

    if abandoned then
        None
    else
        let steps = ResizeArray<struct (int * int)>()
        let mutable x = n
        let mutable y = m

        for d in trace.Count - 1 .. -1 .. 0 do
            let previous = trace[d]
            let middle = d + 1
            let k = x - y

            let before =
                if k = -d || (k <> d && previous[k - 1 + middle] < previous[k + 1 + middle]) then
                    k + 1
                else
                    k - 1

            let priorX = if d = 0 then 0 else previous[before + middle]
            let priorY = priorX - before

            while x > priorX && y > priorY do
                x <- x - 1
                y <- y - 1
                steps.Add(struct (x, y))

            if d > 0 then
                if x = priorX then
                    y <- y - 1
                    steps.Add(struct (-1, y))
                else
                    x <- x - 1
                    steps.Add(struct (x, -1))

        steps.Reverse()
        Some steps

let private regions (steps: ResizeArray<struct (int * int)>) =
    let found = ResizeArray<struct (int * int * ResizeArray<int> * ResizeArray<int>)>()
    let mutable dropped = ResizeArray<int>()
    let mutable added = ResizeArray<int>()
    let mutable opened = 0
    let mutable mirrored = 0

    let close () =
        if dropped.Count > 0 || added.Count > 0 then
            found.Add(struct (opened, mirrored, dropped, added))
            dropped <- ResizeArray<int>()
            added <- ResizeArray<int>()

    for struct (r, c) in steps do
        if r >= 0 && c >= 0 then
            close ()
            opened <- r + 1
            mirrored <- c + 1
        elif c < 0 then
            dropped.Add r
            opened <- r + 1
        else
            added.Add c
            mirrored <- c + 1

    close ()
    found

let hunksWithin (limit: int) (relative: string) (before: Side) (after: Side) =
    let reference = before.Lines
    let candidate = after.Lines
    let found = ResizeArray<Hunk>()
    let paired = ResizeArray<struct (int * int)>()

    let shapeOf (shapes: string array) index =
        if index >= 0 && index < shapes.Length then
            shapes[index]
        else
            absent

    let shapeHunk
        (opened: int)
        (mirrored: int)
        (dropped: ResizeArray<int>)
        (added: ResizeArray<int>)
        =
        let line = if dropped.Count > 0 then dropped[0] + 1 else opened + 1
        let mirror = if added.Count > 0 then added[0] + 1 else mirrored + 1

        {
            File = relative
            Name = ""
            Line = line
            Mirror = mirror
            Span = max dropped.Count added.Count
            Dropped = dropped.Count
            Added = added.Count
            Delta =
                if dropped.Count > 0 && added.Count > 0 then
                    indentOf candidate[added[0]] - indentOf reference[dropped[0]]
                else
                    0
            IndentOnly = false
            Approximate = false
            Reference = if dropped.Count > 0 then reference[dropped[0]] else absent
            Candidate = if added.Count > 0 then candidate[added[0]] else absent
            Before =
                if dropped.Count > 0 then
                    shapeOf before.Shapes dropped[0]
                else
                    absent
            After =
                if added.Count > 0 then
                    shapeOf after.Shapes added[0]
                else
                    absent
        }

    let alignment =
        match script reference candidate limit with
        | None -> Approximate
        | Some steps ->
            for struct (r, c) in steps do
                if r >= 0 && c >= 0 then
                    paired.Add(struct (r, c))

            for struct (opened, mirrored, dropped, added) in regions steps do
                if dropped.Count <> added.Count then
                    found.Add(shapeHunk opened mirrored dropped added)
                else
                    for position in 0 .. dropped.Count - 1 do
                        paired.Add(struct (dropped[position], added[position]))

                    let mutable index = 0

                    while index < dropped.Count do
                        let r = dropped[index]
                        let c = added[index]
                        let delta = indentOf candidate[c] - indentOf reference[r]

                        let owned = before.Inside[r] || after.Inside[c]

                        if owned && reference[r] <> candidate[c] then
                            found.Add(
                                named
                                    relative
                                    "literal text"
                                    (r + 1)
                                    (c + 1)
                                    (string (indentOf reference[r]))
                                    (string (indentOf candidate[c]))
                            )

                            index <- index + 1
                        elif
                            reference[r].TrimStart() = candidate[c].TrimStart()
                            && delta = 0
                            && indentTextOf reference[r] <> indentTextOf candidate[c]
                        then
                            found.Add(
                                named
                                    relative
                                    "indentation style"
                                    (r + 1)
                                    (c + 1)
                                    (indentStyleOf reference[r])
                                    (indentStyleOf candidate[c])
                            )

                            index <- index + 1
                        elif reference[r].TrimStart() = candidate[c].TrimStart() then
                            let first = index

                            let mutable sameShift = true

                            while sameShift do
                                if
                                    index < dropped.Count
                                    && not before.Inside[dropped[index]]
                                    && not after.Inside[added[index]]
                                    && reference[dropped[index]].TrimStart() =
                                        candidate[added[index]].TrimStart()
                                    && indentOf candidate[added[index]]
                                       - indentOf reference[dropped[index]]
                                        =
                                        delta
                                then
                                    index <- index + 1
                                else
                                    sameShift <- false

                            found.Add
                                {
                                    File = relative
                                    Name = ""
                                    Line = r + 1
                                    Mirror = c + 1
                                    Span = index - first
                                    Dropped = index - first
                                    Added = index - first
                                    Delta = delta
                                    IndentOnly = true
                                    Approximate = false
                                    Reference = reference[r]
                                    Candidate = candidate[c]
                                    Before = shapeOf before.Shapes r
                                    After = shapeOf after.Shapes c
                                }
                        elif reference[r].TrimEnd() = candidate[c].TrimEnd() then
                            let blanks (line: string) = line.Length - line.TrimEnd().Length

                            found.Add(
                                named
                                    relative
                                    "trailing whitespace"
                                    (r + 1)
                                    (c + 1)
                                    (string (blanks reference[r]))
                                    (string (blanks candidate[c]))
                            )

                            index <- index + 1
                        else
                            let one = ResizeArray<int>()
                            one.Add r
                            let other = ResizeArray<int>()
                            other.Add c
                            let hunk = shapeHunk r c one other

                            let named =
                                if
                                    hunk.Name = ""
                                    && hunk.Delta = 0
                                    && hunk.Before = hunk.After
                                    && reference[r].Trim() <> candidate[c].Trim()
                                then
                                    let same =
                                        shapeOf before.Collapsed r = shapeOf after.Collapsed c

                                    let label =
                                        if same then
                                            "internal whitespace: "
                                        else
                                            "text, not layout: "

                                    { hunk with Name = label + hunk.Before }
                                else
                                    hunk

                            found.Add named
                            index <- index + 1

            Exact

    if alignment = Approximate then
        let mutable r = 0
        let mutable c = 0

        while r < reference.Length && c < candidate.Length do
            if reference[r] = candidate[c] then
                paired.Add(struct (r, c))
                r <- r + 1
                c <- c + 1
            else
                let openedAt = r
                let mirroredAt = c
                let mutable offset = 1
                let mutable joined = false

                while not joined && offset <= 40 do
                    if c + offset < candidate.Length && reference[r] = candidate[c + offset] then
                        c <- c + offset
                        joined <- true
                    elif r + offset < reference.Length && reference[r + offset] = candidate[c] then
                        r <- r + offset
                        joined <- true
                    else
                        offset <- offset + 1

                if not joined then
                    r <- r + 1
                    c <- c + 1

                let one = ResizeArray<int>()
                let other = ResizeArray<int>()

                for position in openedAt .. r - 1 do
                    one.Add position

                for position in mirroredAt .. c - 1 do
                    other.Add position

                found.Add(shapeHunk openedAt mirroredAt one other)

        if r < reference.Length || c < candidate.Length then
            let one = ResizeArray<int>()
            let other = ResizeArray<int>()

            for position in r .. reference.Length - 1 do
                one.Add position

            for position in c .. candidate.Length - 1 do
                other.Add position

            found.Add(shapeHunk r c one other)

    if alignment = Approximate then
        for position in 0 .. found.Count - 1 do
            found[position] <-
                { found[position] with
                    Approximate = true
                }

    {
        Hunks = found
        Alignment = alignment
        Paired = paired
    }

[<NoComparison>]
type Cluster =
    {
        Key: string
        Lines: int
        Files: int
        Approximate: bool
        Sites: ResizeArray<Hunk>
    }

let clusters (found: seq<Hunk>) =
    let groups = Dictionary<string, ResizeArray<Hunk>>(StringComparer.Ordinal)

    for hunk in found do
        let name = key hunk

        match groups.TryGetValue name with
        | true, sites -> sites.Add hunk
        | _ ->
            let sites = ResizeArray<Hunk>()
            sites.Add hunk
            groups[name] <- sites

    [|
        for pair in groups ->
            {
                Key = pair.Key
                Lines = pair.Value |> Seq.sumBy (fun site -> site.Span)
                Files = pair.Value |> Seq.map (fun site -> site.File) |> Seq.distinct |> Seq.length
                Approximate = pair.Value |> Seq.forall (fun site -> site.Approximate)
                Sites = pair.Value
            }
    |]
    |> Array.sortByDescending (fun cluster ->
        not cluster.Approximate, cluster.Lines, cluster.Files, cluster.Key)

let private smallestFirst (sites: ResizeArray<Hunk>) =
    sites
    |> Seq.sortBy (fun site ->
        site.Span, site.Reference.Length + site.Candidate.Length, site.File, site.Line)

let private endings (text: string) =
    let found = ResizeArray<string>()
    let mutable index = 0

    while index < text.Length do
        if text[index] = '\r' then
            if index + 1 < text.Length && text[index + 1] = '\n' then
                found.Add "crlf"
                index <- index + 2
            else
                found.Add "cr"
                index <- index + 1
        elif text[index] = '\n' then
            found.Add "lf"
            index <- index + 1
        else
            index <- index + 1

    found

let private terminators
    (relative: string)
    (reference: string)
    (candidate: string)
    (paired: ResizeArray<struct (int * int)>)
    =
    let found = ResizeArray<Hunk>()
    let left = endings reference
    let right = endings candidate

    let mutable index = 0
    let mutable differing = ValueNone

    while differing.IsNone && index < paired.Count do
        let struct (r, c) = paired[index]

        if r < left.Count && c < right.Count && left[r] <> right[c] then
            differing <- ValueSome(struct (r, c))

        index <- index + 1

    match differing with
    | ValueSome(struct (r, c)) ->
        found.Add(named relative "line endings" (r + 1) (c + 1) left[r] right[c])
    | ValueNone ->
        let only (found: ResizeArray<string>) =
            if found.Count > 0 && Seq.forall (fun ending -> ending = found[0]) found then
                ValueSome found[0]
            else
                ValueNone

        match only left, only right with
        | ValueSome before, ValueSome after when before <> after ->
            found.Add(wholeFile relative "line endings" before after)
        | _ ->
            let counts (of_: ResizeArray<string>) =
                of_
                |> Seq.countBy id
                |> Seq.fold
                    (fun (map: Map<string, int>) (style, count) -> map.Add(style, count))
                    Map.empty

            let before = counts left
            let after = counts right

            let lost =
                before
                |> Map.toSeq
                |> Seq.tryFind (fun (style, _) -> not (after.ContainsKey style))

            let gained =
                after
                |> Map.toSeq
                |> Seq.tryFind (fun (style, count) ->
                    count > (before.TryFind style |> Option.defaultValue 0))

            match lost, gained with
            | Some(went, _), Some(came, _) -> found.Add(wholeFile relative "line endings" went came)
            | _ -> ()

    let ends (text: string) =
        if text.Length = 0 then
            "empty"
        elif text.EndsWith '\n' || text.EndsWith '\r' then
            "terminated"
        else
            "unterminated"

    if ends reference <> ends candidate then
        found.Add(wholeFile relative "final line" (ends reference) (ends candidate))

    found

let differenceBound = 3000

let hunks relative reference candidate =
    hunksWithin differenceBound relative (fromLines reference) (fromLines candidate)

let private decode (bytes: byte array) =
    let opens (prefix: byte array) =
        bytes.Length >= prefix.Length
        && ReadOnlySpan(bytes, 0, prefix.Length).SequenceEqual(ReadOnlySpan prefix)

    let past (count: int) (encoding: Encoding) =
        encoding.GetString(bytes, count, bytes.Length - count)

    if opens [| 0uy; 0uy; 0xFEuy; 0xFFuy |] then
        struct (past 4 (UTF32Encoding(true, false)), "utf-32be")
    elif opens [| 0xFFuy; 0xFEuy; 0uy; 0uy |] then
        struct (past 4 (UTF32Encoding(false, false)), "utf-32le")
    elif opens [| 0xFFuy; 0xFEuy |] then
        struct (past 2 (UnicodeEncoding(false, false)), "utf-16le")
    elif opens [| 0xFEuy; 0xFFuy |] then
        struct (past 2 (UnicodeEncoding(true, false)), "utf-16be")
    elif opens [| 0xEFuy; 0xBBuy; 0xBFuy |] then
        struct (past 3 (UTF8Encoding(false, false)), "utf-8 with mark")
    else

        try
            struct (UTF8Encoding(false, true).GetString bytes, "utf-8")
        with :? DecoderFallbackException ->
            struct (Encoding.Latin1.GetString bytes, "single byte")

let private split (text: string) =
    let joined = text.Replace("\r\n", "\n").Replace('\r', '\n')

    if joined.EndsWith '\n' then
        joined.Substring(0, joined.Length - 1).Split '\n'
    else
        joined.Split '\n'

let private linesOf (path: string) =
    let struct (text, _) = decode (File.ReadAllBytes path)
    split text

let private relativePaths (root: string) =
    let found = Dictionary<string, string>(StringComparer.Ordinal)

    let rec descend (directory: string) =
        for child in Directory.EnumerateDirectories directory do
            let attributes = File.GetAttributes child

            if not (attributes &&& FileAttributes.ReparsePoint = FileAttributes.ReparsePoint) then
                descend child

        for file in Directory.EnumerateFiles(directory, "*.cs") do
            found[Path.GetRelativePath(root, file)] <- file

    if Directory.Exists root then
        descend root

    found

let private report
    (reference: string)
    (candidate: string)
    (compared: int)
    (differing: int)
    (grouped: Cluster array)
    =
    let limit = 50
    let builder = StringBuilder()
    builder.AppendLine "{" |> ignore

    builder.AppendLine($"  \"referenceDirectory\": {JsonText.quote reference},")
    |> ignore

    builder.AppendLine($"  \"candidateDirectory\": {JsonText.quote candidate},")
    |> ignore

    builder.AppendLine($"  \"filesCompared\": {compared},") |> ignore
    builder.AppendLine($"  \"filesDiffering\": {differing},") |> ignore
    builder.AppendLine($"  \"sitesPerCluster\": {limit},") |> ignore
    builder.AppendLine "  \"clusters\": [" |> ignore

    for position in 0 .. grouped.Length - 1 do
        let cluster = grouped[position]
        let shown = smallestFirst cluster.Sites |> Seq.truncate limit |> Seq.toArray
        builder.AppendLine "    {" |> ignore
        builder.AppendLine($"      \"shape\": {JsonText.quote cluster.Key},") |> ignore
        builder.AppendLine($"      \"lines\": {cluster.Lines},") |> ignore
        builder.AppendLine($"      \"files\": {cluster.Files},") |> ignore

        let approximate = if cluster.Approximate then "true" else "false"
        builder.AppendLine($"      \"approximate\": {approximate},") |> ignore
        builder.AppendLine($"      \"sites\": {cluster.Sites.Count},") |> ignore

        builder.AppendLine($"      \"sitesOmitted\": {cluster.Sites.Count - shown.Length},")
        |> ignore

        builder.AppendLine "      \"places\": [" |> ignore

        for site in 0 .. shown.Length - 1 do
            let hunk = shown[site]
            let comma = if site = shown.Length - 1 then "" else ","

            builder.AppendLine(
                $"        {{ \"file\": {JsonText.quote hunk.File}, \"line\": {hunk.Line}, "
                + $"\"candidateLine\": {hunk.Mirror}, "
                + $"\"span\": {hunk.Span}, \"delta\": {hunk.Delta}, "
                + $"\"reference\": {JsonText.quote hunk.Reference}, "
                + $"\"candidate\": {JsonText.quote hunk.Candidate} }}{comma}"
            )
            |> ignore

        builder.AppendLine "      ]" |> ignore

        builder.AppendLine(if position = grouped.Length - 1 then "    }" else "    },")
        |> ignore

    builder.AppendLine "  ]" |> ignore
    builder.AppendLine "}" |> ignore
    builder.ToString()

let private compare (argv: string array) =
    if argv.Length < 2 then
        Console.Error.WriteLine usage
        2
    else

        let reference = Path.GetFullPath argv[0]
        let candidate = Path.GetFullPath argv[1]
        let mutable clusterLimit = 20
        let mutable exampleLimit = 1
        let mutable contextLines = 0
        let mutable json = null
        let mutable index = 2
        let mutable bad = false

        while index < argv.Length && not bad do
            let value () =
                if index + 1 < argv.Length then
                    Some argv[index + 1]
                else
                    None

            match argv[index], value () with
            | "--clusters", Some v when Int32.TryParse(v, &clusterLimit) -> index <- index + 2
            | "--examples", Some v when Int32.TryParse(v, &exampleLimit) -> index <- index + 2
            | "--context", Some v when Int32.TryParse(v, &contextLines) -> index <- index + 2
            | "--json", Some v ->
                json <- v
                index <- index + 2
            | other, _ ->
                Console.Error.WriteLine $"unrecognised option {other}"
                Console.Error.WriteLine usage
                bad <- true

        if bad then
            2
        else

            let left = relativePaths reference
            let right = relativePaths candidate

            if left.Count = 0 || right.Count = 0 then
                let empty = if left.Count = 0 then reference else candidate
                Console.Error.WriteLine $"no C# under {empty}"
                2
            else

                let shared = ResizeArray<string>()
                let onlyReference = ResizeArray<string>()

                for pair in left do
                    if right.ContainsKey pair.Key then
                        shared.Add pair.Key
                    else
                        onlyReference.Add pair.Key

                let onlyCandidate =
                    right |> Seq.filter (fun pair -> not (left.ContainsKey pair.Key)) |> Seq.length

                shared.Sort StringComparer.Ordinal
                let differing = ResizeArray<string>()
                let found = ResizeArray<Hunk>()
                let approximated = ResizeArray<string>()

                for relative in shared do
                    let rawReference = File.ReadAllBytes left[relative]
                    let rawCandidate = File.ReadAllBytes right[relative]

                    if
                        not (ReadOnlySpan(rawReference).SequenceEqual(ReadOnlySpan(rawCandidate)))
                    then
                        differing.Add relative
                        let countBefore = found.Count
                        let struct (textReference, readAs) = decode rawReference
                        let struct (textCandidate, writtenAs) = decode rawCandidate

                        if readAs <> writtenAs then
                            found.Add(wholeFile relative "encoding" readAs writtenAs)

                        let a = split textReference
                        let b = split textCandidate

                        let comparison = hunksWithin differenceBound relative (sideOf a) (sideOf b)

                        found.AddRange comparison.Hunks

                        if comparison.Alignment = Approximate then
                            approximated.Add relative

                        found.AddRange(
                            terminators
                                relative
                                textReference
                                textCandidate
                                (comparison.Paired
                                 |> Seq.sortBy (fun (struct (r, _)) -> r)
                                 |> ResizeArray)
                        )

                        if found.Count = countBefore then
                            found.Add(wholeFile relative "bytes" readAs writtenAs)

                let grouped = clusters found
                let changedLines = grouped |> Array.sumBy (fun cluster -> cluster.Lines)

                printfn "reference %s" reference
                printfn "candidate %s" candidate
                printfn "%d files compared, %d differ" shared.Count differing.Count

                printfn
                    "%d changed lines in %d hunks in %d clusters"
                    changedLines
                    found.Count
                    grouped.Length

                if onlyReference.Count > 0 || onlyCandidate > 0 then
                    printfn
                        "only in reference: %d, only in candidate: %d"
                        onlyReference.Count
                        onlyCandidate

                if approximated.Count > 0 then
                    printfn
                        "%d files hold more differences than the exact alignment covers, so their hunks are approximate and sort last:"
                        approximated.Count

                    for relative in Seq.truncate 5 approximated do
                        printfn "    %s" relative

                    if approximated.Count > 5 then
                        printfn "    and %d more" (approximated.Count - 5)

                let publish () =
                    if not (isNull json) then
                        File.WriteAllText(
                            json,
                            report reference candidate shared.Count differing.Count grouped
                        )

                        printfn "wrote %s" json

                if shared.Count = 0 then
                    Console.Error.WriteLine $"no path under {reference} is also under {candidate}"

                    2
                elif differing.Count = 0 then
                    printfn "identical"
                    publish ()
                    0
                else

                    let shown = grouped |> Array.truncate (max 1 clusterLimit)
                    printfn ""

                    for cluster in shown do
                        printfn
                            "%d lines, %d files, %d sites  %s"
                            cluster.Lines
                            cluster.Files
                            cluster.Sites.Count
                            cluster.Key

                        for site in smallestFirst cluster.Sites |> Seq.truncate (max 1 exampleLimit) do
                            printfn
                                "    %s:%d%s"
                                site.File
                                site.Line
                                (if site.Span > 1 then $" (+{site.Span - 1})" else "")

                            if contextLines > 0 then
                                let show (label: string) (path: string) (at: int) (span: int) =
                                    let lines = linesOf path
                                    let first = max 0 (at - 1 - contextLines)

                                    let last =
                                        min (lines.Length - 1) (at - 2 + max span 1 + contextLines)

                                    for position in first..last do
                                        let inside =
                                            span > 0
                                            && position >= at - 1
                                            && position < at - 1 + span

                                        printfn
                                            "      %s %s %4d |%s"
                                            label
                                            (if inside then ">" else " ")
                                            (position + 1)
                                            lines[position]

                                show "reference" left[site.File] site.Line site.Dropped
                                show "candidate" right[site.File] site.Mirror site.Added
                            else
                                printfn "      reference  |%s" site.Reference
                                printfn "      candidate  |%s" site.Candidate

                        printfn ""

                    if grouped.Length > shown.Length then
                        printfn
                            "%d further clusters, %d lines, not shown"
                            (grouped.Length - shown.Length)
                            (grouped
                             |> Array.skip shown.Length
                             |> Array.sumBy (fun cluster -> cluster.Lines))

                    publish ()
                    1

let run (argv: string array) = compare argv
