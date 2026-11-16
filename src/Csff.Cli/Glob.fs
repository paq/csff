namespace Csff.Cli

open System
open System.Collections.Generic
open System.Globalization
open System.IO
open System.Numerics
open System.Text
open System.Text.RegularExpressions
open System.Threading

[<RequireQualifiedAccess>]
module internal FastGlobKind =
    [<Literal>]
    let Guarded = 0uy

    [<Literal>]
    let AnyNoNewline = 1uy

    [<Literal>]
    let Exact = 2uy

    [<Literal>]
    let AnySuffix = 3uy

    [<Literal>]
    let AnySuffixes = 4uy

    [<Literal>]
    let AnySegment = 5uy

    [<Literal>]
    let AnySegmentPrefix = 6uy

    [<Literal>]
    let AnySegmentPrefixSuffix = 7uy

    [<Literal>]
    let AnySegmentContains = 8uy

    [<Literal>]
    let AnyDualSegment = 9uy

    [<Literal>]
    let AnyDualSegmentPrefix = 10uy

    [<Literal>]
    let AnyDualSuffix = 11uy

[<Struct; NoEquality; NoComparison>]
type internal FastGlob =
    {
        Kind: byte
        Flags: byte
        Expanded: string
        Primary: string
        Secondary: string
        Tertiary: string
        Suffixes: string array
        Required: string
        SegmentLength: int
    }

module internal Glob =
    let normalize (path: string) = path.Replace('\\', '/')

    let private maximumRangeDigits = 128

    let private tryMatchNumericRange (pattern: string) (start: int) =
        let mutable pos = start + 1

        let scanSignedDigits () =
            let s = pos

            if pos < pattern.Length && pattern[pos] = '-' then
                pos <- pos + 1

            let digitStart = pos

            while pos < pattern.Length && pattern[pos] >= '0' && pattern[pos] <= '9' do
                pos <- pos + 1

            if pos > digitStart then
                ValueSome(struct (s, pos - s, pos - digitStart))
            else
                ValueNone

        match scanSignedDigits () with
        | ValueSome(struct (s1, len1, d1)) when
            pos + 1 < pattern.Length && pattern[pos] = '.' && pattern[pos + 1] = '.'
            ->
            pos <- pos + 2

            match scanSignedDigits () with
            | ValueSome(struct (s2, len2, d2)) when pos < pattern.Length && pattern[pos] = '}' ->
                ValueSome(struct (s1, len1, d1, s2, len2, d2, pos - start + 1))
            | _ -> ValueNone
        | _ -> ValueNone

    let private unsignedRange (first: BigInteger) (last: BigInteger) =
        let rec digits (lower: string) (upper: string) =
            if lower = upper then
                lower
            elif lower = String('0', lower.Length) && upper = String('9', upper.Length) then
                $"[0-9]{{{lower.Length}}}"
            elif lower[0] = upper[0] then
                string lower[0] + digits lower[1..] upper[1..]
            else
                let length = lower.Length - 1
                let choices = ResizeArray<string>()
                choices.Add(string lower[0] + digits lower[1..] (String('9', length)))

                if int upper[0] - int lower[0] > 1 then
                    let left = char (int lower[0] + 1)
                    let right = char (int upper[0] - 1)

                    choices.Add(
                        $"[{left}-{right}]" + digits (String('0', length)) (String('9', length))
                    )

                choices.Add(string upper[0] + digits (String('0', length)) upper[1..])
                "(?:" + String.Join("|", choices) + ")"

        let lower = first.ToString(CultureInfo.InvariantCulture)
        let upper = last.ToString(CultureInfo.InvariantCulture)
        let choices = ResizeArray<string>()

        for length in lower.Length .. upper.Length do
            let left =
                if length = lower.Length then
                    lower
                else
                    "1" + String('0', length - 1)

            let right = if length = upper.Length then upper else String('9', length)
            choices.Add(digits left right)

        "(?:" + String.Join("|", choices) + ")"

    let private rangePattern first last =
        let lower, upper = min first last, max first last
        let choices = ResizeArray<string>()

        if lower < BigInteger.Zero then
            choices.Add("-" + unsignedRange (max BigInteger.One (-upper)) (-lower))

        if upper >= BigInteger.Zero then
            choices.Add(unsignedRange (max BigInteger.Zero lower) upper)

        "(?:" + String.Join("|", choices) + ")"

    let private classMember (character: char) =
        if "\\]-^[".Contains character then
            "\\" + string character
        else
            string character

    let private classEnd (pattern: string) first =
        let mutable index = first
        let mutable ending = -1

        while ending < 0 && index < pattern.Length do
            if pattern[index] = '\\' then
                index <- index + 2
            elif pattern[index] = ']' && index > first then
                ending <- index
            else
                index <- index + 1

        ending

    let private runeAt (content: string) index =
        let c = content[index]

        if
            Char.IsHighSurrogate c
            && index + 1 < content.Length
            && Char.IsLowSurrogate content[index + 1]
        then
            struct (Char.ConvertToUtf32(c, content[index + 1]), 2)
        else
            struct (int c, 1)

    let private classMemberAt (content: string) index =
        if content[index] = '\\' && index + 1 < content.Length then
            let struct (cp, consumed) = runeAt content (index + 1)
            struct (cp, index + 1 + consumed)
        else
            let struct (cp, consumed) = runeAt content index
            struct (cp, index + consumed)

    let private classMemberCharAt (content: string) index =
        if content[index] = '\\' && index + 1 < content.Length then
            struct (int content[index + 1], index + 2)
        else
            struct (int content[index], index + 1)

    let private classPattern (scalar: bool) (negated: bool) (content: string) =
        let bmp = StringBuilder()
        let astral = ResizeArray<string>()

        let appendScalar cp =
            if cp <= 0xFFFF then
                bmp.Append(classMember (char cp)) |> ignore
            else
                let high = char (0xD800 + ((cp - 0x10000) >>> 10))
                let low = char (0xDC00 + ((cp - 0x10000) &&& 0x3FF))
                astral.Add(string high + string low)

        let appendBmpRange first last =
            if first = last then
                bmp.Append(classMember (char first)) |> ignore
            elif first = int '-' then
                bmp.Append("\\-.") |> ignore

                if last > int '.' then
                    bmp.Append('-').Append(classMember (char last)) |> ignore
            else
                bmp.Append(classMember (char first)).Append('-').Append(classMember (char last))
                |> ignore

        let appendAstralRange first last =
            let h1 = 0xD800 + ((first - 0x10000) >>> 10)
            let l1 = 0xDC00 + ((first - 0x10000) &&& 0x3FF)
            let h2 = 0xD800 + ((last - 0x10000) >>> 10)
            let l2 = 0xDC00 + ((last - 0x10000) &&& 0x3FF)

            if h1 = h2 then
                if l1 = l2 then
                    astral.Add(string (char h1) + string (char l1))
                else
                    astral.Add(
                        string (char h1) + "[" + string (char l1) + "-" + string (char l2) + "]"
                    )
            elif l1 = 0xDC00 && l2 = 0xDFFF then
                astral.Add("[" + string (char h1) + "-" + string (char h2) + "][\\uDC00-\\uDFFF]")
            else
                if l1 = 0xDC00 then
                    astral.Add(string (char h1) + "[\\uDC00-\\uDFFF]")
                elif l1 = 0xDFFF then
                    astral.Add(string (char h1) + "\\uDFFF")
                else
                    astral.Add(string (char h1) + "[" + string (char l1) + "-\\uDFFF]")

                if h1 + 1 = h2 - 1 then
                    astral.Add(string (char (h1 + 1)) + "[\\uDC00-\\uDFFF]")
                elif h1 + 1 < h2 - 1 then
                    astral.Add(
                        "["
                        + string (char (h1 + 1))
                        + "-"
                        + string (char (h2 - 1))
                        + "][\\uDC00-\\uDFFF]"
                    )

                if l2 = 0xDFFF then
                    astral.Add(string (char h2) + "[\\uDC00-\\uDFFF]")
                elif l2 = 0xDC00 then
                    astral.Add(string (char h2) + "\\uDC00")
                else
                    astral.Add(string (char h2) + "[\\uDC00-" + string (char l2) + "]")

        let mutable index = 0

        let readMember idx =
            if scalar then
                classMemberAt content idx
            else
                classMemberCharAt content idx

        while index < content.Length do
            let struct (first, next) = readMember index

            if next + 1 < content.Length && content[next] = '-' then
                let struct (last, after) = readMember (next + 1)

                if first < last then
                    if last <= 0xFFFF then
                        appendBmpRange first last
                    elif first >= 0x10000 then
                        appendAstralRange first last
                    else
                        if first <= 0xD7FF then
                            appendBmpRange first 0xD7FF

                        if first <= 0xD7FF then
                            appendBmpRange 0xE000 0xFFFF
                        else
                            appendBmpRange first 0xFFFF

                        appendAstralRange 0x10000 last
                else
                    appendScalar first

                index <- after
            else
                appendScalar first
                index <- next

        if astral.Count = 0 then
            if negated then
                if scalar then
                    "(?!/)(?>[\\uD800-\\uDBFF][\\uDC00-\\uDFFF]|(?!(?<=[\\uD800-\\uDBFF])[\\uDC00-\\uDFFF])(?![\\uD800-\\uDBFF][\\uDC00-\\uDFFF])[^"
                    + bmp.ToString()
                    + "])"
                else
                    "(?!/)" + "[^" + bmp.ToString() + "]"
            else
                "(?!/)" + "[" + bmp.ToString() + "]"
        else
            let alts = ResizeArray<string>(astral.Count + 1)

            if bmp.Length > 0 then
                alts.Add("[" + bmp.ToString() + "]")

            alts.AddRange astral

            let positive =
                if alts.Count = 1 then
                    alts[0]
                else
                    "(?:" + String.Join("|", alts) + ")"

            if negated then
                "(?!/)(?!"
                + positive
                + ")(?>[\\uD800-\\uDBFF][\\uDC00-\\uDFFF]|(?!(?<=[\\uD800-\\uDBFF])[\\uDC00-\\uDFFF])(?![\\uD800-\\uDBFF][\\uDC00-\\uDFFF])[\\u0000-\\uFFFF])"
            else
                "(?!/)" + positive

    let private compileWith alternatives tolerant (pattern: string) =
        let text = StringBuilder("^")
        let mutable index = 0
        let mutable braces = 0
        let mutable canBoundary = true
        let mutable canNonBoundary = false
        let braceStack = Stack<struct (bool * bool * bool * bool)>()
        let mutable malformed = false

        while not malformed && index < pattern.Length do
            match pattern[index] with
            | '\\' when index + 1 < pattern.Length ->
                index <- index + 1
                let isSlash = pattern[index] = '/'
                text.Append(Regex.Escape(string pattern[index])) |> ignore
                canBoundary <- isSlash
                canNonBoundary <- not isSlash
            | '*' ->
                let starStart = index

                while index + 1 < pattern.Length && pattern[index + 1] = '*' do
                    index <- index + 1

                let starCount = index - starStart + 1

                let isRightUnescapedSlash = index + 1 < pattern.Length && pattern[index + 1] = '/'

                let isRightEscapedSlash =
                    index + 2 < pattern.Length
                    && pattern[index + 1] = '\\'
                    && pattern[index + 2] = '/'

                let isDirGlob =
                    starCount >= 2
                    && (alternatives
                        || ((starStart = 0 || pattern[starStart - 1] = '/')
                            && (index + 1 = pattern.Length
                                || isRightUnescapedSlash
                                || isRightEscapedSlash)))

                if isDirGlob then
                    if isRightUnescapedSlash && canBoundary then
                        if not canNonBoundary then
                            text.Append("(?:[\\s\\S]*/)?") |> ignore
                        else
                            text.Append("(?:(?<=\\A|/)|[\\s\\S]*/)") |> ignore

                        index <- index + 1
                        canBoundary <- true
                        canNonBoundary <- false
                    else
                        text.Append("[\\s\\S]*") |> ignore
                        canBoundary <- true
                        canNonBoundary <- true
                else
                    text.Append("[^/]*") |> ignore
                    canNonBoundary <- true
            | '?' ->
                text.Append("[^/]") |> ignore
                canBoundary <- false
                canNonBoundary <- true
            | '[' ->
                let negated =
                    index + 1 < pattern.Length
                    && (pattern[index + 1] = '!' || pattern[index + 1] = '^')

                let first = if negated then index + 2 else index + 1
                let ending = classEnd pattern first

                if ending < 0 then
                    if tolerant then
                        text.Append("(?!)") |> ignore
                    else
                        invalidArg (nameof pattern) ("Unclosed glob character class: " + pattern)
                else
                    let scalar = alternatives || not tolerant

                    text.Append(
                        classPattern scalar negated (pattern.Substring(first, ending - first))
                    )
                    |> ignore

                    index <- ending

                canBoundary <- false
                canNonBoundary <- true
            | '{' when alternatives ->
                match tryMatchNumericRange pattern index with
                | ValueSome(struct (s1, len1, d1, s2, len2, d2, matchLen)) ->
                    if d1 > maximumRangeDigits || d2 > maximumRangeDigits then
                        if tolerant then
                            malformed <- true
                        else
                            invalidArg
                                (nameof pattern)
                                $"Glob numeric bounds may contain at most {maximumRangeDigits} digits."

                    if not malformed then
                        let first =
                            BigInteger.Parse(
                                pattern.AsSpan(s1, len1),
                                NumberStyles.AllowLeadingSign,
                                CultureInfo.InvariantCulture
                            )

                        let last =
                            BigInteger.Parse(
                                pattern.AsSpan(s2, len2),
                                NumberStyles.AllowLeadingSign,
                                CultureInfo.InvariantCulture
                            )

                        text.Append(rangePattern first last) |> ignore
                        index <- index + matchLen - 1
                        canBoundary <- false
                        canNonBoundary <- true
                | ValueNone ->
                    text.Append("(?:") |> ignore
                    braces <- braces + 1
                    braceStack.Push(struct (canBoundary, canNonBoundary, false, false))
            | '}' when braces > 0 ->
                text.Append(')') |> ignore
                braces <- braces - 1
                let struct (_, _, exitB, exitNB) = braceStack.Pop()
                canBoundary <- exitB || canBoundary
                canNonBoundary <- exitNB || canNonBoundary
            | ',' when braces > 0 ->
                text.Append('|') |> ignore
                let struct (entryB, entryNB, exitB, exitNB) = braceStack.Pop()

                braceStack.Push(
                    struct (entryB, entryNB, exitB || canBoundary, exitNB || canNonBoundary)
                )

                canBoundary <- entryB
                canNonBoundary <- entryNB
            | '/' ->
                text.Append('/') |> ignore
                canBoundary <- true
                canNonBoundary <- false
            | character ->
                text.Append(Regex.Escape(string character)) |> ignore
                canBoundary <- false
                canNonBoundary <- true

            index <- index + 1

        if malformed || braces <> 0 then
            if tolerant then
                Regex("(?!)", RegexOptions.CultureInvariant, TimeSpan.FromSeconds 1.)
            else
                invalidArg (nameof pattern) ("Unclosed glob alternatives: " + pattern)
        else
            text.Append("\\z") |> ignore
            Regex(text.ToString(), RegexOptions.CultureInvariant, TimeSpan.FromSeconds 1.)

    let private isMeta alternatives (c: char) =
        c = '\\'
        || c = '*'
        || c = '?'
        || c = '['
        || (alternatives && (c = '{' || c = '}'))

    let private isLiteral alternatives (s: ReadOnlySpan<char>) =
        let mutable ok = true
        let mutable i = 0

        while ok && i < s.Length do
            if isMeta alternatives s[i] then
                ok <- false

            i <- i + 1

        ok

    let private isSegmentLiteral alternatives (s: ReadOnlySpan<char>) =
        let mutable ok = true
        let mutable i = 0

        while ok && i < s.Length do
            let c = s[i]

            if c = '/' || isMeta alternatives c then
                ok <- false

            i <- i + 1

        ok

    let private tryDualSegment alternatives (s: ReadOnlySpan<char>) =
        if s.Length < 4 || s.IndexOf('[') < 0 then
            ValueNone
        else
            let p = StringBuilder(s.Length)
            let q = StringBuilder(s.Length)
            let mutable ok = true
            let mutable i = 0
            let mutable hasDual = false

            while ok && i < s.Length do
                let c = s[i]

                if c = '[' then
                    if i + 3 < s.Length && s[i + 3] = ']' then
                        let a = s[i + 1]
                        let b = s[i + 2]

                        if
                            a <> '!'
                            && a <> '^'
                            && a <> ']'
                            && a <> '\\'
                            && a <> '-'
                            && a <> '/'
                            && b <> ']'
                            && b <> '\\'
                            && b <> '-'
                            && b <> '/'
                            && not (Char.IsSurrogate a)
                            && not (Char.IsSurrogate b)
                        then
                            p.Append a |> ignore
                            q.Append b |> ignore
                            hasDual <- true
                            i <- i + 4
                        else
                            ok <- false
                    else
                        ok <- false
                elif c = '/' || isMeta alternatives c then
                    ok <- false
                else
                    p.Append c |> ignore
                    q.Append c |> ignore
                    i <- i + 1

            if ok && hasDual && p.Length > 0 then
                ValueSome(struct (p.ToString(), q.ToString()))
            else
                ValueNone

    let private matchesDual (s: ReadOnlySpan<char>) (p: string) (q: string) =
        if s.Length <> p.Length then
            false
        else
            let mutable i = 0
            let mutable ok = true

            while ok && i < p.Length do
                let ch = s[i]

                if ch <> p[i] && ch <> q[i] then
                    ok <- false

                i <- i + 1

            ok

    let private tryBraceSuffixes (body: ReadOnlySpan<char>) =
        if
            body.Length = 0
            || body.IndexOf('{') < 0
            || body.Contains("..".AsSpan(), StringComparison.Ordinal)
            || body.Contains("**".AsSpan(), StringComparison.Ordinal)
        then
            ValueNone
        else
            let mutable valid = true
            let mutable i = 0

            while valid && i < body.Length do
                let c = body[i]

                if c = '/' || c = '\\' || c = '?' || c = '[' then
                    valid <- false

                i <- i + 1

            if not valid then
                ValueNone
            else
                let mutable acc = [| "" |]
                let mutable pos = 0

                while valid && pos < body.Length do
                    if body[pos] = '{' then
                        let start = pos + 1
                        let mutable close = start

                        while close < body.Length && body[close] <> '}' && body[close] <> '{' do
                            close <- close + 1

                        if close >= body.Length || body[close] <> '}' then
                            valid <- false
                        else
                            let inner = String(body.Slice(start, close - start))
                            let branches = inner.Split(',')

                            if acc.Length * branches.Length > 32 then
                                valid <- false
                            else
                                let next = Array.zeroCreate<string>(acc.Length * branches.Length)
                                let mutable k = 0

                                for prefix in acc do
                                    for branch in branches do
                                        next[k] <- prefix + branch
                                        k <- k + 1

                                acc <- next
                                pos <- close + 1
                    elif body[pos] = '}' then
                        valid <- false
                    else
                        let start = pos

                        while pos < body.Length && body[pos] <> '{' && body[pos] <> '}' do
                            pos <- pos + 1

                        let lit = String(body.Slice(start, pos - start))

                        for j = 0 to acc.Length - 1 do
                            acc[j] <- acc[j] + lit

                if not valid || acc.Length = 0 then
                    ValueNone
                elif acc |> Array.forall (fun s -> s.Length > 0 && s.IndexOf('*') < 0) then
                    ValueSome
                        {
                            Kind = FastGlobKind.AnySuffixes
                            Flags = 0uy
                            Expanded = ""
                            Primary = ""
                            Secondary = ""
                            Tertiary = ""
                            Suffixes = acc
                            Required = ""
                            SegmentLength = 0
                        }
                elif
                    acc
                    |> Array.forall (fun s ->
                        let star = s.LastIndexOf('*')
                        star < s.Length - 1)
                then
                    let suffixes =
                        acc
                        |> Array.map (fun s ->
                            let star = s.LastIndexOf('*')
                            if star < 0 then s else s.Substring(star + 1))

                    ValueSome
                        {
                            Kind = FastGlobKind.Guarded
                            Flags = 0uy
                            Expanded = ""
                            Primary = ""
                            Secondary = ""
                            Tertiary = ""
                            Suffixes = suffixes
                            Required = ""
                            SegmentLength = 0
                        }
                else
                    ValueNone

    let private segmentAtoms (tail: string) =
        let mutable count = 0
        let mutable index = 0
        let mutable fixedLength = true

        while fixedLength && index < tail.Length do
            match tail[index] with
            | '\\' when index + 1 < tail.Length ->
                index <- index + 2
                count <- count + 1
            | '[' ->
                let negated =
                    index + 1 < tail.Length && (tail[index + 1] = '!' || tail[index + 1] = '^')

                let first = if negated then index + 2 else index + 1
                let ending = classEnd tail first

                if ending < 0 || negated then
                    fixedLength <- false
                else
                    let mutable hasSurrogate = false
                    let mutable k = first

                    while not hasSurrogate && k < ending do
                        if Char.IsSurrogate tail[k] then
                            hasSurrogate <- true

                        k <- k + 1

                    if hasSurrogate then
                        fixedLength <- false
                    else
                        index <- ending + 1
                        count <- count + 1
            | _ ->
                index <- index + 1
                count <- count + 1

        if fixedLength then count else 0

    let private extractGuards alternatives (pattern: string) =
        if alternatives && pattern.IndexOf('{') >= 0 then
            {
                Kind = FastGlobKind.Guarded
                Flags = 0uy
                Expanded = pattern
                Primary = ""
                Secondary = ""
                Tertiary = ""
                Suffixes = null
                Required = ""
                SegmentLength = 0
            }
        else
            let mutable prefixEnd = 0

            while prefixEnd < pattern.Length && not (isMeta alternatives pattern[prefixEnd]) do
                prefixEnd <- prefixEnd + 1

            let reqPrefix =
                if prefixEnd > 0 then
                    pattern.Substring(0, prefixEnd)
                else
                    ""

            let lastSlash = pattern.LastIndexOf('/')
            let mutable index = 0
            let mutable valid = true
            let mutable currentRunStart = 0
            let mutable longestSegStart = 0
            let mutable longestSegLen = 0
            let mutable longestRunStart = 0
            let mutable longestRunLen = 0
            let mutable segHasDoubleStar = false

            while valid && index < pattern.Length do
                match pattern[index] with
                | '\\' when index + 1 < pattern.Length ->
                    index <- index + 2
                    currentRunStart <- index
                | '*' ->
                    if index + 1 < pattern.Length && pattern[index + 1] = '*' then
                        if index > lastSlash then
                            segHasDoubleStar <- true

                        index <- index + 2

                        if index < pattern.Length && pattern[index] = '/' then
                            index <- index + 1
                    else
                        index <- index + 1

                    currentRunStart <- index
                | '?' ->
                    index <- index + 1
                    currentRunStart <- index
                | '[' ->
                    let negated =
                        index + 1 < pattern.Length
                        && (pattern[index + 1] = '!' || pattern[index + 1] = '^')

                    let first = if negated then index + 2 else index + 1
                    let ending = classEnd pattern first

                    if ending < 0 then
                        valid <- false
                    else
                        index <- ending + 1
                        currentRunStart <- index
                | '/' ->
                    index <- index + 1
                    currentRunStart <- index
                | _ ->
                    index <- index + 1
                    let runLen = index - currentRunStart

                    if runLen > longestRunLen then
                        longestRunStart <- currentRunStart
                        longestRunLen <- runLen

                    if currentRunStart > lastSlash && runLen > longestSegLen then
                        longestSegStart <- currentRunStart
                        longestSegLen <- runLen

            if not valid then
                {
                    Kind = FastGlobKind.Guarded
                    Flags = 0uy
                    Expanded = pattern
                    Primary = ""
                    Secondary = ""
                    Tertiary = ""
                    Suffixes = null
                    Required = ""
                    SegmentLength = 0
                }
            else
                let reqSuffix =
                    if currentRunStart < pattern.Length then
                        pattern.Substring(currentRunStart)
                    else
                        ""

                let reqSegment =
                    if not segHasDoubleStar && longestSegLen > 0 then
                        let seg = pattern.Substring(longestSegStart, longestSegLen)

                        if
                            reqSuffix.Length > 0
                            && reqSuffix.Contains(seg, StringComparison.Ordinal)
                        then
                            ""
                        else
                            seg
                    else
                        ""

                let required =
                    if longestRunLen = 0 then
                        ""
                    else
                        let run = pattern.Substring(longestRunStart, longestRunLen)

                        if
                            reqPrefix.Contains(run, StringComparison.Ordinal)
                            || reqSuffix.Contains(run, StringComparison.Ordinal)
                            || reqSegment.Contains(run, StringComparison.Ordinal)
                        then
                            ""
                        else
                            run

                let segmentLength =
                    if
                        pattern.StartsWith("**/", StringComparison.Ordinal)
                        && pattern.IndexOf('/', 3) < 0
                        && pattern.IndexOf('*', 3) < 0
                    then
                        segmentAtoms (pattern.Substring 3)
                    else
                        0

                {
                    Kind = FastGlobKind.Guarded
                    Flags = 0uy
                    Expanded = pattern
                    Primary = reqPrefix
                    Secondary = reqSuffix
                    Tertiary = reqSegment
                    Suffixes = null
                    Required = required
                    SegmentLength = segmentLength
                }

    let fastCompileWithFlags alternatives tolerant (pattern: string) =
        let flags = (if alternatives then 1uy else 0uy) ||| (if tolerant then 2uy else 0uy)

        let raw =
            if pattern = "**" || pattern = "**/*" then
                {
                    Kind = FastGlobKind.AnyNoNewline
                    Flags = flags
                    Expanded = pattern
                    Primary = ""
                    Secondary = ""
                    Tertiary = ""
                    Suffixes = null
                    Required = ""
                    SegmentLength = 0
                }
            elif isLiteral alternatives (pattern.AsSpan()) then
                {
                    Kind = FastGlobKind.Exact
                    Flags = flags
                    Expanded = pattern
                    Primary = pattern
                    Secondary = ""
                    Tertiary = ""
                    Suffixes = null
                    Required = ""
                    SegmentLength = 0
                }
            elif pattern.StartsWith("**/", StringComparison.Ordinal) then
                let tail = pattern.AsSpan(3)

                if tail.Length > 0 && isSegmentLiteral alternatives tail then
                    {
                        Kind = FastGlobKind.AnySegment
                        Flags = flags
                        Expanded = pattern
                        Primary = String(tail)
                        Secondary = ""
                        Tertiary = ""
                        Suffixes = null
                        Required = ""
                        SegmentLength = 0
                    }
                elif
                    tail.Length >= 2
                    && tail[0] = '*'
                    && isSegmentLiteral alternatives (tail.Slice(1))
                then
                    {
                        Kind = FastGlobKind.AnySuffix
                        Flags = flags
                        Expanded = pattern
                        Primary = String(tail.Slice(1))
                        Secondary = ""
                        Tertiary = ""
                        Suffixes = null
                        Required = ""
                        SegmentLength = 0
                    }
                elif
                    tail.Length >= 2
                    && tail[tail.Length - 1] = '*'
                    && isSegmentLiteral alternatives (tail.Slice(0, tail.Length - 1))
                then
                    {
                        Kind = FastGlobKind.AnySegmentPrefix
                        Flags = flags
                        Expanded = pattern
                        Primary = String(tail.Slice(0, tail.Length - 1))
                        Secondary = ""
                        Tertiary = ""
                        Suffixes = null
                        Required = ""
                        SegmentLength = 0
                    }
                elif
                    tail.Length >= 3
                    && tail[0] = '*'
                    && tail[tail.Length - 1] = '*'
                    && isSegmentLiteral alternatives (tail.Slice(1, tail.Length - 2))
                then
                    {
                        Kind = FastGlobKind.AnySegmentContains
                        Flags = flags
                        Expanded = pattern
                        Primary = String(tail.Slice(1, tail.Length - 2))
                        Secondary = ""
                        Tertiary = ""
                        Suffixes = null
                        Required = ""
                        SegmentLength = 0
                    }
                else
                    let star = tail.IndexOf('*')

                    if
                        star > 0
                        && star < tail.Length - 1
                        && isSegmentLiteral alternatives (tail.Slice(0, star))
                        && isSegmentLiteral alternatives (tail.Slice(star + 1))
                    then
                        {
                            Kind = FastGlobKind.AnySegmentPrefixSuffix
                            Flags = flags
                            Expanded = pattern
                            Primary = String(tail.Slice(0, star))
                            Secondary = String(tail.Slice(star + 1))
                            Tertiary = ""
                            Suffixes = null
                            Required = ""
                            SegmentLength = 0
                        }
                    elif alternatives && tail.Length >= 4 && tail[0] = '*' then
                        match tryBraceSuffixes (tail.Slice(1)) with
                        | ValueSome fast ->
                            { fast with
                                Flags = flags
                                Expanded = pattern
                            }
                        | ValueNone ->
                            { (extractGuards alternatives pattern) with
                                Flags = flags
                            }
                    else
                        let dual =
                            if star < 0 then
                                match tryDualSegment alternatives tail with
                                | ValueSome(struct (p, q)) ->
                                    ValueSome(FastGlobKind.AnyDualSegment, p, q)
                                | ValueNone -> ValueNone
                            elif star = 0 && tail.Slice(1).IndexOf('*') < 0 then
                                match tryDualSegment alternatives (tail.Slice(1)) with
                                | ValueSome(struct (p, q)) ->
                                    ValueSome(FastGlobKind.AnyDualSuffix, p, q)
                                | ValueNone -> ValueNone
                            elif star = tail.Length - 1 then
                                match
                                    tryDualSegment alternatives (tail.Slice(0, tail.Length - 1))
                                with
                                | ValueSome(struct (p, q)) ->
                                    ValueSome(FastGlobKind.AnyDualSegmentPrefix, p, q)
                                | ValueNone -> ValueNone
                            else
                                ValueNone

                        match dual with
                        | ValueSome(kind, p, q) ->
                            {
                                Kind = kind
                                Flags = flags
                                Expanded = pattern
                                Primary = p
                                Secondary = q
                                Tertiary = ""
                                Suffixes = null
                                Required = ""
                                SegmentLength = 0
                            }
                        | ValueNone ->
                            { (extractGuards alternatives pattern) with
                                Flags = flags
                            }
            else
                { (extractGuards alternatives pattern) with
                    Flags = flags
                }

        raw

    let fastCompile alternatives (pattern: string) =
        fastCompileWithFlags alternatives true pattern

    let hasNewline (relative: string) = relative.IndexOf('\n') >= 0

    let ensureRegex (regex: byref<Regex>) (fast: FastGlob) =
        match Volatile.Read(&regex) with
        | null ->
            let compiled =
                compileWith
                    ((fast.Flags &&& 1uy) <> 0uy)
                    ((fast.Flags &&& 2uy) <> 0uy)
                    fast.Expanded

            let prev = Interlocked.CompareExchange(&regex, compiled, null)
            if isNull prev then compiled else prev
        | existing -> existing

    let isMatchScanned (newline: bool) (fast: FastGlob) (regex: byref<Regex>) (relative: string) =
        if newline then
            (ensureRegex &regex fast).IsMatch relative
        else
            match fast.Kind with
            | FastGlobKind.AnyNoNewline -> true
            | FastGlobKind.Exact -> String.Equals(relative, fast.Primary, StringComparison.Ordinal)
            | FastGlobKind.AnySuffix -> relative.EndsWith(fast.Primary, StringComparison.Ordinal)
            | FastGlobKind.AnySuffixes ->
                let suffixes = fast.Suffixes
                let mutable matched = false
                let mutable i = 0

                while not matched && i < suffixes.Length do
                    if relative.EndsWith(suffixes[i], StringComparison.Ordinal) then
                        matched <- true

                    i <- i + 1

                matched
            | FastGlobKind.AnySegment ->
                let seg = fast.Primary

                relative.EndsWith(seg, StringComparison.Ordinal)
                && (relative.Length = seg.Length || relative[relative.Length - seg.Length - 1] = '/')
            | FastGlobKind.AnySegmentPrefix ->
                let lastSlash = relative.LastIndexOf('/')

                let segment =
                    if lastSlash < 0 then
                        relative.AsSpan()
                    else
                        relative.AsSpan(lastSlash + 1)

                segment.StartsWith(fast.Primary.AsSpan(), StringComparison.Ordinal)
            | FastGlobKind.AnySegmentPrefixSuffix ->
                let lastSlash = relative.LastIndexOf('/')

                let segment =
                    if lastSlash < 0 then
                        relative.AsSpan()
                    else
                        relative.AsSpan(lastSlash + 1)

                let prefix = fast.Primary
                let suffix = fast.Secondary

                segment.Length >= prefix.Length + suffix.Length
                && segment.StartsWith(prefix.AsSpan(), StringComparison.Ordinal)
                && segment.EndsWith(suffix.AsSpan(), StringComparison.Ordinal)
            | FastGlobKind.AnySegmentContains ->
                let lastSlash = relative.LastIndexOf('/')

                let segment =
                    if lastSlash < 0 then
                        relative.AsSpan()
                    else
                        relative.AsSpan(lastSlash + 1)

                segment.Contains(fast.Primary.AsSpan(), StringComparison.Ordinal)
            | FastGlobKind.AnyDualSegment ->
                let lastSlash = relative.LastIndexOf('/')

                let segment =
                    if lastSlash < 0 then
                        relative.AsSpan()
                    else
                        relative.AsSpan(lastSlash + 1)

                matchesDual segment fast.Primary fast.Secondary
            | FastGlobKind.AnyDualSegmentPrefix ->
                let lastSlash = relative.LastIndexOf('/')

                let segment =
                    if lastSlash < 0 then
                        relative.AsSpan()
                    else
                        relative.AsSpan(lastSlash + 1)

                let p = fast.Primary

                segment.Length >= p.Length
                && matchesDual (segment.Slice(0, p.Length)) p fast.Secondary
            | FastGlobKind.AnyDualSuffix ->
                let p = fast.Primary

                relative.Length >= p.Length
                && matchesDual (relative.AsSpan(relative.Length - p.Length)) p fast.Secondary
            | _ ->
                let prefix = fast.Primary
                let suffix = fast.Secondary
                let segContains = fast.Tertiary

                if
                    prefix.Length > 0 && not (relative.StartsWith(prefix, StringComparison.Ordinal))
                then
                    false
                elif
                    suffix.Length > 0 && not (relative.EndsWith(suffix, StringComparison.Ordinal))
                then
                    false
                elif
                    segContains.Length > 0
                    && (let lastSlash = relative.LastIndexOf('/')

                        let segment =
                            if lastSlash < 0 then
                                relative.AsSpan()
                            else
                                relative.AsSpan(lastSlash + 1)

                        not (segment.Contains(segContains.AsSpan(), StringComparison.Ordinal)))
                then
                    false
                elif
                    fast.Required.Length > 0
                    && not (relative.Contains(fast.Required, StringComparison.Ordinal))
                then
                    false
                elif
                    fast.SegmentLength > 0
                    && relative.Length - relative.LastIndexOf('/') - 1 <> fast.SegmentLength
                then
                    false
                elif not (isNull fast.Suffixes) then
                    let suffixes = fast.Suffixes
                    let mutable anySuffix = false
                    let mutable i = 0

                    while not anySuffix && i < suffixes.Length do
                        if relative.EndsWith(suffixes[i], StringComparison.Ordinal) then
                            anySuffix <- true

                        i <- i + 1

                    anySuffix && (ensureRegex &regex fast).IsMatch relative
                else
                    (ensureRegex &regex fast).IsMatch relative

    let private equalsNormalized (span: ReadOnlySpan<char>) (pattern: string) =
        if span.Length <> pattern.Length then
            false
        elif Path.DirectorySeparatorChar = '/' then
            span.SequenceEqual(pattern.AsSpan())
        else
            let mutable i = 0
            let mutable ok = true

            while ok && i < pattern.Length do
                let c = span[i]
                let p = pattern[i]

                if c <> p && not (p = '/' && c = '\\') then
                    ok <- false

                i <- i + 1

            ok

    let private startsWithNormalized (span: ReadOnlySpan<char>) (prefix: string) =
        if span.Length < prefix.Length then
            false
        elif Path.DirectorySeparatorChar = '/' then
            span.StartsWith(prefix.AsSpan(), StringComparison.Ordinal)
        else
            let mutable i = 0
            let mutable ok = true

            while ok && i < prefix.Length do
                let c = span[i]
                let p = prefix[i]

                if c <> p && not (p = '/' && c = '\\') then
                    ok <- false

                i <- i + 1

            ok

    let private isMatchRegexSpan
        (regex: byref<Regex>)
        (fast: FastGlob)
        (relative: ReadOnlySpan<char>)
        =
        let rx = ensureRegex &regex fast

        if Path.DirectorySeparatorChar = '\\' && relative.IndexOf('\\') >= 0 then
            rx.IsMatch(String(relative).Replace('\\', '/'))
        else
            rx.IsMatch relative

    let isMatchSpan
        (fast: FastGlob)
        (regex: byref<Regex>)
        (relative: ReadOnlySpan<char>)
        (segment: ReadOnlySpan<char>)
        =
        match fast.Kind with
        | FastGlobKind.AnyNoNewline -> true
        | FastGlobKind.Exact -> equalsNormalized relative fast.Primary
        | FastGlobKind.AnySuffix ->
            relative.EndsWith(fast.Primary.AsSpan(), StringComparison.Ordinal)
        | FastGlobKind.AnySuffixes ->
            let suffixes = fast.Suffixes
            let mutable matched = false
            let mutable i = 0

            while not matched && i < suffixes.Length do
                if relative.EndsWith(suffixes[i].AsSpan(), StringComparison.Ordinal) then
                    matched <- true

                i <- i + 1

            matched
        | FastGlobKind.AnySegment -> segment.SequenceEqual(fast.Primary.AsSpan())
        | FastGlobKind.AnySegmentPrefix ->
            segment.StartsWith(fast.Primary.AsSpan(), StringComparison.Ordinal)
        | FastGlobKind.AnySegmentPrefixSuffix ->
            let prefix = fast.Primary
            let suffix = fast.Secondary

            segment.Length >= prefix.Length + suffix.Length
            && segment.StartsWith(prefix.AsSpan(), StringComparison.Ordinal)
            && segment.EndsWith(suffix.AsSpan(), StringComparison.Ordinal)
        | FastGlobKind.AnySegmentContains ->
            segment.Contains(fast.Primary.AsSpan(), StringComparison.Ordinal)
        | FastGlobKind.AnyDualSegment -> matchesDual segment fast.Primary fast.Secondary
        | FastGlobKind.AnyDualSegmentPrefix ->
            let p = fast.Primary

            segment.Length >= p.Length
            && matchesDual (segment.Slice(0, p.Length)) p fast.Secondary
        | FastGlobKind.AnyDualSuffix ->
            let p = fast.Primary

            relative.Length >= p.Length
            && matchesDual (relative.Slice(relative.Length - p.Length)) p fast.Secondary
        | _ ->
            let prefix = fast.Primary
            let suffix = fast.Secondary
            let segContains = fast.Tertiary

            if prefix.Length > 0 && not (startsWithNormalized relative prefix) then
                false
            elif
                suffix.Length > 0
                && not (relative.EndsWith(suffix.AsSpan(), StringComparison.Ordinal))
            then
                false
            elif
                segContains.Length > 0
                && not (segment.Contains(segContains.AsSpan(), StringComparison.Ordinal))
            then
                false
            elif
                fast.Required.Length > 0
                && not (relative.Contains(fast.Required.AsSpan(), StringComparison.Ordinal))
            then
                false
            elif fast.SegmentLength > 0 && segment.Length <> fast.SegmentLength then
                false
            elif not (isNull fast.Suffixes) then
                let suffixes = fast.Suffixes
                let mutable anySuffix = false
                let mutable i = 0

                while not anySuffix && i < suffixes.Length do
                    if relative.EndsWith(suffixes[i].AsSpan(), StringComparison.Ordinal) then
                        anySuffix <- true

                    i <- i + 1

                anySuffix && isMatchRegexSpan &regex fast relative
            else
                isMatchRegexSpan &regex fast relative

    let isMatch (fast: FastGlob) (regex: Regex) (relative: string) =
        let mutable rx = regex
        isMatchScanned (hasNewline relative) fast &rx relative

    let compile pattern = compileWith true false pattern
    let compileIgnore pattern = compileWith false false pattern

    let compileGitIgnore pattern = compileWith false true pattern

    let compileEditorConfig pattern = compileWith true true pattern

    let isCanonicalUnixPath (path: string) =
        if path.IndexOf('\\') >= 0 then
            false
        else
            let mutable ok = true
            let mutable i = path.IndexOf('/')

            while ok && i >= 0 do
                if i + 1 < path.Length then
                    let next = path[i + 1]

                    if next = '/' then
                        ok <- false
                    elif next = '.' then
                        if
                            i + 2 = path.Length
                            || path[i + 2] = '/'
                            || (path[i + 2] = '.' && (i + 3 = path.Length || path[i + 3] = '/'))
                        then
                            ok <- false

                i <-
                    if ok && i + 1 < path.Length then
                        path.IndexOf('/', i + 1)
                    else
                        -1

            ok

    let isCanonicalWindowsPath (path: string) =
        if
            path.Length < 4
            || not ((path[0] >= 'A' && path[0] <= 'Z') || (path[0] >= 'a' && path[0] <= 'z'))
            || path[1] <> ':'
            || path[2] <> '\\'
            || path.IndexOf('/') >= 0
        then
            false
        else
            let mutable ok = true
            let mutable i = 2

            while ok && i >= 0 do
                if i + 1 < path.Length then
                    let next = path[i + 1]

                    if next = '\\' then
                        ok <- false
                    elif next = '.' then
                        if
                            i + 2 = path.Length
                            || path[i + 2] = '\\'
                            || (path[i + 2] = '.' && (i + 3 = path.Length || path[i + 3] = '\\'))
                        then
                            ok <- false

                i <-
                    if ok && i + 1 < path.Length then
                        path.IndexOf('\\', i + 1)
                    else
                        -1

            ok

    let isCanonicalNativePath (path: string) =
        if Path.DirectorySeparatorChar = '/' then
            path.Length > 1
            && path[0] = '/'
            && path[path.Length - 1] <> '/'
            && isCanonicalUnixPath path
        else
            Path.DirectorySeparatorChar = '\\'
            && path.Length >= 4
            && path[path.Length - 1] <> '\\'
            && isCanonicalWindowsPath path

    let isCanonicalChildPath (directory: string) (path: string) =
        if Path.DirectorySeparatorChar = '/' then
            directory.Length > 1
            && directory[0] = '/'
            && directory[directory.Length - 1] <> '/'
            && path.Length > directory.Length + 1
            && path[directory.Length] = '/'
            && path[path.Length - 1] <> '/'
            && path.StartsWith(directory, StringComparison.Ordinal)
            && isCanonicalUnixPath path
        else
            Path.DirectorySeparatorChar = '\\'
            && directory.Length >= 4
            && directory[directory.Length - 1] <> '\\'
            && path.Length > directory.Length + 1
            && path[directory.Length] = '\\'
            && path[path.Length - 1] <> '\\'
            && path.StartsWith(directory, StringComparison.Ordinal)
            && isCanonicalWindowsPath path

    let relative (directory: string) (path: string) =
        if isCanonicalChildPath directory path then
            let sub = path.Substring(directory.Length + 1)

            Some(
                if Path.DirectorySeparatorChar = '\\' then
                    sub.Replace('\\', '/')
                else
                    sub
            )
        else
            let result = Path.GetRelativePath(directory, path) |> normalize

            if
                result = ".."
                || result.StartsWith("../", StringComparison.Ordinal)
                || Path.IsPathRooted result
            then
                None
            else
                Some result

    let private suffixCompatibleWithCs (suffix: string) =
        if suffix.Length = 0 then
            true
        elif suffix.Length <= 3 then
            ".cs".EndsWith(suffix, StringComparison.Ordinal)
        else
            suffix.EndsWith(".cs", StringComparison.Ordinal)

    let private dualSuffixCompatibleWithCs (p: string) (q: string) =
        let cs = ".cs"
        let n = min 3 p.Length
        let mutable ok = true

        for k = 1 to n do
            let target = cs[3 - k]

            if p[p.Length - k] <> target && q[q.Length - k] <> target then
                ok <- false

        ok

    let canMatchLowercaseCs (fast: FastGlob) =
        match fast.Kind with
        | FastGlobKind.Exact
        | FastGlobKind.AnySuffix
        | FastGlobKind.AnySegment -> suffixCompatibleWithCs fast.Primary
        | FastGlobKind.AnyDualSegment ->
            fast.Primary.Length >= 3
            && dualSuffixCompatibleWithCs fast.Primary fast.Secondary
        | FastGlobKind.AnyDualSuffix -> dualSuffixCompatibleWithCs fast.Primary fast.Secondary
        | FastGlobKind.AnySegmentPrefixSuffix -> suffixCompatibleWithCs fast.Secondary
        | FastGlobKind.AnySuffixes -> fast.Suffixes |> Array.exists suffixCompatibleWithCs
        | FastGlobKind.Guarded ->
            (fast.Secondary.Length = 0 || suffixCompatibleWithCs fast.Secondary)
            && (isNull fast.Suffixes || (fast.Suffixes |> Array.exists suffixCompatibleWithCs))
        | _ -> true

    let alwaysMatchesLowercaseCs (fast: FastGlob) =
        match fast.Kind with
        | FastGlobKind.AnyNoNewline -> true
        | FastGlobKind.AnySuffix ->
            fast.Primary.Length <= 3
            && ".cs".EndsWith(fast.Primary, StringComparison.Ordinal)
        | FastGlobKind.AnySuffixes ->
            fast.Suffixes
            |> Array.exists (fun s -> s.Length <= 3 && ".cs".EndsWith(s, StringComparison.Ordinal))
        | _ -> false

    let filePattern (pattern: string) =
        compile (
            if pattern.Contains('/') then
                pattern.TrimStart('/')
            else
                "**/" + pattern
        )

    let private expandSection (pattern: string) =
        if pattern.Contains('/') then
            pattern.TrimStart('/')
        else
            "**/" + pattern

    let filePatternWithFast (pattern: string) =
        let expanded = expandSection pattern
        let regex = compile expanded
        let fast = fastCompile true expanded
        regex, fast

    let editorConfigPatternWithFast (pattern: string) =
        let expanded = expandSection pattern
        let fast = fastCompileWithFlags true true expanded
        (null: Regex), fast
