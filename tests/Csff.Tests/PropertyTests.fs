module Csff.Tests.PropertyTests

open System
open System.Collections.Generic
open System.IO
open System.Security.Cryptography
open System.Text
open Csff.Cli
open Csff.Conformance
open Csff.Printer
open Expecto
open FsCheck
open FsCheck.FSharp

let private config cases seed =
    { FsCheckConfig.defaultConfig with
        maxTest = cases
        replay = Some(seed, 11400714819323198485UL, None)
    }

let private withDirectory action =
    let directory =
        Path.Combine(Path.GetTempPath(), "csff-property-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory directory |> ignore

    try
        action directory
    finally
        Directory.Delete(directory, true)

let private anyCharacter =
    Gen.oneof
        [
            Gen.elements [ 'a' .. 'z' ]
            Gen.elements [ '0' .. '9' ]
            Gen.elements [ ' '; '\t'; '"'; '{'; '}'; '/'; '\\' ]
            Gen.elements [ 'ᄀ'; '〈'; '〉'; '一'; '가'; '豈' ]
            Gen.elements [ '︐'; '︰'; '＀'; '￠' ]
            Gen.elements [ '〿'; '힤'; '\ud83d'; '\ude00' ]
        ]

let private anyText = Gen.listOf anyCharacter |> Gen.map (List.toArray >> String)

let private widthProperties =
    [
        testPropertyWithConfig
            (config 500 20261008UL)
            "printed width sums the oracle's per-character widths"
            (Prop.forAll (Arb.fromGen anyText) (fun text ->
                let expected = text |> Seq.sumBy PrintedWidth.character

                Expect.equal
                    (PrintedWidth.measure (text.AsSpan()))
                    expected
                    "Measuring a span equals summing its code units."))
        testPropertyWithConfig
            (config 500 20261009UL)
            "printed width is additive over concatenation"
            (Prop.forAll (Arb.fromGen (Gen.two anyText)) (fun (left, right) ->
                Expect.equal
                    (PrintedWidth.measure ((left + right).AsSpan()))
                    (PrintedWidth.measure (left.AsSpan()) + PrintedWidth.measure (right.AsSpan()))
                    "A join costs exactly its two halves."))
        testPropertyWithConfig
            (config 300 20261010UL)
            "printed width equals the length below the wide threshold"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.listOf (
                        Gen.oneof [ Gen.elements [ 'a' .. 'z' ]; Gen.elements [ '0' .. '9' ] ]
                    )
                    |> Gen.map (List.toArray >> String)
                ))
                (fun text ->
                    Expect.equal
                        (PrintedWidth.measure (text.AsSpan()))
                        (uint32 text.Length)
                        "Every ASCII code unit has width one."))
        testPropertyWithConfig
            (config 300 20261011UL)
            "printed width stays between the length and twice the length"
            (Prop.forAll (Arb.fromGen anyText) (fun text ->
                let width = PrintedWidth.measure (text.AsSpan())

                Expect.isGreaterThanOrEqual
                    width
                    (uint32 text.Length)
                    "No character is narrower than one."

                Expect.isLessThanOrEqual
                    width
                    (uint32 (2 * text.Length))
                    "No character is wider than two."))
    ]

let private literalCharacter =
    Gen.oneof
        [
            Gen.elements [ 'a' .. 'z' ]
            Gen.elements [ 'A' .. 'Z' ]
            Gen.elements [ '0' .. '9' ]
            Gen.elements [ '.'; '-'; '_'; '+'; '('; ')'; '^'; '$'; '|'; '#' ]
        ]

let private literal =
    Gen.nonEmptyListOf literalCharacter |> Gen.map (List.toArray >> String)

let private segment =
    Gen.nonEmptyListOf (Gen.oneof [ Gen.elements [ 'a' .. 'z' ]; Gen.elements [ '0' .. '9' ] ])
    |> Gen.map (List.toArray >> String)

let private classCharacter =
    Gen.elements [ 'a'; 'b'; 'z'; '0'; '9'; ']'; '-'; '^'; '!'; '*'; '['; '.'; '\\'; 'd' ]

let private globProperties =
    [
        testPropertyWithConfig
            (config 400 20261012UL)
            "a literal glob matches its own text and nothing longer"
            (Prop.forAll (Arb.fromGen (Gen.two literal)) (fun (text, other) ->
                let pattern = Glob.compile text
                Expect.isTrue (pattern.IsMatch text) $"{text} matches itself."
                Expect.isFalse (pattern.IsMatch(text + "x")) "A literal is anchored at the end."
                Expect.isFalse (pattern.IsMatch("x" + text)) "A literal is anchored at the start."

                if other <> text then
                    Expect.isFalse (pattern.IsMatch other) $"{text} does not match {other}."))
        testPropertyWithConfig
            (config 400 20261013UL)
            "a star matches within one segment and a double star crosses them"
            (Prop.forAll (Arb.fromGen (Gen.nonEmptyListOf segment)) (fun segments ->
                let path = String.Join("/", segments)
                let single = Glob.compile "*"
                let double = Glob.compile "**"

                Expect.equal
                    (single.IsMatch path)
                    (segments.Length = 1)
                    "A star never crosses a separator."

                Expect.isTrue (double.IsMatch path) "A double star crosses every separator."

                let last = List.last segments

                Expect.isTrue
                    ((Glob.compile ("**/" + last)).IsMatch path)
                    "Any prefix is optional."

                Expect.isFalse
                    ((Glob.compile ("**/" + last)).IsMatch(path + "x"))
                    "The anchored segment still has to match in full."))
        testPropertyWithConfig
            (config 400 20261014UL)
            "a question mark matches exactly one character other than the separator"
            (Prop.forAll (Arb.fromGen segment) (fun text ->
                let pattern = Glob.compile "?"
                Expect.equal (pattern.IsMatch text) (text.Length = 1) "One character, not a run."
                Expect.isFalse (pattern.IsMatch "/") "The separator is excluded."

                Expect.isTrue
                    ((Glob.compile (String('?', text.Length))).IsMatch text)
                    "One per character."))
        testPropertyWithConfig
            (config 400 20261015UL)
            "brace alternatives match exactly their branches"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.map2
                        (fun branches other -> branches, other)
                        (Gen.nonEmptyListOf literal)
                        literal
                ))
                (fun (branches, other) ->
                    let pattern = Glob.compile ("{" + String.Join(",", branches) + "}")

                    for branch in branches do
                        Expect.isTrue (pattern.IsMatch branch) $"{branch} is a branch."

                    if not (List.contains other branches) then
                        Expect.isFalse (pattern.IsMatch other) $"{other} is not a branch."))
        testPropertyWithConfig
            (config 600 20261016UL)
            "a numeric range matches exactly the integers it spans"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! first = Gen.choose (-400, 400)
                        let! last = Gen.choose (-400, 400)
                        let! probe = Gen.choose (-500, 500)
                        return first, last, probe
                    }
                ))
                (fun (first, last, probe) ->
                    let pattern = Glob.compile $"{{{first}..{last}}}"
                    let low, high = min first last, max first last

                    Expect.equal
                        (pattern.IsMatch(string probe))
                        (probe >= low && probe <= high)
                        $"{probe} against {{{first}..{last}}}."))
        testPropertyWithConfig
            (config 400 20261017UL)
            "a numeric range rejects non-canonical decimals"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! first = Gen.choose (0, 200)
                        let! last = Gen.choose (201, 400)
                        let! zeros = Gen.choose (1, 3)
                        let! probe = Gen.choose (first, last)
                        return first, last, zeros, probe
                    }
                ))
                (fun (first, last, zeros, probe) ->
                    let pattern = Glob.compile $"{{{first}..{last}}}"
                    Expect.isTrue (pattern.IsMatch(string probe)) $"{probe} is in range."

                    Expect.isFalse
                        (pattern.IsMatch(String('0', zeros) + string probe))
                        "Leading zeros are not a canonical decimal form."

                    Expect.isFalse (pattern.IsMatch "-0") "Negative zero is not canonical."))
        testPropertyWithConfig
            (config 300 20261018UL)
            "a backslash escapes any glob metacharacter"
            (Prop.forAll
                (Arb.fromGen (Gen.elements [ '*'; '?'; '['; ']'; '{'; '}'; ','; '\\' ]))
                (fun character ->
                    let text = string character
                    let pattern = Glob.compile ("\\" + text)
                    Expect.isTrue (pattern.IsMatch text) $"An escaped {text} matches itself."
                    Expect.isFalse (pattern.IsMatch "x") $"An escaped {text} matches nothing else."))
        testPropertyWithConfig
            (config 400 20261042UL)
            "a character class matches exactly the members it escapes"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.map2
                        (fun members probe -> members, probe)
                        (Gen.nonEmptyListOf classCharacter)
                        classCharacter
                ))
                (fun (members, probe) ->
                    let body =
                        members
                        |> List.map (fun character -> "\\" + string character)
                        |> String.concat ""

                    let pattern = Glob.compile ("[" + body + "]")
                    let negated = Glob.compile ("[!" + body + "]")

                    for character in members do
                        Expect.isTrue
                            (pattern.IsMatch(string character))
                            $"{character} is a member."

                        Expect.isFalse
                            (negated.IsMatch(string character))
                            $"{character} is excluded."

                    Expect.equal
                        (pattern.IsMatch(string probe))
                        (List.contains probe members)
                        $"{probe} against the class."

                    Expect.equal
                        (negated.IsMatch(string probe))
                        (not (List.contains probe members))
                        $"{probe} against the negated class."

                    let leading = Glob.compile ("[]" + body + "]")
                    Expect.isTrue (leading.IsMatch "]") "A leading ']' is a member."

                    Expect.equal
                        (leading.IsMatch(string probe))
                        (probe = ']' || List.contains probe members)
                        $"{probe} against a class led by ']'."))
        testPropertyWithConfig
            (config 400 20261043UL)
            "a character class range runs upwards from a member of its own"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! first = classCharacter
                        let! last = classCharacter
                        let! probe = classCharacter
                        return first, last, probe
                    }
                ))
                (fun (first, last, probe) ->
                    let body = "\\" + string first + "-\\" + string last
                    let pattern = Glob.compile ("[" + body + "]")
                    Expect.isTrue (pattern.IsMatch(string first)) $"{first} opens the range."

                    Expect.equal
                        (pattern.IsMatch(string probe))
                        (probe = first || (probe >= first && probe <= last))
                        $"{probe} against [{first}-{last}]."))
        testPropertyWithConfig
            (config 300 20261019UL)
            "an ignore pattern keeps braces and commas literal"
            (Prop.forAll (Arb.fromGen (Gen.two literal)) (fun (left, right) ->
                let text = "{" + left + "," + right + "}"
                let ignore = Glob.compileIgnore text
                Expect.isTrue (ignore.IsMatch text) "An ignore pattern matches the braces."
                Expect.isFalse (ignore.IsMatch left) "An ignore pattern has no branches."
                Expect.isTrue ((Glob.compile text).IsMatch left) "A config pattern does."))
        testPropertyWithConfig
            (config 300 20261020UL)
            "a file pattern anchors only when it carries a separator"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.map2 (fun name prefix -> name, prefix) segment (Gen.nonEmptyListOf segment)
                ))
                (fun (name, prefix) ->
                    let leading = String.Join("/", prefix) + "/"
                    let bare = Glob.filePattern name
                    Expect.isTrue (bare.IsMatch name) "A bare name matches at the root."

                    Expect.isTrue
                        (bare.IsMatch(leading + name))
                        "A bare name matches at any depth."

                    let anchored = Glob.filePattern (leading + name)

                    Expect.isTrue
                        (anchored.IsMatch(leading + name))
                        "An anchored pattern matches its path."

                    Expect.isFalse (anchored.IsMatch name) "An anchored pattern does not float."))
        testPropertyWithConfig
            (config 300 20261021UL)
            "normalizing a path removes every backslash and is idempotent"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.nonEmptyListOf segment
                    |> Gen.map (fun segments -> String.Join("\\", segments))
                ))
                (fun path ->
                    let normalized = Glob.normalize path

                    Expect.isFalse
                        (normalized.Contains '\\')
                        "No separator survives as a backslash."

                    Expect.equal
                        (Glob.normalize normalized)
                        normalized
                        "Normalizing twice changes nothing."))
        testPropertyWithConfig
            (config 300 20261022UL)
            "a relative path resolves inside its directory and is refused outside"
            (Prop.forAll (Arb.fromGen (Gen.nonEmptyListOf segment)) (fun segments ->
                let root = Path.Combine(Path.GetTempPath(), "csff-relative")
                let relative = String.Join("/", segments)

                Expect.equal
                    (Glob.relative root (Path.Combine(root, Path.Combine(List.toArray segments))))
                    (Some relative)
                    "A descendant resolves to its normalized relative path."

                Expect.equal
                    (Glob.relative (Path.Combine(root, "inner")) root)
                    None
                    "An ancestor is outside the directory."))
        testPropertyWithConfig
            (config 900 20261023UL)
            "fast glob matching agrees with compiled regex matching"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! a = segment
                        let! b = segment
                        let! pathSegments = Gen.nonEmptyListOf segment

                        let patterns =
                            [
                                "*"
                                "**"
                                "**/*"
                                a
                                "**/" + a
                                "**/*" + a
                                "**/" + a + "*"
                                "**/*" + a + "*"
                                "**/" + a + "*" + b
                                "**/*.{" + a + "," + b + "}"
                                "**/*.{" + a + ",*" + b + "}"
                                "**/[" + string a[0] + "]" + a.Substring(1) + "*"
                                a + "/**/*" + b
                                "**/" + a + "/**"
                                "**/" + a + "/*"
                                "**/" + a + "/" + b
                                a + "/**/" + b + "/*"
                                "**/" + a + "?"
                                "**/[._]s[a-w][a-z]"
                                "**/[" + string a[0] + string b[0] + "]" + a.Substring(1)
                                "**/[" + string a[0] + string b[0] + "]" + a.Substring(1) + "*"
                                "**/*[" + string a[0] + string b[0] + "]" + a.Substring(1)
                                "**/*.{" + a + "," + b + "}*"
                            ]

                        let! pattern = Gen.elements patterns

                        let! shape = Gen.choose (0, 4)
                        let trunk = String.Join("/", pathSegments)

                        let candidate =
                            match shape with
                            | 0 -> trunk
                            | 1 -> trunk + "/" + a + "/" + b
                            | 2 -> a + "/" + trunk + "/" + b + "/" + a
                            | 3 -> trunk + "/" + a + "z"
                            | _ -> trunk + "/.s" + string a[0] + "b"

                        return pattern, candidate
                    }
                ))
                (fun (pattern, candidate) ->
                    let regex = Glob.compile pattern
                    let fast = Glob.fastCompile true pattern

                    Expect.equal
                        (Glob.isMatch fast regex candidate)
                        (regex.IsMatch candidate)
                        "FastGlob agrees with Regex.IsMatch in config mode."

                    let ignoreRegex = Glob.compileIgnore pattern
                    let ignoreFast = Glob.fastCompile false pattern

                    Expect.equal
                        (Glob.isMatch ignoreFast ignoreRegex candidate)
                        (ignoreRegex.IsMatch candidate)
                        "FastGlob agrees with Regex.IsMatch in ignore mode."))
    ]

let private cacheKey =
    gen {
        let! a = ArbMap.generate<uint64> ArbMap.defaults
        let! b = ArbMap.generate<uint64> ArbMap.defaults
        let! c = ArbMap.generate<uint64> ArbMap.defaults
        let! d = ArbMap.generate<uint64> ArbMap.defaults
        let! width = Gen.choose (1, 400)
        let! indent = Gen.choose (1, 16)
        let! flags = Gen.choose (0, 15)

        return
            {
                A = a
                B = b
                C = c
                D = d
                Width = width
                Indent = indent
                Flags = flags
            }
    }

let private settingsGenerator =
    gen {
        let! width = Gen.choose (1, 400)
        let! indent = Gen.choose (1, 16)
        let! tabs = Gen.elements [ false; true ]
        let! crlf = Gen.elements [ false; true ]
        let! auto = Gen.elements [ false; true ]

        return
            {
                Printer =
                    { PrinterOptions.Default with
                        Width = width
                        IndentSize = indent
                        UseTabs = tabs
                        EndOfLine = if crlf then EndOfLine.CrLf else EndOfLine.Lf
                    }
                AutoEndOfLine = auto
            }
    }

let private digest = Gen.arrayOfLength 32 (ArbMap.generate<byte> ArbMap.defaults)

let private cacheProperties =
    [
        testPropertyWithConfig
            (config 200 20261023UL)
            "a saved cache reads back as the keys it was saved from"
            (Prop.forAll
                (Arb.fromGen (Gen.listOf cacheKey |> Gen.map (List.truncate 64)))
                (fun keys ->
                    withDirectory (fun directory ->
                        let path = Path.Combine(directory, "entries.cache")
                        let current = HashSet<CacheKey> keys
                        Cache.save path (HashSet<CacheKey>()) current

                        Expect.isTrue
                            (Cache.read(path).SetEquals current)
                            "Every key survives the round trip.")))
        testPropertyWithConfig
            (config 200 20261024UL)
            "a cache key changes with every input it covers"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.map3
                        (fun d s g -> d, s, g)
                        digest
                        settingsGenerator
                        (Gen.elements [ false; true ])
                ))
                (fun (bytes, settings, includeGenerated) ->
                    let key = Cache.key (ReadOnlySpan<byte> bytes) settings includeGenerated

                    Expect.equal
                        (Cache.key (ReadOnlySpan<byte> bytes) settings includeGenerated)
                        key
                        "The same inputs give the same key."

                    Expect.notEqual
                        (Cache.key (ReadOnlySpan<byte> bytes) settings (not includeGenerated))
                        key
                        "Generated-file inclusion reaches the key."

                    let widened =
                        { settings with
                            Printer =
                                { settings.Printer with
                                    Width = settings.Printer.Width + 1
                                }
                        }

                    Expect.notEqual
                        (Cache.key (ReadOnlySpan<byte> bytes) widened includeGenerated)
                        key
                        "Width reaches the key."

                    let reindented =
                        { settings with
                            Printer =
                                { settings.Printer with
                                    IndentSize = settings.Printer.IndentSize + 1
                                }
                        }

                    Expect.notEqual
                        (Cache.key (ReadOnlySpan<byte> bytes) reindented includeGenerated)
                        key
                        "Indent reaches the key."

                    for changed in
                        [
                            { settings with
                                Printer =
                                    { settings.Printer with
                                        UseTabs = not settings.Printer.UseTabs
                                    }
                            }
                            { settings with
                                Printer =
                                    { settings.Printer with
                                        EndOfLine =
                                            if settings.Printer.EndOfLine = EndOfLine.Lf then
                                                EndOfLine.CrLf
                                            else
                                                EndOfLine.Lf
                                    }
                            }
                            { settings with
                                AutoEndOfLine = not settings.AutoEndOfLine
                            }
                        ] do
                        Expect.notEqual
                            (Cache.key (ReadOnlySpan<byte> bytes) changed includeGenerated)
                            key
                            "Every printer setting reaches the key."))
        testPropertyWithConfig
            (config 200 20261025UL)
            "a cache digest change reaches the key"
            (Prop.forAll
                (Arb.fromGen (Gen.map2 (fun d index -> d, index) digest (Gen.choose (0, 31))))
                (fun (bytes, index) ->
                    let settings = Settings.Default
                    let key = Cache.key (ReadOnlySpan<byte> bytes) settings false
                    let flipped = Array.copy bytes
                    flipped[index] <- flipped[index] ^^^ 1uy

                    Expect.notEqual
                        (Cache.key (ReadOnlySpan<byte> flipped) settings false)
                        key
                        $"Byte {index} of the digest reaches the key."))
        testPropertyWithConfig
            (config 150 20261026UL)
            "a corrupted cache file reads as empty rather than as wrong entries"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! keys = Gen.nonEmptyListOf cacheKey |> Gen.map (List.truncate 16)
                        let! offset = Gen.choose (0, 1000)
                        return keys, offset
                    }
                ))
                (fun (keys, offset) ->
                    withDirectory (fun directory ->
                        let path = Path.Combine(directory, "entries.cache")
                        let current = HashSet<CacheKey> keys
                        Cache.save path (HashSet<CacheKey>()) current
                        let bytes = File.ReadAllBytes path
                        let index = offset % bytes.Length
                        bytes[index] <- bytes[index] ^^^ 0xffuy
                        File.WriteAllBytes(path, bytes)

                        Expect.isEmpty
                            (Cache.read path)
                            $"A cache corrupted at byte {index} of {bytes.Length} is discarded.")))
        testPropertyWithConfig
            (config 200 20261027UL)
            "a cache path is stable per root and distinct between roots"
            (Prop.forAll (Arb.fromGen (Gen.two segment)) (fun (left, right) ->
                let directory = Path.Combine(Path.GetTempPath(), "csff-cache")

                let path root =
                    Cache.path directory (Path.Combine(directory, root))

                Expect.equal (path left) (path left) "The same root gives the same path."

                if left <> right then
                    Expect.notEqual (path left) (path right) "Distinct roots do not share a cache."))
    ]

let private endOfLineName =
    Gen.elements [ "auto", None; "lf", Some EndOfLine.Lf; "crlf", Some EndOfLine.CrLf ]

let private configurationProperties =
    [
        testPropertyWithConfig
            (config 200 20261028UL)
            "a csffrc reads back as the settings it was written from"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! width = Gen.choose (1, 400)
                        let! indent = Gen.choose (1, 16)
                        let! tabs = Gen.elements [ false; true ]
                        let! eol = endOfLineName
                        return width, indent, tabs, eol
                    }
                ))
                (fun (width, indent, tabs, (eolName, eol)) ->
                    withDirectory (fun directory ->
                        let path = Path.Combine(directory, ".csffrc.json")
                        let tabsText = if tabs then "true" else "false"

                        File.WriteAllText(
                            path,
                            $"""{{"printWidth":{width},"indentSize":{indent},"useTabs":{tabsText},"endOfLine":"{eolName}"}}"""
                        )

                        let config = Configuration.read path
                        let settings = config.Settings

                        Expect.equal
                            settings.Printer.Width
                            width
                            "printWidth reaches the printer."

                        Expect.equal
                            settings.Printer.IndentSize
                            indent
                            "indentSize reaches the printer."

                        Expect.equal settings.Printer.UseTabs tabs "useTabs reaches the printer."

                        match eol with
                        | None ->
                            Expect.isTrue settings.AutoEndOfLine "auto defers the line ending."
                        | Some expected ->
                            Expect.isFalse
                                settings.AutoEndOfLine
                                "An explicit line ending is not automatic."

                            Expect.equal
                                settings.Printer.EndOfLine
                                expected
                                "The line ending reaches the printer."

                        Expect.equal
                            (Configuration.find directory
                             |> Option.map (fun found -> found.Settings))
                            (Some settings)
                            "Finding the file agrees with reading it.")))
        testPropertyWithConfig
            (config 200 20261029UL)
            "a csffrc override applies to the files its pattern selects"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! outer = Gen.choose (1, 200)
                        let! inner = Gen.choose (201, 400)
                        let! directoryName = segment
                        let! fileName = segment
                        return outer, inner, directoryName, fileName
                    }
                ))
                (fun (outer, inner, directoryName, fileName) ->
                    withDirectory (fun directory ->
                        let path = Path.Combine(directory, ".csffrc.json")

                        File.WriteAllText(
                            path,
                            $"""{{"printWidth":{outer},"overrides":[{{"files":"{directoryName}/**/*.cs","printWidth":{inner}}}]}}"""
                        )

                        let config = Some(Configuration.read path)
                        let selected = Path.Combine(directory, directoryName, fileName + ".cs")
                        let other = Path.Combine(directory, fileName + ".cs")

                        Expect.equal
                            (Configuration.forFile config selected).Printer.Width
                            inner
                            "The override selects the file under its directory."

                        Expect.equal
                            (Configuration.forFile config other).Printer.Width
                            outer
                            "A file outside the pattern keeps the outer width.")))
        testPropertyWithConfig
            (config 200 20261030UL)
            "an editorconfig reads back as the settings it was written from"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! width = Gen.choose (1, 400)
                        let! indent = Gen.choose (1, 16)
                        let! tabs = Gen.elements [ false; true ]
                        let! eol = endOfLineName
                        let! name = segment
                        return width, indent, tabs, eol, name
                    }
                ))
                (fun (width, indent, tabs, (eolName, eol), name) ->
                    withDirectory (fun directory ->
                        let style = if tabs then "tab" else "space"

                        File.WriteAllText(
                            Path.Combine(directory, ".editorconfig"),
                            $"root = true\n[*.cs]\nmax_line_length = {width}\nindent_size = {indent}\nindent_style = {style}\ntab_width = {indent}\nend_of_line = {eolName}\n"
                        )

                        let isRoot, sections = Configuration.readEditor directory
                        Expect.isTrue isRoot "The root marker is read outside any section."
                        Expect.isNonEmpty sections "The section is read."

                        let group = Some { Sections = sections; Parent = None }
                        let file = Path.Combine(directory, name + ".cs")

                        let settings =
                            Configuration.editorForFile group file
                            |> Option.defaultWith (fun () ->
                                failtest "The csharp formatter is selected.")

                        Expect.equal
                            settings.Printer.Width
                            width
                            "max_line_length reaches the printer."

                        Expect.equal
                            settings.Printer.IndentSize
                            indent
                            "The indent width reaches the printer."

                        Expect.equal
                            settings.Printer.UseTabs
                            tabs
                            "indent_style reaches the printer."

                        match eol with
                        | None ->
                            Expect.isTrue settings.AutoEndOfLine "auto defers the line ending."
                        | Some expected ->
                            Expect.equal
                                settings.Printer.EndOfLine
                                expected
                                "end_of_line reaches the printer."

                        let other = Path.Combine(directory, name + ".txt")

                        let untouched =
                            Configuration.editorForFile group other
                            |> Option.defaultWith (fun () ->
                                failtest "A non-C# file is still formattable.")

                        Expect.equal
                            untouched.Printer.Width
                            PrinterOptions.Default.Width
                            "A file the pattern misses keeps the default width.")))
    ]

let private discoveryProperties =
    [
        testPropertyWithConfig
            (config 150 20261031UL)
            "discovery finds every source once, in ordinal order, at any job count"
            (Prop.forAll
                (Arb.fromGen (
                    gen {
                        let! names = Gen.nonEmptyListOf segment |> Gen.map (List.truncate 12)
                        let! depths = Gen.listOfLength names.Length (Gen.choose (0, 3))
                        let! jobs = Gen.elements [ 1; 2; 4 ]
                        return names, depths, jobs
                    }
                ))
                (fun (names, depths, jobs) ->
                    withDirectory (fun directory ->
                        File.WriteAllText(Path.Combine(directory, ".git"), "gitdir: /fixture")

                        let expected =
                            List.zip names depths
                            |> List.map (fun (name, depth) ->
                                let relative =
                                    Path.Combine(
                                        Array.append (Array.create depth name) [| name + ".cs" |]
                                    )

                                let path = Path.Combine(directory, relative)
                                Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
                                File.WriteAllText(path, "class C {}")
                                path)
                            |> List.distinct
                            |> List.sortWith (fun left right ->
                                StringComparer.Ordinal.Compare(left, right))

                        let found = Discovery.files [| directory |] None None false jobs

                        Expect.equal
                            (found |> Array.map (fun file -> file.Path) |> Array.toList)
                            expected
                            $"Every source is found once in ordinal order at {jobs} jobs.")))
        testPropertyWithConfig
            (config 150 20261041UL)
            "spelling one file several ways discovers it once"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.map2 (fun name jobs -> name, jobs) segment (Gen.elements [ 1; 2; 4 ])
                ))
                (fun (name, jobs) ->
                    withDirectory (fun directory ->
                        File.WriteAllText(Path.Combine(directory, ".git"), "gitdir: /fixture")
                        let child = Path.Combine(directory, name)
                        Directory.CreateDirectory child |> ignore
                        let file = Path.Combine(child, name + ".cs")
                        File.WriteAllText(file, "class C {}")

                        let roots =
                            [|
                                file
                                Path.Combine(child, ".", name + ".cs")
                                Path.Combine(child, "..", name, name + ".cs")
                                Path.GetFullPath file
                            |]

                        let found = Discovery.files roots None None false jobs

                        Expect.equal
                            found.Length
                            1
                            $"Four spellings of one file find it once at {jobs} jobs.")))
        testPropertyWithConfig
            (config 150 20261032UL)
            "aliasing a root does not discover a source twice"
            (Prop.forAll
                (Arb.fromGen (
                    Gen.map2 (fun name jobs -> name, jobs) segment (Gen.elements [ 1; 2; 4 ])
                ))
                (fun (name, jobs) ->
                    withDirectory (fun directory ->
                        File.WriteAllText(Path.Combine(directory, ".git"), "gitdir: /fixture")
                        let child = Path.Combine(directory, name)
                        Directory.CreateDirectory child |> ignore
                        File.WriteAllText(Path.Combine(child, name + ".cs"), "class C {}")

                        let roots =
                            [|
                                directory
                                child
                                child + string Path.DirectorySeparatorChar
                                Path.Combine(child, ".")
                            |]

                        let found = Discovery.files roots None None false jobs

                        Expect.equal
                            found.Length
                            1
                            $"Four aliases of one source find it once at {jobs} jobs.")))
    ]

let craftedSource (seed: int) =
    let rng = Random(seed)
    let choice (items: string list) = items[rng.Next items.Length]
    let symbols = [ "A"; "B"; "C"; "FLAG"; "NET" ]
    let mutable counter = 0

    let ident prefix =
        counter <- counter + 1
        $"{prefix}{counter}"

    let spaces () = choice [ ""; " "; "   "; "\t" ]

    let marker () =
        let kind = choice [ "// csff-ignore"; "// csff-ignore-start"; "// csff-ignore-end" ]

        kind + choice [ ""; ""; " - reason"; " - why not" ]

    let commentLine () =
        choice
            [
                "// plain note"
                "/* same line */"
                "/** doc */"
                "/*\n * spans\n */"
                "/**doc\n*/"
                "/*\n#elif H\n*/"
                "/*\n#endif\n*/"
                "/*\n#warning tail */"
            ]

    let condition () =
        let a = choice symbols
        let mutable b = choice symbols

        while b = a do
            b <- choice symbols

        choice
            [
                a
                $"{a}&&{b}"
                $"{a}||{b}"
                $"!{a}"
                $"{a} && !{b}"
                "true"
                $"({a}||{b})&&{b}"
            ]

    let statement broken =
        let name = ident "x"

        if broken then
            choice [ "class " + ident "Broken" + "{"; $"int {name}"; "}" ]
        else
            choice
                [
                    $"X({spaces ()}{rng.Next(0, 100)}{spaces ()});"
                    $"int{spaces ()} {name} = {rng.Next(0, 10)};"
                    $"var {name} = \"a  b\";"
                    "var " + name + $" = $\"{{M({rng.Next(0, 10)},{rng.Next(0, 10)})}}\";"
                    $"var {name} = @\"ver\nbatim\";"
                    "do ;\nwhile (false);"
                    $"string {name} = \"\"\"\n    body {spaces ()}\n    \"\"\";"
                ]

    let rec directiveBlock depth =
        let lines = ResizeArray()
        lines.Add $"#if {condition ()}"
        lines.Add(bodyLines (depth + 1) true)

        if rng.NextDouble() < 0.4 then
            lines.Add $"#elif {condition ()}"
            lines.Add(bodyLines (depth + 1) true)

        if rng.NextDouble() < 0.3 then
            lines.Add "#else"
            lines.Add(bodyLines (depth + 1) true)

        lines.Add "#endif"
        String.Join("\n", Seq.filter (fun (l: string) -> l <> "") lines)

    and regionBlock depth =
        let name = ident "R"
        $"#region {name}\n{bodyLines (depth + 1) false}\n#endregion"

    and bodyLines depth allowBroken =
        if depth > 3 then
            statement false
        else
            let parts = ResizeArray()

            for _ in 1 .. rng.Next(1, 4) do
                let roll = rng.NextDouble()

                if roll < 0.12 then
                    parts.Add(marker ())
                    parts.Add(statement false)
                elif roll < 0.2 then
                    parts.Add(commentLine ())
                elif roll < 0.35 then
                    parts.Add(directiveBlock depth)
                elif roll < 0.42 then
                    parts.Add(regionBlock depth)
                elif roll < 0.5 then
                    parts.Add("{\n" + bodyLines (depth + 1) false + "\n}")
                elif allowBroken && roll < 0.56 then
                    parts.Add(statement true)
                elif roll < 0.62 then
                    parts.Add(
                        choice
                            [
                                "#warning odd /* text"
                                $"#pragma warning disable {rng.Next(100, 1000)}"
                                $"#define {choice symbols}"
                                $"#undef {choice symbols}"
                            ]
                    )
                else
                    parts.Add(statement false)

            String.Join("\n", parts)

    let memberDecl () =
        let roll = rng.NextDouble()
        let name = ident "M"

        if roll < 0.12 then
            let field = ident "f"
            $"{marker ()}\nint{spaces ()} {field}; // keep"
        elif roll < 0.2 then
            $"{marker ()}\n[My]\nvoid {name}() {{ }}"
        elif roll < 0.3 then
            let enumName = ident "E"
            $"enum {enumName}\n{{\n    {marker ()}\n    AA{spaces ()}={spaces ()}1, // keep\n    BB = 2,\n}}"
        else
            $"void {name}()\n{{\n{bodyLines 1 (rng.NextDouble() < 0.3)}\n}}"

    let pieces = ResizeArray()

    if rng.NextDouble() < 0.3 then
        pieces.Add(choice [ "\f"; "" ] + $"#if {condition ()}")
        pieces.Add("using " + ident "NsA" + ";")
        pieces.Add "#endif"

    if rng.NextDouble() < 0.25 then
        pieces.Add(marker ())

    if rng.NextDouble() < 0.3 then
        pieces.Add("using" + spaces () + " " + ident "NsZ" + ";")
        pieces.Add("using " + ident "NsB" + ";")

    if rng.NextDouble() < 0.2 then
        pieces.Add(commentLine ())

    let members = String.Join("\n", [ for _ in 1 .. rng.Next(1, 4) -> memberDecl () ])

    let className = ident "C"
    let mutable declaration = $"class {className}\n{{\n{members}\n}}"

    if rng.NextDouble() < 0.3 then
        let namespaceName = ident "N"
        declaration <- $"namespace {namespaceName}\n{{\n{declaration}\n}}"

    if rng.NextDouble() < 0.15 then
        declaration <- $"{marker ()}\n{declaration}"

    pieces.Add declaration
    let text = String.Join("\n", pieces) + "\n"

    let prefixed = rng.NextDouble() < 0.1
    let first = text.IndexOf "#if"

    if prefixed && first >= 0 then
        text.Insert(first, "/**doc*/")
    else
        text

let private sourceProperties =
    [
        for width in [ 20; 30; 40; 60; 80; 100; 120 ] ->
            testCase $"formatting a crafted source is idempotent at width {width}" (fun () ->
                use worker = new Worker()

                let settings =
                    { Settings.Default with
                        Printer =
                            { PrinterOptions.Default with
                                Width = width
                            }
                    }

                let print (source: string) =
                    try
                        worker.Print(source, settings)
                        Some worker.OutputText
                    with :? InvalidOperationException ->
                        None

                let unstable =
                    [
                        for seed in 0..19999 do
                            match print (craftedSource seed) with
                            | None -> ()
                            | Some once ->
                                match print once with
                                | Some twice when twice = once -> ()
                                | Some _ -> $"seed {seed}"
                                | None -> $"seed {seed} (output refused)"
                    ]

                Expect.equal
                    unstable
                    []
                    "Formatting a crafted source's output again must not change it.")
    ]

let tests =
    testList
        "property"
        (widthProperties
         @ globProperties
         @ cacheProperties
         @ configurationProperties
         @ discoveryProperties
         @ sourceProperties)
