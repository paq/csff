module Csff.Tests.YamlTests

open System
open System.IO
open Csff.Cli
open Expecto
open FsCheck
open FsCheck.FSharp

let private parse text = Yaml.parse "test.yaml" text

let private scalar style value = YamlNode.Scalar("", value, style)
let private plain = scalar YamlStyle.Plain
let private single = scalar YamlStyle.SingleQuoted
let private double = scalar YamlStyle.DoubleQuoted
let private literal = scalar YamlStyle.Literal
let private folded = scalar YamlStyle.Folded

let private sequence items =
    YamlNode.Sequence("", List.toArray items)

let private mapping entries =
    YamlNode.Mapping("", entries |> List.map (fun (key, value) -> plain key, value) |> List.toArray)

let private tagged tag node =
    match node with
    | YamlNode.Scalar(_, value, style) -> YamlNode.Scalar(tag, value, style)
    | YamlNode.Sequence(_, items) -> YamlNode.Sequence(tag, items)
    | YamlNode.Mapping(_, entries) -> YamlNode.Mapping(tag, entries)

let private core name = "tag:yaml.org,2002:" + name

let private reads cases =
    for input: string, expected in cases do
        Expect.equal (parse input) [| expected |] input

let private rejects (input: string) (position: string) (message: string) =
    try
        parse input |> ignore
        failtest ("Rejected input was read: " + input)
    with :? FormatException as error ->
        Expect.equal error.Message ("test.yaml:" + position + ": " + message) input

let private word =
    Gen.elements
        [
            "a"
            "key"
            "x1"
            "80"
            "true"
            "null"
            "a-b"
            "a_b"
            "é"
            "a b"
            "x:y"
            "a#b"
        ]

let private text =
    Gen.elements [ 'a'; ' '; '"'; '\\'; '\''; '\n'; '\t'; ':'; '#'; '-'; 'é'; '\u00a0' ]
    |> Gen.arrayOf
    |> Gen.map String

let private escape (value: string) =
    value.Replace("\\", "\\\\").Replace("\"", "\\\"").Replace("\n", "\\n").Replace("\t", "\\t")

let private leaf =
    Gen.oneof
        [
            word |> Gen.map (fun value -> value, plain value)
            text |> Gen.map (fun value -> "\"" + escape value + "\"", double value)
            text
            |> Gen.map (fun value ->
                let value = value.Replace("\n", "")
                "'" + value.Replace("'", "''") + "'", single value)
        ]

type private Tree =
    | Leaf of text: string * node: YamlNode
    | Map of Tree list
    | List of Tree list

let rec private tree size =
    if size <= 0 then
        leaf |> Gen.map Leaf
    else
        Gen.oneof
            [
                leaf |> Gen.map Leaf
                Gen.listOf (tree (size / 3)) |> Gen.map Map
                Gen.listOf (tree (size / 3)) |> Gen.map List
            ]

let rec private node tree =
    match tree with
    | Leaf(_, node) -> node
    | Map children ->
        mapping (children |> List.mapi (fun index child -> "k" + string index, node child))
    | List children -> sequence (List.map node children)

let rec private render (step: int) (indent: int) (dash: bool) (tree: Tree) =
    match tree with
    | Leaf(text, _) -> " " + text + "\n"
    | Map [] -> " {}\n"
    | List [] -> " []\n"
    | Map children when dash ->
        let inner = indent + 2

        children
        |> List.mapi (fun index child ->
            (if index = 0 then " " else String(' ', inner))
            + "k"
            + string index
            + ":"
            + render step inner false child)
        |> String.concat ""
    | Map children ->
        "\n"
        + (children
           |> List.mapi (fun index child ->
               String(' ', indent + step)
               + "k"
               + string index
               + ":"
               + render step (indent + step) false child)
           |> String.concat "")
    | List children ->
        let inner = if dash then indent + 2 else indent + step

        (if dash then "" else "\n")
        + (children
           |> List.mapi (fun index child ->
               (if dash && index = 0 then " " else String(' ', inner))
               + "-"
               + render step inner true child)
           |> String.concat "")

let private document =
    gen {
        let! size = Gen.choose (0, 40)
        let! children = Gen.listOf (tree size)
        let! step = Gen.choose (1, 4)
        let tree = Map children
        let text = render step -step false tree
        return text, node tree
    }

let private withConfig (content: string) check =
    let directory =
        Path.Combine(Path.GetTempPath(), "csff-yaml-review-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory directory |> ignore

    try
        let path = Path.Combine(directory, ".csffrc.yaml")
        File.WriteAllText(path, content)
        check directory (Configuration.read path)
    finally
        Directory.Delete(directory, true)

let tests =
    testList
        "yaml"
        [
            test "YAML block structure reads as YamlDotNet read it" {
                reads
                    [
                        "printWidth: 80\nuseTabs: true\n",
                        mapping [ "printWidth", plain "80"; "useTabs", plain "true" ]
                        "a:\n  b:\n    c: 1\n  d: 2\ne: 3\n",
                        mapping
                            [
                                "a", mapping [ "b", mapping [ "c", plain "1" ]; "d", plain "2" ]
                                "e", plain "3"
                            ]
                        "overrides:\n- files: \"*.cs\"\n  printWidth: 40\n- files: '*.fs'\n",
                        mapping
                            [
                                "overrides",
                                sequence
                                    [
                                        mapping [ "files", double "*.cs"; "printWidth", plain "40" ]
                                        mapping [ "files", single "*.fs" ]
                                    ]
                            ]
                        "- - a\n  - b\n-   c: 1\n    d: 2\n",
                        sequence
                            [
                                sequence [ plain "a"; plain "b" ]
                                mapping [ "c", plain "1"; "d", plain "2" ]
                            ]
                        "a:\nb: ~\nc:\n-\n- x\n",
                        mapping
                            [ "a", plain ""; "b", plain "~"; "c", sequence [ plain ""; plain "x" ] ]
                        "? a\n: 1\n? b\n", mapping [ "a", plain "1"; "b", plain "" ]
                        "# head\na: 1 # trailing\n\n  # indented\nb: 2\n",
                        mapping [ "a", plain "1"; "b", plain "2" ]
                        "\"q\" : 1\n'r': 2\n",
                        YamlNode.Mapping("", [| double "q", plain "1"; single "r", plain "2" |])
                    ]
            }
            test "YAML flow collections read as YamlDotNet read them" {
                reads
                    [
                        "a: [1, \"two\", {b: c, d}, [], {}]\n",
                        mapping
                            [
                                "a",
                                sequence
                                    [
                                        plain "1"
                                        double "two"
                                        mapping [ "b", plain "c"; "d", plain "" ]
                                        sequence []
                                        mapping []
                                    ]
                            ]
                        "a: [1,\n  2, # comment\n  3,]\n",
                        mapping [ "a", sequence [ plain "1"; plain "2"; plain "3" ] ]
                        "a: [? 'files'\n  : '*.cs']\n",
                        mapping
                            [
                                "a",
                                sequence
                                    [ YamlNode.Mapping("", [| single "files", single "*.cs" |]) ]
                            ]
                        "overrides: [{files # comment\n  : '*.cs', printWidth: 40}]\n",
                        mapping
                            [
                                "overrides",
                                sequence
                                    [ mapping [ "files", single "*.cs"; "printWidth", plain "40" ] ]
                            ]
                        "overrides: [ &rule\n  # c\n  !!map {files: '*.cs'} ]\n",
                        mapping
                            [
                                "overrides",
                                sequence
                                    [ tagged (core "map") (mapping [ "files", single "*.cs" ]) ]
                            ]
                        "[a: 1, b, x:y, \"c\":d]",
                        sequence
                            [
                                mapping [ "a", plain "1" ]
                                plain "b"
                                plain "x:y"
                                YamlNode.Mapping("", [| double "c", plain "d" |])
                            ]
                        "{ multi\n  line: value, \"quoted\"\n  : key}",
                        YamlNode.Mapping(
                            "",
                            [| plain "multi line", plain "value"; double "quoted", plain "key" |]
                        )
                        "a: [@x, |y, >z]\n",
                        mapping [ "a", sequence [ plain "@x"; plain "|y"; plain ">z" ] ]
                    ]
            }
            test "empty tagged flow scalars stop at collection delimiters" {
                reads
                    [
                        "[!!null]", sequence [ tagged (core "null") (plain "") ]
                        "{a: !!null, b: !!str}",
                        mapping
                            [
                                "a", tagged (core "null") (plain "")
                                "b", tagged (core "str") (plain "")
                            ]
                    ]
            }
            test "malformed tag escapes carry YAML source locations" {
                rejects "a: !<tag:%ZZ> x\n" "1:4" "Invalid YAML tag escape"
                rejects "a: !!str%Q0 x\n" "1:4" "Invalid YAML tag escape"
                rejects "%TAG !e! tag:bad%Q0/\n---\na: !e!x y\n" "1:1" "Invalid YAML tag escape"
            }
            test "folded blocks retain blank lines before more-indented content" {
                reads
                    [
                        "a: >\n  one\n\n    code\n  last\n",
                        mapping [ "a", folded "one\n\n  code\nlast\n" ]
                        "a: >\n  one\n\n\n    code\n", mapping [ "a", folded "one\n\n\n  code\n" ]
                    ]
            }
            test "YAML scalars fold and escape as YamlDotNet read them" {
                reads
                    [
                        "a: one\n  two\n\n  three\n", mapping [ "a", plain "one two\nthree" ]
                        "a: 'it''s\n  here'\n", mapping [ "a", single "it's here" ]
                        "a: \"t\\t\\x41\\u00e9\\U0001F600\\ud83d\\ude00 \\N\\_\\L\\P\\/\\0\"\n",
                        mapping
                            [
                                "a",
                                double "t\tAé\U0001F600\U0001F600 \u0085\u00a0\u2028\u2029/\000"
                            ]
                        "a: \"x\\\n  y\"\nb: \"x\n\n  y\"\n",
                        mapping [ "a", double "xy"; "b", double "x\ny" ]
                        "a: |\n  x\n   y\n\nb: |-\n  z\n\nc: |+\n  w\n\n",
                        mapping [ "a", literal "x\n y\n"; "b", literal "z"; "c", literal "w\n\n" ]
                        "a: >\n  one\n  two\n\n  three\n   more\n  last\n",
                        mapping [ "a", folded "one two\nthree\n more\nlast\n" ]
                        "a: |2\n   x\nb: >-\n\n  y\n",
                        mapping [ "a", literal " x\n"; "b", folded "\ny" ]
                        "--- |\nx\ny\n", literal "x\ny\n"
                        "a: |\n  \tx\n", mapping [ "a", literal "\tx\n" ]
                    ]
            }
            test "YAML anchors and aliases resolve as YamlDotNet resolved them" {
                reads
                    [
                        "base: &w 100\nprintWidth: *w\n",
                        mapping [ "base", plain "100"; "printWidth", plain "100" ]
                        "a: &k key\n*k : v\n", mapping [ "a", plain "key"; "key", plain "v" ]
                        "a: *x\nb: &x 1\nc: &x 2\n",
                        mapping [ "a", plain "2"; "b", plain "1"; "c", plain "2" ]
                        "a: &x 1\nb: *x\nc: &x 2\nd: *x\n",
                        mapping [ "a", plain "1"; "b", plain "1"; "c", plain "2"; "d", plain "2" ]
                        "a: &x\n  b: &x 2\nc: *x\n",
                        mapping [ "a", mapping [ "b", plain "2" ]; "c", plain "2" ]
                        "a: &m {b: 1}\nc: *m\n",
                        mapping [ "a", mapping [ "b", plain "1" ]; "c", mapping [ "b", plain "1" ] ]
                        "seq:\n &s\n- a\n", mapping [ "seq", sequence [ plain "a" ] ]
                    ]
            }
            test "YAML tags and directives resolve as YamlDotNet resolved them" {
                reads
                    [
                        "a: !!int '7'\nb: !!str 7\nc: !local x\nd: !<tag:example.com,2000:x> y\ne: ! z\nf: !!\n",
                        mapping
                            [
                                "a", tagged (core "int") (single "7")
                                "b", tagged (core "str") (plain "7")
                                "c", tagged "!local" (plain "x")
                                "d", tagged "tag:example.com,2000:x" (plain "y")
                                "e", tagged "!" (plain "z")
                                "f", tagged (core "") (plain "")
                            ]
                        "%YAML 1.1\n%TAG !e! tag:example.com,2000:app/\n---\na: !e!foo%21 1\n",
                        mapping [ "a", tagged "tag:example.com,2000:app/foo!" (plain "1") ]
                        "%FOO ignored\n--- !!map\n!!str a: 1\n",
                        tagged
                            (core "map")
                            (YamlNode.Mapping("", [| tagged (core "str") (plain "a"), plain "1" |]))
                        "{&b : 1}", YamlNode.Mapping("", [| plain "", plain "1" |])
                    ]
            }
            test "YAML documents, line breaks and tabs read as YamlDotNet read them" {
                for input in
                    [
                        "a: 1\nb:\n- x\n"
                        "a: 1\r\nb:\r\n- x\r\n"
                        "a: 1\rb:\r- x\r"
                        "a: 1\u0085b:\u0085- x"
                    ] do
                    Expect.equal
                        (parse input)
                        [| mapping [ "a", plain "1"; "b", sequence [ plain "x" ] ] |]
                        "CRLF, CR and NEL all break lines."

                reads
                    [
                        "---\na: 1\n...\n# done\n", mapping [ "a", plain "1" ]
                        "--- value\n", plain "value"
                        "a:\t1\nb: [1,\t2]\nc: x\ty\n",
                        mapping
                            [
                                "a", plain "1"
                                "b", sequence [ plain "1"; plain "2" ]
                                "c", plain "x\ty"
                            ]
                    ]

                Expect.equal (parse "") [||] "An empty stream holds no document."
                Expect.equal (parse "# only\n...\n") [||] "Comments and an end marker hold none."
                Expect.equal (parse "a: 1\n---\nb: 2\n").Length 2 "Every document is read."
            }
            test "YAML errors name the file, line and column" {
                rejects "a: b: c" "1:5" "A YAML mapping cannot start on this line"
                rejects "a:\n  - b\n - c\n" "3:2" "Unexpected indentation in a YAML mapping"
                rejects "a: 1\n  b: 2\n" "2:4" "A YAML mapping key must stay on one line"
                rejects "a:\n  b: \"1\"\n   c: 2\n" "3:4" "Unexpected indentation in a YAML mapping"
                rejects "a: \"x\n" "1:4" "Unterminated quoted YAML string"
                rejects "a: 1\na: 2\n" "2:1" "Duplicate YAML mapping key a"
                rejects "a: {b: 1, b: 2}" "1:11" "Duplicate YAML mapping key b"
                rejects "a: *x\n" "1:4" "The YAML alias *x has no anchor"
                rejects "&a [*a]" "1:5" "The YAML alias *a refers to its own node"
                rejects "x: [ &a\n  &b y ]" "2:3" "A YAML node can have only one anchor"
                rejects "x: {a\n  : v}" "2:3" "Expected ',' or '}' in a YAML flow collection"
                rejects "x: {&k a # c\n  : v}" "2:3" "Expected ',' or '}' in a YAML flow collection"

                rejects
                    "*k : 80\nfiles: &k printWidth\nprintWidth: 120\n"
                    "1:1"
                    "Duplicate YAML mapping key printWidth"

                rejects "a: [\"b\"\n  : v]" "2:3" "Expected ',' or ']' in a YAML flow collection"

                rejects
                    (String.Join(
                        "\n",
                        Array.init 10000 (fun level ->
                            "a"
                            + string level
                            + ": &a"
                            + string level
                            + " [*a"
                            + string (level + 1)
                            + "]")
                    ))
                    "255:14"
                    "YAML aliases nest deeper than 256 levels"

                rejects "a: \"\\q\"" "1:5" "Unknown escape sequence in a double-quoted YAML string"
                rejects "a: !e!x 1" "1:4" "Undefined YAML tag handle !e!"
                rejects "a: !!str] 1" "1:4" "Invalid YAML tag tag:yaml.org,2002:str]"
                rejects "%YAML 2.0\n---\na: 1" "1:1" "Unsupported YAML version 2.0"
                rejects "%YAML 1.1\na: 1" "2:1" "Expected '---' after YAML directives"
                rejects "a: [1, 2]# c" "1:10" "A comment after ']' needs a blank before it"

                rejects
                    "a: |\n    \n  x\n"
                    "3:3"
                    "The first line of a YAML literal block has extra spaces"

                rejects (String('[', 300)) "1:256" "YAML nesting exceeds 256 levels"

                rejects
                    (String('k', 1100) + ": v")
                    "1:1"
                    "An implicit YAML key cannot exceed 1024 characters"

                rejects "a: x\u0001" "1:5" "YAML cannot contain the control character U+0001"
                rejects ": v" "1:1" "A YAML mapping key cannot be empty"
                rejects "a: [b, : v]" "1:8" "A YAML mapping key cannot be empty"
                rejects "a: :x" "1:4" "A plain YAML value cannot start with ':'; quote it"

                rejects
                    "a: {\"files\" \"*.cs\"}"
                    "1:13"
                    "Expected ',' or '}' in a YAML flow collection"

                rejects "---\n%FOO ignored\na: 1\n" "2:1" "A YAML value cannot start with '%'"
            }
            test
                "YAML property-only continuations reject repeated node properties without overflowing" {
                let anchors =
                    Array.init 10000 (fun index -> "  &a" + string index + "\n") |> String.concat ""

                rejects
                    ("printWidth: !!int\n" + anchors + "  80\n")
                    "3:3"
                    "A YAML node can have only one anchor"

                rejects
                    "printWidth: !!int\n  !!int\n  80\n"
                    "2:3"
                    "A YAML node can have only one tag"

                rejects "printWidth: &a\n  &b 80\n" "2:3" "A YAML node can have only one anchor"

                reads
                    [
                        "printWidth: !!int\n  &width\n  80\nindentSize: *width\n",
                        mapping
                            [
                                "printWidth", tagged (core "int") (plain "80")
                                "indentSize", tagged (core "int") (plain "80")
                            ]
                        "printWidth: !!int\n  &width\n  '80'\nindentSize: *width\n",
                        mapping
                            [
                                "printWidth", tagged (core "int") (single "80")
                                "indentSize", tagged (core "int") (single "80")
                            ]
                        "!!map\n*key : 80\nfiles: &key printWidth\n",
                        tagged
                            (core "map")
                            (mapping [ "printWidth", plain "80"; "files", plain "printWidth" ])
                    ]
            }
            test "YAML flow and block collection recursion is bounded" {
                let block indicator =
                    Array.init 400 (fun depth -> String(' ', depth * 2) + indicator + "\n")
                    |> String.concat ""

                for input in
                    [
                        String('[', 10000)
                        String.replicate 10000 "{key: "
                        String.replicate 10000 "- " + "80"
                        block "-"
                        block "key:"
                        block "?"
                    ] do
                    Expect.throwsT<FormatException>
                        (fun () -> parse input |> ignore)
                        "Deep collections must report a diagnostic rather than exhaust the stack."
            }
            test "YAML folding preserves escaped whitespace before physical line breaks" {
                for escape, decoded in
                    [
                        "\\x20", " "
                        "\\u0020", " "
                        "\\U00000020", " "
                        "\\ ", " "
                        "\\t", "\t"
                        "\\u0009", "\t"
                    ] do
                    reads
                        [
                            "files: \"foo" + escape + " \t\n  bar.cs\"\n",
                            mapping [ "files", double ("foo" + decoded + " bar.cs") ]
                            "files: \"foo" + escape + "\n\n  bar.cs\"\n",
                            mapping [ "files", double ("foo" + decoded + "\nbar.cs") ]
                        ]

                reads
                    [
                        "files: \"foo \t\n  bar.cs\"\n", mapping [ "files", double "foo bar.cs" ]
                        "files: 'foo \t\n  bar.cs'\n", mapping [ "files", single "foo bar.cs" ]
                    ]

                withConfig
                    "overrides:\n- files: \"foo\\x20\n    bar.cs\"\n  printWidth: 40\n  useTabs: true\n  endOfLine: crlf\n"
                    (fun directory config ->
                        let settings file =
                            Configuration.forFile (Some config) (Path.Combine(directory, file))

                        let matched = settings "foo  bar.cs"

                        Expect.equal
                            matched.Printer.Width
                            40
                            "Both spaces participate in the glob."

                        Expect.isTrue matched.Printer.UseTabs "The matching override uses tabs."

                        Expect.equal
                            matched.Printer.EndOfLine
                            Csff.Printer.EndOfLine.CrLf
                            "Override EOL."

                        Expect.isFalse matched.AutoEndOfLine "Override EOL is explicit."

                        Expect.equal
                            (settings "foo bar.cs")
                            config.Settings
                            "One space does not match.")
            }
            test "YAML explicit keys can start on an indented following line" {
                reads
                    [
                        "?\n  printWidth\n: 80\n", mapping [ "printWidth", plain "80" ]
                        "? # key follows\n  printWidth\n: 80\n",
                        mapping [ "printWidth", plain "80" ]
                        "?\n  'printWidth'\n: 80\n",
                        YamlNode.Mapping("", [| single "printWidth", plain "80" |])
                    ]

                withConfig "?\n  printWidth\n: 80\nuseTabs: true\nendOfLine: lf\n" (fun _ config ->
                    Expect.equal
                        config.Settings.Printer.Width
                        80
                        "Explicit key selects printWidth."

                    Expect.isTrue config.Settings.Printer.UseTabs "Tabs remain effective."

                    Expect.equal
                        config.Settings.Printer.EndOfLine
                        Csff.Printer.EndOfLine.Lf
                        "Explicit LF.")
            }
            test "YAML explicit values can start compact block sequences and mappings" {
                reads
                    [
                        "? overrides\n: - files: '*.cs'\n    printWidth: 40\n",
                        mapping
                            [
                                "overrides",
                                sequence
                                    [ mapping [ "files", single "*.cs"; "printWidth", plain "40" ] ]
                            ]
                        "? outer\n: inner: 80\n  other: 40\n",
                        mapping [ "outer", mapping [ "inner", plain "80"; "other", plain "40" ] ]
                        "? overrides\n: - ? files\n    : '*.cs'\n    ? printWidth\n    : 40\n",
                        mapping
                            [
                                "overrides",
                                sequence
                                    [ mapping [ "files", single "*.cs"; "printWidth", plain "40" ] ]
                            ]
                    ]

                withConfig
                    "? overrides\n: - files: '*.cs'\n    printWidth: 40\n    useTabs: true\n    endOfLine: crlf\n"
                    (fun directory config ->
                        let settings =
                            Configuration.forFile
                                (Some config)
                                (Path.Combine(directory, "probe.cs"))

                        Expect.equal config.Overrides.Length 1 "There is one compact override."
                        Expect.equal settings.Printer.Width 40 "The pattern matches C# files."
                        Expect.isTrue settings.Printer.UseTabs "The override uses tabs."

                        Expect.equal
                            settings.Printer.EndOfLine
                            Csff.Printer.EndOfLine.CrLf
                            "Override EOL.")

                Expect.throwsT<FormatException>
                    (fun () -> parse "overrides: - files: '*.cs'\n" |> ignore)
                    "An implicit colon still cannot introduce a compact sequence."
            }
            test "YAML compact block values require an explicit value indicator" {
                for input in
                    [
                        "? overrides: - {files: '*.cs', printWidth: 40}\n"
                        "? overrides: - files: '*.cs'\n    printWidth: 40\n"
                        "? 'overrides': - {files: '*.cs', printWidth: 40}\n"
                        "? files: inner: 80\n"
                        "? overrides\n : - {files: '*.cs', printWidth: 40}\n"
                        "? files\n : inner: 80\n"
                        "overrides:\n- ? files\n  : '*.cs'\n  ? printWidth: - 40\n"
                    ] do
                    Expect.throwsT<FormatException> (fun () -> parse input |> ignore) input

                reads
                    [
                        "? printWidth: 80\n",
                        YamlNode.Mapping("", [| mapping [ "printWidth", plain "80" ], plain "" |])
                        "files:\n  ? inner\n  : - 80\n",
                        mapping [ "files", mapping [ "inner", sequence [ plain "80" ] ] ]
                        "files:\n- ? inner\n  : - 80\n",
                        mapping
                            [ "files", sequence [ mapping [ "inner", sequence [ plain "80" ] ] ] ]
                    ]

                for input in
                    [ "? printWidth: 80\n"; "? overrides: [{files: '*.cs', printWidth: 40}]\n" ] do
                    Expect.throwsT<ArgumentException>
                        (fun () -> withConfig input (fun _ _ -> ()))
                        "Complex keys cannot become active formatter settings."

                withConfig
                    "? overrides\n: - {files: '*.cs', printWidth: 40}\n"
                    (fun directory config ->
                        let settings =
                            Configuration.forFile
                                (Some config)
                                (Path.Combine(directory, "probe.cs"))

                        Expect.equal
                            settings.Printer.Width
                            40
                            "An explicit value enables a compact list.")
            }
            test "an explicit block-scalar key names a property" {
                withConfig "? |-\n  printWidth\n: 80\n" (fun directory config ->
                    let settings =
                        Configuration.forFile (Some config) (Path.Combine(directory, "probe.cs"))

                    Expect.equal
                        settings.Printer.Width
                        80
                        "An explicit block-scalar key names the property.")
            }
            test "a multiline quoted key is still a syntax error" {
                Expect.throwsT<FormatException>
                    (fun () -> parse "  ? \"printWidth\\\n \": 80\n" |> ignore)
                    "A quoted key may not run onto a following line."
            }
            test "a compact explicit key cannot begin with a property" {
                Expect.throwsT<FormatException>
                    (fun () -> parse "? &key - 80\n: 40\n" |> ignore)
                    "A compact explicit key cannot begin with a property."
            }
            test "YAML anchor and alias names stop at delimiters in block context" {
                for delimiter in [ ","; "]"; "}" ] do
                    for name in [ "w"; "width:value"; "width:" ] do
                        for input in
                            [
                                "printWidth: &" + name + delimiter + " 80\n"
                                "files: &" + name + " 80\nprintWidth: *" + name + delimiter + "\n"
                                "&" + name + delimiter + " printWidth: 80\n"
                                "files: &" + name + " printWidth\n*" + name + delimiter + " : 80\n"
                            ] do
                            Expect.throwsT<FormatException> (fun () -> parse input |> ignore) input

                    for input in
                        [
                            "printWidth: &" + delimiter + " 80\n"
                            "files: &w 80\nprintWidth: *" + delimiter + "\n"
                        ] do
                        Expect.throwsT<FormatException>
                            (fun () -> parse input |> ignore)
                            "A delimiter cannot supply an empty anchor or alias name."
            }
            test "YAML name delimiters remain flow collection boundaries" {
                reads
                    [
                        "files: [&w 80, *w, *w]\n",
                        mapping [ "files", sequence [ plain "80"; plain "80"; plain "80" ] ]
                        "files: {first: &w 80, second: *w}\n",
                        mapping [ "files", mapping [ "first", plain "80"; "second", plain "80" ] ]
                        "files: [&w, *w]\n", mapping [ "files", sequence [ plain ""; plain "" ] ]
                        "files: {first: &w, second: *w}\n",
                        mapping [ "files", mapping [ "first", plain ""; "second", plain "" ] ]
                        "files: [&w]\n", mapping [ "files", sequence [ plain "" ] ]
                        "files: {first: &w}\n", mapping [ "files", mapping [ "first", plain "" ] ]
                    ]

                for delimiter in [ ","; "]"; "}" ] do
                    for input in
                        [
                            "overrides: [{files: '*.cs', printWidth: &w" + delimiter + " 80}]\n"
                            "files: &w 80\noverrides: [{files: '*.cs', printWidth: *w"
                            + delimiter
                            + " 80}]\n"
                        ] do
                        Expect.throws
                            (fun () -> withConfig input (fun _ _ -> ()))
                            "A flow delimiter cannot be absorbed to activate a malformed setting."

                withConfig
                    "files: &w 80\noverrides: [{files: '*.cs', printWidth: *w, indentSize: 4}]\n"
                    (fun directory config ->
                        let settings =
                            Configuration.forFile
                                (Some config)
                                (Path.Combine(directory, "probe.cs"))

                        Expect.equal settings.Printer.Width 80 "A comma ends a valid alias."

                        Expect.equal
                            settings.Printer.IndentSize
                            4
                            "The following flow entry is read.")
            }
            test "YAML flow openers cannot immediately follow anchor or alias names" {
                for name in [ "rule"; "rule:value"; "rule:" ] do
                    for collection in [ "{files: '*.cs', printWidth: 40}"; "[80]" ] do
                        for input in
                            [
                                "overrides: [&" + name + collection + "]\n"
                                "files: &" + name + collection + "\n"
                                "printWidth: &"
                                + name
                                + " 80\nfiles: [*"
                                + name
                                + collection
                                + "]\n"
                                "files: &" + name + " 80\nprintWidth: *" + name + collection + "\n"
                                "files: &" + collection + "\n"
                                "files: *" + collection + "\n"
                            ] do
                            Expect.throwsT<FormatException> (fun () -> parse input |> ignore) input

                for separator in [ " "; "\t"; "\n  " ] do
                    reads
                        [
                            "files: [&rule" + separator + "{inner: 80}, *rule]\n",
                            mapping
                                [
                                    "files",
                                    sequence
                                        [
                                            mapping [ "inner", plain "80" ]
                                            mapping [ "inner", plain "80" ]
                                        ]
                                ]
                            "files: [&rule" + separator + "[80], *rule]\n",
                            mapping
                                [
                                    "files",
                                    sequence [ sequence [ plain "80" ]; sequence [ plain "80" ] ]
                                ]
                        ]

                withConfig
                    "overrides: [&rule {files: '*.cs', printWidth: 40}]\n"
                    (fun directory config ->
                        let settings =
                            Configuration.forFile
                                (Some config)
                                (Path.Combine(directory, "probe.cs"))

                        Expect.equal
                            settings.Printer.Width
                            40
                            "A separated flow opener remains valid.")
            }
            test "YAML explicit compact collections cannot carry leading properties" {
                for properties in
                    [
                        "&rule"
                        "!!seq"
                        "&rule !!seq"
                        "!!seq &rule"
                        "!<tag:yaml.org,2002:seq>"
                        "!<tag:yaml.org,2002:seq> &rule"
                    ] do
                    for input in
                        [
                            "? overrides\n: " + properties + " - {files: '*.cs', printWidth: 40}\n"
                            "? overrides\n: "
                            + properties
                            + " - files: '*.cs'\n    printWidth: 40\n"
                            "? files\n: outer:\n    ? inner\n    : " + properties + " - 80\n"
                        ] do
                        Expect.throwsT<FormatException> (fun () -> parse input |> ignore) input

                for properties in
                    [
                        "&rule"
                        "!!str"
                        "&rule !!str"
                        "!!str &rule"
                        "!!map"
                        "&rule !!map"
                        "!!map &rule"
                    ] do
                    let input = "? files\n: " + properties + " ? inner\n  : 80\n"
                    Expect.throwsT<FormatException> (fun () -> parse input |> ignore) input
            }
            test "YAML explicit compact values preserve key and item properties" {
                reads
                    [
                        "? files\n: &key inner: 80\n",
                        mapping [ "files", mapping [ "inner", plain "80" ] ]
                        "? files\n: !!str &key inner: 80\n",
                        mapping
                            [
                                "files",
                                YamlNode.Mapping(
                                    "",
                                    [| tagged (core "str") (plain "inner"), plain "80" |]
                                )
                            ]
                        "? files\n: &key !!str inner: 80\n",
                        mapping
                            [
                                "files",
                                YamlNode.Mapping(
                                    "",
                                    [| tagged (core "str") (plain "inner"), plain "80" |]
                                )
                            ]
                        "? files\n: ? inner\n  : 80\n",
                        mapping [ "files", mapping [ "inner", plain "80" ] ]
                    ]

                withConfig "? files\n: &key printWidth: 40\n? *key\n: 80\n" (fun _ config ->
                    Expect.equal
                        config.Settings.Printer.Width
                        80
                        "The anchor names the compact mapping's key.")

                for value in
                    [
                        "- {files: '*.cs', printWidth: 40}"
                        "- &rule {files: '*.cs', printWidth: 40}"
                        "- !!map {files: '*.cs', printWidth: 40}"
                        "- &rule !!map {files: '*.cs', printWidth: 40}"
                        "&rule\n  - {files: '*.cs', printWidth: 40}"
                        "!!seq\n  - {files: '*.cs', printWidth: 40}"
                        "&rule !!seq\n  - {files: '*.cs', printWidth: 40}"
                        "!!seq &rule\n  - {files: '*.cs', printWidth: 40}"
                        "&rule [{files: '*.cs', printWidth: 40}]"
                        "!!seq [{files: '*.cs', printWidth: 40}]"
                        "&rule !!seq [{files: '*.cs', printWidth: 40}]"
                        "!!seq &rule [{files: '*.cs', printWidth: 40}]"
                    ] do
                    withConfig ("? overrides\n: " + value + "\n") (fun directory config ->
                        let settings =
                            Configuration.forFile
                                (Some config)
                                (Path.Combine(directory, "probe.cs"))

                        Expect.equal
                            settings.Printer.Width
                            40
                            "Valid compact or separated overrides remain effective.")
            }
            test "YAML anchor and alias names permit internal and trailing colons" {
                for name in [ "width:value"; "width:" ] do
                    let input = "printWidth: &" + name + " 80\nindentSize: *" + name + "\n"
                    reads [ input, mapping [ "printWidth", plain "80"; "indentSize", plain "80" ] ]

                    reads
                        [
                            "printWidth: &" + name + " 80\nvalues: [*" + name + ", *" + name + "]\n",
                            mapping
                                [
                                    "printWidth", plain "80"
                                    "values", sequence [ plain "80"; plain "80" ]
                                ]
                            "values: [&" + name + " 80, *" + name + "]\n",
                            mapping [ "values", sequence [ plain "80"; plain "80" ] ]
                        ]

                    withConfig input (fun _ config ->
                        Expect.equal config.Settings.Printer.Width 80 "Anchored width."

                        Expect.equal
                            config.Settings.Printer.IndentSize
                            80
                            "Alias supplies indentation.")
            }
            test "YAML folded block scalars retain trailing physical breaks before chomping" {
                reads
                    [
                        "files: >+\n  x\n\n", mapping [ "files", folded "x\n\n" ]
                        "files: >+\n  x\n\n\n", mapping [ "files", folded "x\n\n\n" ]
                        "files: >\n  x\n  ", mapping [ "files", folded "x\n" ]
                        "files: >+\n  x\n  ", mapping [ "files", folded "x\n" ]
                        "files: >-\n  x\n  ", mapping [ "files", folded "x" ]
                        "files: >+\n  x\n\n  y\n\n", mapping [ "files", folded "x\ny\n\n" ]
                        "files: >+\n  x\n\nother: y\n",
                        mapping [ "files", folded "x\n\n"; "other", plain "y" ]
                        "files: |+\n  x\n\n", mapping [ "files", literal "x\n\n" ]
                    ]

                for input in [ "printWidth: !!int >+\n  80\n\n"; "printWidth: !!int >\n  80\n  " ] do
                    withConfig input (fun _ config ->
                        Expect.equal
                            config.Settings.Printer.Width
                            80
                            "Tagged integers trim the retained breaks.")
            }
            test "YAML trailing comments end plain scalars" {
                for input in
                    [
                        "files: foo #note\n  bar.cs\n"
                        "overrides:\n- files: foo #note\n    bar.cs\n  printWidth: 40\n"
                        "files: foo\n  bar #note\n  baz.cs\n"
                        "files: [foo #note\n  bar.cs]\n"
                    ] do
                    Expect.throwsT<FormatException>
                        (fun () -> parse input |> ignore)
                        "A comment ends the scalar."

                reads
                    [
                        "files: foo#note\n  bar.cs\n", mapping [ "files", plain "foo#note bar.cs" ]
                        "files: foo #note\nprintWidth: 80\n",
                        mapping [ "files", plain "foo"; "printWidth", plain "80" ]
                    ]
            }
            test "YAML Unicode escapes reject unpaired surrogates and preserve valid pairs" {
                for escape in
                    [
                        "\\uD800"
                        "\\uDBFF"
                        "\\uDC00"
                        "\\uDFFF"
                        "\\uD800x"
                        "\\uD800\\u0041"
                        "\\uD800\\uD800"
                        "\\U0000D800"
                    ] do
                    Expect.throwsT<FormatException>
                        (fun () -> parse ("files: \"" + escape + ".cs\"\n") |> ignore)
                        "Unicode escapes must encode complete scalar values."

                reads
                    [
                        "files: \"\\uD83D\\uDE00.cs\"\n",
                        mapping [ "files", double "\U0001F600.cs" ]
                        "files: \"\\uD83D\\U0000DE00.cs\"\n",
                        mapping [ "files", double "\U0001F600.cs" ]
                        "files: \"\\U0000D83D\\uDE00.cs\"\n",
                        mapping [ "files", double "\U0001F600.cs" ]
                        "files: \"\\U0000D83D\\U0000DE00.cs\"\n",
                        mapping [ "files", double "\U0001F600.cs" ]
                        "files: \"\\uD800\\uDC00.cs\"\n",
                        mapping [ "files", double "\U00010000.cs" ]
                        "files: \"\\uDBFF\\uDFFF.cs\"\n",
                        mapping [ "files", double "\U0010FFFF.cs" ]
                    ]

                withConfig
                    "overrides: [{files: \"\\uD83D\\uDE00.cs\", printWidth: 40}]\n"
                    (fun directory config ->
                        let settings =
                            Configuration.forFile
                                (Some config)
                                (Path.Combine(directory, "\U0001F600.cs"))

                        Expect.equal
                            settings.Printer.Width
                            40
                            "A surrogate pair matches its actual Unicode filename.")
            }
            test "YAML single-line flow collection parsing scales with input length" {
                let input count =
                    "overrides: ["
                    + String.concat "," (List.replicate count "{files: '*.cs', printWidth: 40}")
                    + "]\n"

                let small = input 1500, 1500
                let large = input 12000, 12000

                let measure (text, count) =
                    let timer = System.Diagnostics.Stopwatch.StartNew()
                    let documents = parse text
                    timer.Stop()

                    match documents with
                    | [| YamlNode.Mapping("", [| _, YamlNode.Sequence("", items) |]) |] ->
                        Expect.equal items.Length count "Every override entry is read."
                    | _ -> failtest "Expected a document containing the complete override sequence."

                    timer.Elapsed.TotalMilliseconds

                measure small |> ignore
                measure large |> ignore
                let timings = Array.init 5 (fun _ -> measure small, measure large)

                let median values =
                    Array.sort values |> fun values -> values[values.Length / 2]

                let smallTime = timings |> Array.map fst |> median
                let largeTime = timings |> Array.map snd |> median

                Expect.isLessThan
                    largeTime
                    (smallTime * 24.0 + 10.0)
                    $"Eight times the input must stay below quadratic scaling (small={smallTime:F2}ms, large={largeTime:F2}ms)."
            }
            testPropertyWithConfig
                { FsCheckConfig.defaultConfig with
                    maxTest = 300
                    replay = Some(20261007UL, 11400714819323198485UL, None)
                }
                "YAML written in block style reads back as the nodes it was written from"
                (Prop.forAll (Arb.fromGen document) (fun (text, expected) ->
                    Expect.equal (parse text) [| expected |] text))
        ]
