module Csff.Tests.CorpusComparisonTests

open System
open System.IO
open System.Text.Json
open Expecto
open System.Text

let private split (text: string) =
    text.Trim('\n').Split('\n') |> Array.map (fun line -> line.TrimEnd '\r')

let private differences reference candidate =
    let comparison = CorpusComparison.hunks "a.cs" (split reference) (split candidate)
    comparison.Hunks, comparison.Alignment

let private keys reference candidate =
    let found, _ = differences reference candidate
    found |> Seq.map CorpusComparison.key |> Seq.toList

let private withTrees action =
    let root =
        Path.Combine(Path.GetTempPath(), "csff-corpus-" + Guid.NewGuid().ToString("N"))

    let reference = Path.Combine(root, "reference")
    let candidate = Path.Combine(root, "candidate")
    Directory.CreateDirectory reference |> ignore
    Directory.CreateDirectory candidate |> ignore

    try
        action root reference candidate
    finally
        Directory.Delete(root, true)

let private write directory relative (text: string) =
    let path = Path.Combine(directory, relative)
    Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
    File.WriteAllText(path, text)

let private writeBytes directory relative (bytes: byte array) =
    let path = Path.Combine(directory, relative)
    Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
    File.WriteAllBytes(path, bytes)

let private quietly (action: unit -> int) =
    let before = Console.Out

    try
        Console.SetOut(new StringWriter())
        action ()
    finally
        Console.SetOut before

let private printed (action: unit -> int) =
    let before = Console.Out
    let collected = new StringWriter()

    try
        Console.SetOut collected
        action () |> ignore
        collected.ToString()
    finally
        Console.SetOut before

let private shapes =
    testList
        "shapes"
        [
            test "a shape keeps punctuation and drops names" {
                Expect.equal
                    (CorpusComparison.shape "        Foo.Bar(1, longName);")
                    "x.x(x, x);"
                    "identifiers and literals carry no layout information"
            }

            test "a shape ignores how far the line is indented" {
                Expect.equal
                    (CorpusComparison.shape "    return a;")
                    (CorpusComparison.shape "                return b;")
                    "indentation is carried as a delta, not as part of the shape"
            }

            test "a blank line has a shape of its own" {
                Expect.equal (CorpusComparison.shape "    ") "(blank)" "a blank line"
                Expect.equal (CorpusComparison.shape "") "(blank)" "an empty line"
            }

            test "a shape distinguishes where the spaces are" {
                Expect.notEqual
                    (CorpusComparison.shape "byte* bytes,")
                    (CorpusComparison.shape "byte*bytes,")
                    "The pointer declarator spacing remains visible."
            }

            test "a literal's contents do not split one decision in two" {
                Expect.equal
                    (CorpusComparison.shape "[Fact(Skip = \"a.b\")]")
                    (CorpusComparison.shape "[Fact(Skip = \"ab\")]")
                    "the punctuation inside a literal is not layout"
            }

            test "a shape ends a literal where the literal ends" {
                Expect.equal
                    (CorpusComparison.shape "f(@\"a\"\"b\", \u0027c\u0027, \"d\\\"e\") + 1;")
                    (CorpusComparison.shape "f(@\"z\", \u0027q\u0027, \"w\") + 2;")
                    "three literals, then the same tail"
            }

            test "a comment's words are no more layout than an identifier's" {
                Expect.equal
                    (CorpusComparison.shape "a(); // a Windows-1252 en dash \u0096")
                    (CorpusComparison.shape "a(); // an em dash \u0097")
                    "the same line with the same comment in the same place"

                Expect.equal (CorpusComparison.shape "// only a comment") "//x" "its own marker"
                Expect.notEqual (CorpusComparison.shape "/* block */") "//x" "and its own kind"
            }

            test "the lexer decides what a literal is" {
                Expect.equal
                    (CorpusComparison.shape "f(0x1e+2);")
                    (CorpusComparison.shape "f(0x1f+2);")
                    "the hex digit e is not an exponent marker"

                Expect.equal
                    (CorpusComparison.shape "[InlineData(.5)]")
                    (CorpusComparison.shape "[InlineData(0.5)]")
                    "a leading-dot real is a number"

                Expect.equal
                    (CorpusComparison.shape "f($$\"\"\"a{b\"\"\") + 1;")
                    (CorpusComparison.shape "f($$\"\"\"ab\"\"\") + 2;")
                    "two dollars need two braces to open a hole"
            }

            test "a literal inside an interpolation is still one literal" {
                Expect.equal
                    (CorpusComparison.shape "f($\"{M(\"a.b\")}\");")
                    (CorpusComparison.shape "f($\"{M(\"ab\")}\");")
                    "one decision, whatever the nested string holds"
            }

            test "a number's own punctuation is not layout" {
                Expect.equal
                    (CorpusComparison.shape "[InlineData(1.5)]")
                    (CorpusComparison.shape "[InlineData(1)]")
                    "one rewrap, whatever the number is"

                Expect.equal
                    (CorpusComparison.shape "f(0x1F_00, 1e-9, 3.14m);")
                    (CorpusComparison.shape "f(1, 2, 3);")
                    "a radix prefix, an exponent and a suffix all belong to the number"
            }

            test "a number stops where the number stops" {
                Expect.equal (CorpusComparison.shape "a[1..2];") "x[x..x];" "a range"
                Expect.equal (CorpusComparison.shape "f(1, 2);") "x(x, x);" "two arguments"
            }

            test "a raw interpolated string holds its nested literal" {
                Expect.equal
                    (CorpusComparison.shape "f($\"\"\"{M(\"\"\"a.b\"\"\")}\"\"\");")
                    (CorpusComparison.shape "f($\"\"\"{M(\"\"\"ab\"\"\")}\"\"\");")
                    "one decision, whatever the nested string holds"
            }

            test "a line continuing a multiline literal is read in its file's context" {
                let file = "f(\"\"\"\nbody\n\"\"\", arg);\n"

                let struct (shapes, _, _) =
                    CorpusComparison.shapesOf file (file.TrimEnd('\n').Split '\n')

                Expect.equal shapes[2] "x, x);" "the literal ends, then a comma and a call"

                let tight = file.Replace("\"\"\", arg", "\"\"\",arg")

                let struct (tighter, _, _) =
                    CorpusComparison.shapesOf tight (tight.TrimEnd('\n').Split '\n')

                Expect.notEqual tighter[2] shapes[2] "so the comma's space is visible"
            }

            test "a directive is named by the word after its hash" {
                let shapeOf (line: string) =
                    let struct (shapes, _, _) = CorpusComparison.shapesOf line [| line |]
                    shapes[0]

                Expect.equal (shapeOf "#nullable enable") "#nullable" "its own name"
                Expect.equal (shapeOf "#pragma warning disable 1591") "#pragma" "and this one"
                Expect.equal (shapeOf "    #endregion") "#endregion" "whatever the lexer calls it"
                Expect.notEqual (shapeOf "#if DEBUG") (shapeOf "#else") "two directives, two shapes"
            }

            test "a shape collapses a run of blanks but keeps one" {
                Expect.equal (CorpusComparison.shape "a  +   b") "x + x" "runs of blanks"
            }
        ]

let private alignment =
    testList
        "alignment"
        [
            test "a block that moves is one hunk, not one per line" {
                let reference = "class C\n{\n    a();\n    b();\n    c();\n}"
                let candidate = "class C\n{\n        a();\n        b();\n        c();\n}"
                let found, _ = differences reference candidate
                Expect.equal (List.ofSeq found |> List.length) 1 "one decision"
                let hunk = found[0]
                Expect.isTrue hunk.IndentOnly "the content is the same"
                Expect.equal hunk.Delta 4 "four columns to the right"
                Expect.equal hunk.Span 3 "three lines moved"
                Expect.equal hunk.Line 3 "reported where the run starts"
                Expect.equal (CorpusComparison.key hunk) "indentation +4" "named by its delta alone"
            }

            test "two different shifts stay two hunks" {
                let found, _ = differences "    a;\n    b;" "        a;\n            b;"
                Expect.equal (List.ofSeq found |> List.length) 2 "two deltas, two decisions"

                Expect.equal
                    (found |> Seq.map CorpusComparison.key |> Seq.toList)
                    [ "indentation +4"; "indentation +8" ]
                    "each named by its own delta"
            }

            test "a long run of equal lines does not slide" {
                let table indent =
                    [| for _ in 1..200 -> String(' ', indent) + "0x00," |] |> String.concat "\n"

                let comparison =
                    CorpusComparison.hunks
                        "a.cs"
                        (split ("int[] x =\n{\n" + table 4 + "\n};"))
                        (split ("int[] x =\n{\n" + table 8 + "\n};"))

                Expect.equal comparison.Alignment CorpusComparison.Exact "inside the bound"

                Expect.equal
                    (List.ofSeq comparison.Hunks |> List.length)
                    1
                    "one shift of two hundred lines"

                Expect.equal comparison.Hunks[0].Span 200 "the whole run"
            }

            test "a rewrap is one hunk spanning the lines it replaced" {
                let found, _ = differences "var a = new T(\n    1,\n    2);" "var a = new T(1, 2);"

                Expect.equal (List.ofSeq found |> List.length) 1 "one decision"
                Expect.equal found[0].Span 3 "the larger side"
                Expect.equal found[0].Line 1 "where the region opens"
                Expect.isFalse found[0].IndentOnly "the content changed"
            }

            test "an added line is reported against the reference line it follows" {
                let found, _ = differences "a();\nb();" "a();\nextra();\nb();"
                Expect.equal (List.ofSeq found |> List.length) 1 "one addition"
                Expect.equal found[0].Reference CorpusComparison.absent "nothing was there"
                Expect.equal found[0].Candidate "extra();" "the line added"
                Expect.equal found[0].Line 2 "after the first line, not line zero"
            }

            test "a removed line keeps its own position" {
                let found, _ = differences "a();\ngone();\nb();" "a();\nb();"
                Expect.equal (List.ofSeq found |> List.length) 1 "one removal"
                Expect.equal found[0].Reference "gone();" "the line removed"
                Expect.equal found[0].Candidate CorpusComparison.absent "nothing replaced it"
                Expect.equal found[0].Line 2 "the line it was on"
            }

            test "a later hunk knows where it is on the candidate side" {
                let comparison =
                    CorpusComparison.hunks
                        "a.cs"
                        [| "a(1);"; "b();"; "c();"; "d();" |]
                        [| "a("; "    1"; ");"; "b();"; "c();"; "dX();" |]

                Expect.equal comparison.Hunks.Count 2 "the rewrap and the renamed call"

                Expect.equal
                    (comparison.Hunks[1].Line, comparison.Hunks[1].Mirror)
                    (4, 6)
                    "line four here, line six there"
            }

            test "an approximate rejoin covers the lines it passed over" {
                let kept = [| for index in 1..40 -> $"keep{index}();" |]

                let widened =
                    [|
                        for index in 1..40 do
                            for inner in 1..30 do
                                yield $"added{index}x{inner}();"

                            yield kept[index - 1]
                    |]

                let comparison =
                    CorpusComparison.hunksWithin
                        4
                        "a.cs"
                        (CorpusComparison.fromLines kept)
                        (CorpusComparison.fromLines widened)

                Expect.equal
                    comparison.Alignment
                    CorpusComparison.Approximate
                    "far past the bound, so the scan does the work"

                Expect.equal
                    (comparison.Hunks |> Seq.sumBy (fun hunk -> hunk.Span))
                    1200
                    "forty rejoins of thirty lines each"
            }

            test "a collapse that crosses a literal is not called layout" {
                let name reference candidate =
                    let comparison =
                        CorpusComparison.hunksWithin
                            CorpusComparison.differenceBound
                            "a.cs"
                            (CorpusComparison.sideOf [| reference |])
                            (CorpusComparison.sideOf [| candidate |])

                    comparison.Hunks |> Seq.map CorpusComparison.key |> Seq.exactlyOne

                Expect.equal
                    (name "var s = \"a  b\";" "var s = \"a b\";")
                    "text, not layout: x x = x;"
                    "the string's value changed"

                Expect.equal
                    (name "var s = a  +  b;" "var s = a + b;")
                    "internal whitespace: x x = x + x;"
                    "outside a literal the same collapse is still layout"

                Expect.equal
                    (name "var s = \"a b\" + c  +  d;" "var s = \"a b\" + c + d;")
                    "internal whitespace: x x = x + x + x;"
                    "a literal that did not change does not make the line content"

                Expect.equal
                    (name "var s = 'a';" "var s = ' ';")
                    "text, not layout: x x = x;"
                    "a character literal is its value too"

                Expect.equal
                    (name "f(a,  b);\u00a0" "f(a, b);")
                    "internal whitespace: x(x, x);"
                    "a boundary blank outside a literal is still trimmed"

                Expect.equal
                    (name "var s = \"a\u00a0 b\";" "var s = \"a b\";")
                    "text, not layout: x x = x;"
                    "but inside a literal it is value, whatever kind of blank it is"

                let whole reference candidate =
                    let split (text: string) = text.TrimEnd('\n').Split '\n'

                    let comparison =
                        CorpusComparison.hunksWithin
                            CorpusComparison.differenceBound
                            "a.cs"
                            (CorpusComparison.sideOf (split reference))
                            (CorpusComparison.sideOf (split candidate))

                    comparison.Hunks |> Seq.map CorpusComparison.key |> Seq.toList

                Expect.equal
                    (whole
                        "var  s = \"\"\"  \n    body\n    \"\"\";\n"
                        "var s = \"\"\"\n    body\n    \"\"\";\n")
                    [ "internal whitespace: x x = x" ]
                    "a raw string's opening-fence padding is layout, not its value"
            }

            test "identical files produce nothing" {
                let found, kind = differences "a();\nb();" "a();\nb();"
                Expect.isEmpty found "no differences"
                Expect.equal kind CorpusComparison.Exact "exactly aligned"
            }

            test "a file that runs past the difference bound is marked approximate" {
                let reference = [| for index in 1..40 -> $"reference {index};" |]
                let candidate = [| for index in 1..40 -> $"candidate {index};" |]

                let comparison =
                    CorpusComparison.hunksWithin
                        4
                        "a.cs"
                        (CorpusComparison.fromLines reference)
                        (CorpusComparison.fromLines candidate)

                Expect.equal
                    comparison.Alignment
                    CorpusComparison.Approximate
                    "far beyond four differences"

                Expect.isNonEmpty comparison.Hunks "the fallback still reports"

                Expect.all
                    comparison.Hunks
                    (fun hunk -> hunk.Approximate)
                    "every hunk from an approximate alignment says so"

                Expect.all
                    comparison.Hunks
                    (fun hunk -> (CorpusComparison.key hunk).EndsWith "[approximate]")
                    "and never joins an exactly aligned cluster"
            }

            test "the same files within the bound are aligned exactly" {
                let reference = [| for index in 1..40 -> $"reference {index};" |]
                let candidate = [| for index in 1..40 -> $"candidate {index};" |]

                let comparison =
                    CorpusComparison.hunksWithin
                        CorpusComparison.differenceBound
                        "a.cs"
                        (CorpusComparison.fromLines reference)
                        (CorpusComparison.fromLines candidate)

                Expect.equal
                    comparison.Alignment
                    CorpusComparison.Exact
                    "eighty differences, bound of three thousand"
            }
        ]

let private grouping =
    testList
        "grouping"
        [
            test "clusters count lines, files and sites apart" {
                let found = ResizeArray<CorpusComparison.Hunk>()
                found.AddRange (CorpusComparison.hunks "one.cs" [| "a(" |] [| "a" |]).Hunks
                found.AddRange (CorpusComparison.hunks "two.cs" [| "b(" |] [| "b" |]).Hunks

                found.AddRange
                    (CorpusComparison.hunks "two.cs" [| "x"; "    y" |] [| "x"; "        y" |])
                        .Hunks

                let grouped = CorpusComparison.clusters found
                Expect.equal grouped.Length 2 "a shape cluster and an indentation cluster"
                Expect.equal grouped[0].Key "x(  ==>  x" "the larger cluster first"
                Expect.equal grouped[0].Lines 2 "one line each"
                Expect.equal grouped[0].Files 2 "from two files"
                Expect.equal grouped[0].Sites.Count 2 "two sites"
                Expect.equal grouped[1].Key "indentation +4" "the smaller cluster second"
                Expect.equal grouped[1].Files 1 "one file"
            }

            test "clusters are ordered by the lines they cover" {
                let found = ResizeArray<CorpusComparison.Hunk>()

                let wide =
                    CorpusComparison.hunks
                        "one.cs"
                        [| "x"; "    a"; "    b"; "    c"; "y" |]
                        [| "x"; "        a"; "        b"; "        c"; "y" |]

                let narrow = CorpusComparison.hunks "two.cs" [| "p(" |] [| "p" |]
                found.AddRange narrow.Hunks
                found.AddRange wide.Hunks
                let grouped = CorpusComparison.clusters found

                Expect.equal
                    (grouped |> Array.map (fun cluster -> cluster.Key, cluster.Lines))
                    [| "indentation +4", 3; "x(  ==>  x", 1 |]
                    "three lines in one site outranks one line in one site"
            }
        ]

let private driver =
    testList
        "driver"
        [
            test "two trees that agree report nothing to do" {
                withTrees (fun _ reference candidate ->
                    write reference "a.cs" "class A { }\n"
                    write candidate "a.cs" "class A { }\n"

                    Expect.equal
                        (quietly (fun () -> CorpusComparison.run [| reference; candidate |]))
                        0
                        "identical trees")
            }

            test "a layout difference is reported as a cluster, in JSON too" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")

                    write
                        reference
                        "a.cs"
                        "class A\n{\n    [Fact(Skip = \"x\")]\n    void M() { }\n}\n"

                    write
                        candidate
                        "a.cs"
                        "class A\n{\n    [\n        Fact(Skip = \"x\")]\n    void M() { }\n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the trees differ"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let root = document.RootElement
                    Expect.equal (root.GetProperty("filesCompared").GetInt32()) 1 "one shared file"
                    Expect.equal (root.GetProperty("filesDiffering").GetInt32()) 1 "which differs"
                    let clusters = root.GetProperty "clusters"
                    Expect.equal (clusters.GetArrayLength()) 1 "one layout decision"
                    let first = clusters[0]

                    Expect.equal
                        (first.GetProperty("shape").GetString())
                        "[x(x = x)]  ==>  ["
                        "the shape that changed"

                    Expect.equal (first.GetProperty("lines").GetInt32()) 2 "one line became two"
                    Expect.equal (first.GetProperty("sitesOmitted").GetInt32()) 0 "nothing dropped"
                    let place = first.GetProperty("places")[0]

                    Expect.equal
                        (place.GetProperty("file").GetString())
                        "a.cs"
                        "named by relative path"

                    Expect.equal (place.GetProperty("line").GetInt32()) 3 "at the attribute")
            }

            test "a file on one side only is counted, not compared" {
                withTrees (fun _ reference candidate ->
                    write reference "a.cs" "class A { }\n"
                    write reference "b.cs" "class B { }\n"
                    write candidate "a.cs" "class A { }\n"

                    Expect.equal
                        (quietly (fun () -> CorpusComparison.run [| reference; candidate |]))
                        0
                        "the shared file agrees, so there is nothing to cluster")
            }

            test "a difference in line endings is a difference" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A\n{\n}\n"
                    write candidate "a.cs" "class A\r\n{\r\n}\r\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "reading the files as lines would call these identical"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let clusters = document.RootElement.GetProperty "clusters"
                    Expect.equal (clusters.GetArrayLength()) 1 "one whole-file difference"

                    Expect.equal
                        (clusters[0].GetProperty("shape").GetString())
                        "line endings lf  ==>  crlf"
                        "named in its own terms, not canonicalised as C#")
            }

            test "a missing final newline is a difference" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A { }\n"
                    write candidate "a.cs" "class A { }"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the printer's final newline is a printer decision"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let clusters = document.RootElement.GetProperty "clusters"

                    Expect.equal
                        (clusters[0].GetProperty("shape").GetString())
                        "final line terminated  ==>  unterminated"
                        "its own cluster")
            }

            test "a clean run replaces an earlier report" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A { }\n"
                    write candidate "a.cs" "class B { }\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "they differ"

                    write candidate "a.cs" "class A { }\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        0
                        "now they agree"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    Expect.equal
                        (document.RootElement.GetProperty("filesDiffering").GetInt32())
                        0
                        "the report says so rather than keeping the earlier clusters"

                    Expect.equal
                        (document.RootElement.GetProperty("clusters").GetArrayLength())
                        0
                        "no clusters")
            }

            test "a blank line at the end of a file is a difference" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A { }\n\n"
                    write candidate "a.cs" "class A { }\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "they differ"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let clusters = document.RootElement.GetProperty "clusters"

                    Expect.equal
                        (clusters[0].GetProperty("shape").GetString())
                        "(blank)  ==>  (nothing)"
                        "trimming every trailing newline would leave nothing to report")
            }

            test "line endings that move are reported even when both sides stay mixed" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A\r\n{\n}\n"
                    write candidate "a.cs" "class A\n{\r\n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "a summary of the file would call both sides mixed and stop"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let clusters = document.RootElement.GetProperty "clusters"

                    Expect.equal
                        (clusters[0].GetProperty("shape").GetString())
                        "line endings crlf  ==>  lf"
                        "named by the first line whose ending changed")
            }

            test "bytes no decoding agrees on are still compared" {
                withTrees (fun _ reference candidate ->
                    let comment suffix =
                        Array.append
                            (Text.Encoding.ASCII.GetBytes "class A { } // ")
                            [| suffix; 0x0Auy |]

                    writeBytes reference "a.cs" (comment 0x96uy)
                    writeBytes candidate "a.cs" (comment 0x97uy)

                    Expect.equal
                        (quietly (fun () -> CorpusComparison.run [| reference; candidate |]))
                        1
                        "the bytes differ, so the formatters disagree")
            }

            test "a site carries both coordinates into the report" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "a(1);\nb();\nc();\nd();\n"
                    write candidate "a.cs" "a(\n    1\n);\nb();\nc();\ndX();\n"

                    quietly (fun () ->
                        CorpusComparison.run [| reference; candidate; "--json"; path |])
                    |> ignore

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let places =
                        [
                            for cluster in
                                document.RootElement.GetProperty("clusters").EnumerateArray() do
                                for place in cluster.GetProperty("places").EnumerateArray() do
                                    place.GetProperty("line").GetInt32(),
                                    place.GetProperty("candidateLine").GetInt32()
                        ]

                    Expect.contains
                        places
                        (4, 6)
                        "the later site is on reference line four and candidate line six")
            }

            test "a file with a byte-order mark is read as what it is" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")

                    let source =
                        "class A\r\n{\r\n    void M()\r\n    {\r\n        x();\r\n    }\r\n}\r\n"

                    let mark = [| 0xFFuy; 0xFEuy |]

                    let utf16 (text: string) =
                        Array.append mark (Text.Encoding.Unicode.GetBytes text)

                    writeBytes reference "a.cs" (utf16 source)

                    writeBytes
                        candidate
                        "a.cs"
                        (utf16 (source.Replace("        x();", "            x();")))

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "they differ"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let clusters = document.RootElement.GetProperty "clusters"
                    Expect.equal (clusters.GetArrayLength()) 1 "one indentation shift"

                    Expect.equal
                        (clusters[0].GetProperty("shape").GetString())
                        "indentation +4"
                        "not a shape change full of NULs"

                    let place = clusters[0].GetProperty("places")[0]

                    Expect.equal
                        (place.GetProperty("line").GetInt32())
                        5
                        "on the line it is actually on, not twice that")
            }

            test "an encoding change is reported in the direction it happened" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")

                    writeBytes
                        reference
                        "a.cs"
                        (Array.append (Text.Encoding.ASCII.GetBytes "// ") [| 0xE9uy; 0x0Auy |])

                    writeBytes
                        candidate
                        "a.cs"
                        (Array.append
                            (Text.Encoding.ASCII.GetBytes "// ")
                            [| 0xC3uy; 0xA9uy; 0x0Auy |])

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the bytes differ"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let first = document.RootElement.GetProperty("clusters")[0]

                    Expect.equal
                        (first.GetProperty("shape").GetString())
                        "encoding single byte  ==>  utf-8"
                        "which way round it went")
            }

            test "an inserted line does not invent an ending change" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "a();\r\nb();\n"
                    write candidate "a.cs" "a();\r\n\r\nb();\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "a line was added"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let clusters = document.RootElement.GetProperty "clusters"

                    Expect.equal
                        [
                            for cluster in clusters.EnumerateArray() ->
                                cluster.GetProperty("shape").GetString()
                        ]
                        [ "(nothing)  ==>  (blank)" ]
                        "neither existing line changed how it ends")
            }

            test "trailing whitespace is not an indentation shift" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A\n{\n    a();\n}\n"
                    write candidate "a.cs" "class A\n{\n    a(); \n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "a space was added"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let first = document.RootElement.GetProperty("clusters")[0]

                    Expect.equal
                        (first.GetProperty("shape").GetString())
                        "trailing whitespace 0  ==>  1"
                        "trimming both ends called this an indentation shift of zero")
            }

            test "an ending that changes with its line is still reported" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "a();\n"
                    write candidate "a.cs" "    a();\r\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "both the indentation and the ending changed"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let shapes =
                        [
                            for cluster in
                                document.RootElement.GetProperty("clusters").EnumerateArray() ->
                                cluster.GetProperty("shape").GetString()
                        ]

                    Expect.containsAll
                        shapes
                        [ "indentation +4"; "line endings lf  ==>  crlf" ]
                        "taking only the lines that match would miss the ending")
            }

            test "context is decoded the way the comparison decoded it" {
                withTrees (fun _ reference candidate ->
                    let comment suffix =
                        Array.append
                            (Text.Encoding.ASCII.GetBytes "class A\n{\n    // dash ")
                            [| suffix; 0x0Auy; byte '}'; 0x0Auy |]

                    writeBytes reference "a.cs" (comment 0x96uy)
                    writeBytes candidate "a.cs" (comment 0x97uy)

                    let report =
                        printed (fun () ->
                            CorpusComparison.run [| reference; candidate; "--context"; "1" |])

                    let shown =
                        report.Split '\n'
                        |> Array.filter (fun line -> line.Contains ">    3 |")
                        |> Array.map (fun line -> line.Substring(line.IndexOf '|'))

                    Expect.equal shown.Length 2 "one line from each side"
                    Expect.notEqual shown[0] shown[1] "the two bytes are different characters")
            }

            test "a difference confined to a comment's text is named as such" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "a(); // one\n"
                    write candidate "a.cs" "a(); // two\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the text differs"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let first = document.RootElement.GetProperty("clusters")[0]

                    Expect.equal
                        (first.GetProperty("shape").GetString())
                        "text, not layout: x(); //x"
                        "rather than a shape printed against itself")
            }

            test "a rewrap that also shifts indentation is its own cluster" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A\n{\n    f(a, b);\n}\n"
                    write reference "b.cs" "class A\n{\n    f(c, d);\n}\n"
                    write candidate "a.cs" "class A\n{\n    f(\n        a, b);\n}\n"
                    write candidate "b.cs" "class A\n{\nf(\n    c, d);\n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "both files differ"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let shapes =
                        [
                            for cluster in
                                document.RootElement.GetProperty("clusters").EnumerateArray() ->
                                cluster.GetProperty("shape").GetString()
                        ]

                    Expect.containsAll
                        shapes
                        [ "x(x, x);  ==>  x("; "x(x, x);  ==>  x(, indentation -4" ]
                        "merging them would hide the indentation regression in one")
            }

            test "an ending change outlives a rewrap that consumes every line" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class C {}\n"
                    write candidate "a.cs" "class C\r\n{\r\n}\r\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the file was rewrapped"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let shapes =
                        [
                            for cluster in
                                document.RootElement.GetProperty("clusters").EnumerateArray() ->
                                cluster.GetProperty("shape").GetString()
                        ]

                    Expect.contains
                        shapes
                        "line endings lf  ==>  crlf"
                        "no pair of lines survives, but one style throughout each side still says it")
            }

            test "an approximate insertion is an insertion" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    let kept = [| for index in 1..4000 -> $"keep{index}();" |]
                    write reference "a.cs" (String.Join("\n", kept) + "\n")

                    write
                        candidate
                        "a.cs"
                        (String.Join("\n", [| for line in kept -> "\n" + line |]).TrimStart '\n'
                         + "\n")

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "four thousand blank lines were added"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let first = document.RootElement.GetProperty("clusters")[0]

                    Expect.equal
                        (first.GetProperty("shape").GetString())
                        "(nothing)  ==>  (blank)   [approximate]"
                        "not a replacement of the line that follows each one")
            }

            test "an indentation shift keeps its name when the shape is unchanged" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A\n{\n    void M() =>\n        f(1);\n}\n"
                    write reference "b.cs" "class B\n{\n    void M() =>\n        f(1);\n}\n"
                    write candidate "a.cs" "class A\n{\n    void M() =>\n        g(2, 3);\n}\n"
                    write candidate "b.cs" "class B\n{\n    void M() =>\n    g(2, 3);\n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "both differ"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let shapes =
                        [
                            for cluster in
                                document.RootElement.GetProperty("clusters").EnumerateArray() ->
                                cluster.GetProperty("shape").GetString()
                        ]

                    Expect.exists
                        shapes
                        (fun shape -> shape.EndsWith ", indentation -4")
                        "the shift is part of the name even where the shape did not change")
            }

            test "a spaces-to-tabs conversion is one decision at every depth" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")

                    write
                        reference
                        "a.cs"
                        "class A\n{\n    void M()\n    {\n        x();\n    }\n}\n"

                    write candidate "a.cs" "class A\n{\n\tvoid M()\n\t{\n\t\tx();\n\t}\n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the indentation was rewritten"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let clusters = document.RootElement.GetProperty "clusters"

                    Expect.equal
                        (clusters.GetArrayLength())
                        1
                        "counting a tab as one character gave a different shift per depth"

                    Expect.equal
                        (clusters[0].GetProperty("shape").GetString())
                        "indentation style spaces  ==>  tabs"
                        "named for what changed")
            }

            test "an ending that a rewrap consumed is still found" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "a();\nf(x);\r\nb();\n"
                    write candidate "a.cs" "a();\nf(\n    x);\nb();\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the only CRLF line was rewrapped into LF lines"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let shapes =
                        [
                            for cluster in
                                document.RootElement.GetProperty("clusters").EnumerateArray() ->
                                cluster.GetProperty("shape").GetString()
                        ]

                    Expect.contains
                        shapes
                        "line endings crlf  ==>  lf"
                        "neither file is of one style and the changed lines are unpaired")
            }

            test "the earliest ending change is the one reported" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "a();\nb();\r\n"
                    write candidate "a.cs" "    a();\r\nb();\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "both lines changed how they end"

                    use document = JsonDocument.Parse(File.ReadAllText path)

                    let ending =
                        [
                            for cluster in
                                document.RootElement.GetProperty("clusters").EnumerateArray() do
                                if
                                    cluster.GetProperty("shape").GetString().StartsWith
                                        "line endings"
                                then
                                    cluster.GetProperty("shape").GetString()
                        ]

                    Expect.equal
                        ending
                        [ "line endings lf  ==>  crlf" ]
                        "an indentation change on line one must not promote line two's ending")
            }

            test "two roots that share no path are a usage error" {
                withTrees (fun _ reference candidate ->
                    write reference "one/x.cs" "class A { }\n"
                    write candidate "two/y.cs" "class B { }\n"

                    Expect.equal
                        (quietly (fun () -> CorpusComparison.run [| reference; candidate |]))
                        2
                        "the wrong root must not pass as agreement")
            }

            test "a directory link is not followed" {
                withTrees (fun _ reference candidate ->
                    write reference "inner/x.cs" "class A { }\n"
                    write candidate "inner/x.cs" "class A { }\n"

                    let linked =
                        try
                            Directory.CreateSymbolicLink(
                                Path.Combine(reference, "inner", "loop"),
                                ".."
                            )
                            |> ignore

                            true
                        with _ ->
                            false

                    if linked then
                        Expect.equal
                            (quietly (fun () -> CorpusComparison.run [| reference; candidate |]))
                            0
                            "following the link would run until the path grew too long")
            }

            test "blanks a string owns are content, not indentation" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")

                    write
                        reference
                        "a.cs"
                        "class A\n{\n    const string S = @\"\n    body\n\";\n}\n"

                    write
                        candidate
                        "a.cs"
                        "class A\n{\n    const string S = @\"\n        body\n\";\n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "the string's value changed"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let first = document.RootElement.GetProperty("clusters")[0]

                    Expect.equal
                        (first.GetProperty("shape").GetString())
                        "literal text 4  ==>  8"
                        "an indentation cluster would have hidden it among block moves")
            }

            test "a collapsed run of blanks is layout, not text" {
                withTrees (fun root reference candidate ->
                    let path = Path.Combine(root, "clusters.json")
                    write reference "a.cs" "class A\n{\n    var x = a  + b;\n}\n"
                    write candidate "a.cs" "class A\n{\n    var x = a + b;\n}\n"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--json"; path |]))
                        1
                        "two spaces became one"

                    use document = JsonDocument.Parse(File.ReadAllText path)
                    let first = document.RootElement.GetProperty("clusters")[0]

                    Expect.equal
                        (first.GetProperty("shape").GetString())
                        "internal whitespace: x x = x + x;"
                        "a shape collapses blank runs, so equal shapes are not equal layout")
            }

            test "context marks only the side that changed" {
                withTrees (fun _ reference candidate ->
                    write reference "a.cs" "a();\nb();\n"
                    write candidate "a.cs" "a();\nextra();\nb();\n"

                    let report =
                        printed (fun () ->
                            CorpusComparison.run [| reference; candidate; "--context"; "1" |])

                    let marked =
                        report.Split '\n'
                        |> Array.filter (fun line -> line.Contains " > ")
                        |> Array.map (fun line -> line.Trim().Split(' ')[0])

                    Expect.equal
                        marked
                        [| "candidate" |]
                        "the reference contributes nothing, so none of its lines changed")
            }

            test "the driver refuses what it cannot answer" {
                withTrees (fun root reference candidate ->
                    write reference "a.cs" "class A { }\n"
                    write candidate "a.cs" "class A { }\n"

                    Expect.equal (quietly (fun () -> CorpusComparison.run [||])) 2 "no directories"

                    Expect.equal
                        (quietly (fun () -> CorpusComparison.run [| reference |]))
                        2
                        "one directory"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; candidate; "--rubbish" |]))
                        2
                        "an option it does not have"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| Path.Combine(root, "absent"); candidate |]))
                        2
                        "a reference directory holding no C#"

                    Expect.equal
                        (quietly (fun () ->
                            CorpusComparison.run [| reference; Path.Combine(root, "absent") |]))
                        2
                        "a candidate directory holding no C#")
            }
        ]

let private shrinking =
    testList
        "shrinking"
        [
            test "a reduction keeps only what the test needs" {
                let lines = [| for index in 1..40 -> $"line {index}" |]
                let needed = set [ "line 7"; "line 23" ]
                let differs (trial: string array) = Set.isSubset needed (set trial)
                let kept = Shrink.reduce differs lines
                Expect.equal (set kept) needed "everything else came out"
            }

            test "a reduction keeps a line it cannot remove" {
                let kept = Shrink.reduce (fun _ -> false) [| "a"; "b"; "c" |]
                Expect.equal kept [| "a"; "b"; "c" |] "no removal was accepted"
            }

            test "a reduction stops where every line matters" {
                let lines = [| "a"; "b"; "c" |]
                let kept = Shrink.reduce (fun trial -> trial.Length = 3) lines
                Expect.equal kept lines "each removal broke the test"
            }

            test "a byte-order mark whose newline is more than one byte is refused" {
                let asBytes (bytes: byte array) = Encoding.Latin1.GetString bytes

                Expect.equal
                    (Shrink.markedEncoding (asBytes [| 0xffuy; 0xfeuy; 0x00uy; 0x00uy |]))
                    (Some "UTF-32LE")
                    "four bytes, little endian"

                Expect.equal
                    (Shrink.markedEncoding (asBytes [| 0x00uy; 0x00uy; 0xfeuy; 0xffuy |]))
                    (Some "UTF-32BE")
                    "four bytes, big endian"

                Expect.equal
                    (Shrink.markedEncoding (asBytes [| 0xffuy; 0xfeuy; 0x41uy; 0x00uy |]))
                    (Some "UTF-16LE")
                    "two bytes, little endian"

                Expect.equal
                    (Shrink.markedEncoding (asBytes [| 0xfeuy; 0xffuy; 0x00uy; 0x41uy |]))
                    (Some "UTF-16BE")
                    "two bytes, big endian"

                Expect.equal
                    (Shrink.markedEncoding (asBytes [| 0xefuy; 0xbbuy; 0xbfuy; 0x41uy |]))
                    None
                    "a UTF-8 mark is safe to split"

                Expect.equal (Shrink.markedEncoding "class C { }") None "and so is no mark"
            }

            test "the reduced snippet is shown in its own encoding" {
                let utf8 = Encoding.Latin1.GetString(Encoding.UTF8.GetBytes "var s = \"café\";")
                Expect.notEqual utf8 "var s = \"café\";" "the bytes are not the text"
                Expect.equal (Shrink.display utf8) "var s = \"café\";" "but they display as it"

                let windows = Encoding.Latin1.GetString [| 0x2fuy; 0x2fuy; 0x20uy; 0x96uy |]
                Expect.equal (Shrink.display windows) windows "invalid UTF-8 stays as bytes"
            }

            test "reading a file normalises nothing about it" {
                for text in [ "a\r\nb\r\n"; "a\nb\n"; "a\n\n\n"; "a"; "" ] do
                    Expect.equal
                        (String.Join('\n', Shrink.linesOf text))
                        text
                        "the lines join back to the file"

                let crlf = Shrink.linesOf "a\r\nb"
                Expect.equal crlf.Length 2 "a CRLF file has two lines"
                Expect.equal crlf[0] "a\r" "and the first keeps its return"
            }

            test "a reduction never empties the file" {
                let kept = Shrink.reduce (fun trial -> trial.Length >= 0) [| "a"; "b" |]
                Expect.isNonEmpty kept "a predicate that accepts anything still leaves a line"
            }
        ]

let tests =
    TestList([ shapes; alignment; grouping; driver; shrinking ], Normal)
    |> testLabel "corpus comparison"
    |> testSequenced
