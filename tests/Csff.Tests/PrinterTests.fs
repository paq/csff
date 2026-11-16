module Csff.Tests.PrinterTests

open System
open System.Runtime.CompilerServices
open System.IO
open Csff.Cli
open Csff.Lexer
open Csff.Parser
open Csff.Conformance
open Csff.Printer
open Expecto
open Microsoft.CodeAnalysis.CSharp

let private text (doc: DocumentBuffer) (source: string) (value: string) =
    let start = source.IndexOf(value, StringComparison.Ordinal)

    if start < 0 then
        invalidArg (nameof value) "Fixture text must be a source slice."

    doc.AddText(source, start, value.Length)

let private outputText (printer: Printer) = printer.OutputText

let private print source options build =
    use doc = new DocumentBuffer()
    use printer = new Printer()
    build doc
    printer.Print(source, doc, options)
    outputText printer

let private expect source width expected build =
    let actual =
        print
            source
            { PrinterOptions.Default with
                Width = width
            }
            build

    Expect.equal actual expected "Document layout matches the expected output."

let private group (doc: DocumentBuffer) build =
    let id = doc.StartGroup()
    build ()
    doc.EndGroup()
    id

let private scope (doc: DocumentBuffer) start finish build =
    doc.AddTag(start)
    build ()
    doc.AddTag(finish)

let private ifBreak (doc: DocumentBuffer) target onBreak onFlat =
    doc.AddTag(Tag.StartIfBreak, target)
    onBreak ()
    doc.AddTag(Tag.Else)
    onFlat ()
    doc.AddTag(Tag.EndIfBreak)

let private conditional (doc: DocumentBuffer) alternatives =
    let id = doc.NewGroupId()
    doc.AddTag(Tag.StartConditionalGroup, id)

    for build in alternatives do
        scope doc Tag.StartAlternative Tag.EndAlternative build

    doc.AddTag(Tag.EndConditionalGroup)

let private allocatedWhilePrinting
    source
    (doc: DocumentBuffer)
    (printer: Printer)
    options
    iterations
    =
    let before = GC.GetAllocatedBytesForCurrentThread()

    for _ = 1 to iterations do
        printer.Print(source, doc, options)

    GC.GetAllocatedBytesForCurrentThread() - before

let private nestedIfSource levels statement =
    let text = Text.StringBuilder()
    text.Append "class C\n{\nvoid M()\n{\n" |> ignore

    for _ = 1 to levels do
        text.Append "if (true)\n{\n" |> ignore

    text.Append(statement: string).Append '\n' |> ignore

    for _ = 1 to levels do
        text.Append "}\n" |> ignore

    text.Append "}\n}\n" |> ignore
    text.ToString()

let private onStack size body =
    let mutable failure: exn = null

    let thread =
        Threading.Thread(
            Threading.ThreadStart(fun () ->
                try
                    body ()
                with error ->
                    failure <- error),
            size
        )

    thread.IsBackground <- true
    thread.Start()
    thread.Join()

    if not (isNull failure) then
        Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(failure).Throw()

let private nestedLambdaSource family constructor variant depth =
    let call = if constructor then "new C" else "F"
    let mutable expression = "0"

    for _ = 1 to depth do
        let arrow =
            match variant with
            | "arrow block" -> "=>/* arrow */"
            | "arrow line" -> "=>// arrow\n"
            | _ -> "=>"

        let body =
            match variant with
            | "raw block" -> "{/* before */return " + expression + ";/* after */}"
            | "ignored" -> "{\n// csff-ignore\nreturn    " + expression + ";\n}"
            | _ -> expression

        let head = if family = "simple" then "x" else "()"

        let preceding =
            if family = "trailing" then
                if variant = "comma" then "0,/* comma */" else "0,"
            else
                ""

        expression <- call + "(" + preceding + head + arrow + body + ")"

    "class C{object M()=>" + expression + ";}"

let private nestedLambdaOptions =
    [
        for width in [ 20; 35; 40; 100 ] do
            for tabs in [ false; true ] do
                for crlf in [ false; true ] do
                    { PrinterOptions.Default with
                        Width = width
                        UseTabs = tabs
                        EndOfLine = if crlf then EndOfLine.CrLf else EndOfLine.Lf
                    }
    ]

let private deepLambdaOutput =
    [
        "empty",
        false,
        "plain",
        10,
        "8641880045FBC7BF064D99C330CE9C306FA1484AA537F1272EDB7CB1E600428E"
        "empty",
        false,
        "plain",
        12,
        "282FB9C68E9CFF601C9009B112E108E410BC4E7AE9BFF8BED81F066B35356068"
        "empty",
        false,
        "plain",
        8,
        "7C2B092EC5153BEB1DFB42A6D70E06361A0222734B955C6DDB91C0675150C8C2"
        "empty",
        true,
        "plain",
        10,
        "4EA5E239FBB5FE4CD0C0493DDF57831E2ECD7D7F3BA789FFF2AB538F43C23730"
        "empty",
        true,
        "plain",
        12,
        "889AD7D628597F4B38B3615C97A43DA30F06EEAFABE81571CFC0324917F9585B"
        "empty",
        true,
        "plain",
        8,
        "C3A7070C658E2C7919331027220496530A2F2D47463284C4F4645D9CB5B4BA6D"
        "simple",
        false,
        "plain",
        10,
        "17465433AE03B0A917AAB12DD6F4065DA8B400530B11C05A2F262050992AF7E0"
        "simple",
        false,
        "plain",
        12,
        "FE008B91B28BE84671B7148D602E93B2F35AE966A275504BEA91B599BFB04607"
        "simple",
        false,
        "plain",
        8,
        "9E395864DE69E6A53F0B37BF34983CD23C4CC3C9284C1217C3819C748F3D1E60"
        "simple",
        true,
        "plain",
        10,
        "333830C2AE02420B6DCE673B024C7047EBA29FCFCDBBAAA0F7930F40C82D9B9D"
        "simple",
        true,
        "plain",
        12,
        "A0BB6827AC84B12521BDC57AC12BC45E25B2E38159601F82CFAC92357A9D085E"
        "simple",
        true,
        "plain",
        8,
        "C6AE14E252A9B408740A6B8398F763FF4527056578747938CE7D39A316397A06"
        "trailing",
        false,
        "plain",
        10,
        "F53259893B4F04FC7D830DD52A49424DFBE835C29A0CAC754A0A434369E8F743"
        "trailing",
        false,
        "plain",
        12,
        "3E9D5336375A528EA73DBD92145C851E42E142C26D9B26ACA0047B75AF4CDD12"
        "trailing",
        false,
        "plain",
        8,
        "6155349D9D13B04A5DD1C716CC6289F4E5E00252D00AD4D649D613DBA9A2A41C"
        "trailing",
        true,
        "plain",
        10,
        "266B2F97566E8337145F7444B720BCC73D963C7E4FBFABE4A5BED3C7F56581C2"
        "trailing",
        true,
        "plain",
        12,
        "F5DA5B502A2BE9603CABCDC5CF46821261B03A8A4117E063B57A338232B79C37"
        "trailing",
        true,
        "plain",
        8,
        "F3261E9C5C159C2F60B2ABFAA4149AD38129AA1EA95AEEC2B7023DDCFC50A9D1"
    ]

let private nestedLambdaOutput =
    [
        "empty",
        false,
        "arrow block",
        2,
        "FAE93BC7D204541AB89C6952D61BAEEE62F132CC2BCA4F5B718F4672F784E29E"
        "empty",
        false,
        "arrow line",
        2,
        "A8E3CF5C7D374E4148A597FBFDAC74EB45E946BB06ABB1D44019C5B69E383FB5"
        "empty",
        false,
        "comma",
        2,
        "38251B6FD2E7E21DF8A8FEFAC45AF5BEB83C0E2B4C6F81BA1735148DA5AFB188"
        "empty",
        false,
        "ignored",
        2,
        "6800CA3725BEFA8CC99990A06F8CA16A3D62C334D58BC0D91B952448DD980E47"
        "empty",
        false,
        "plain",
        2,
        "38251B6FD2E7E21DF8A8FEFAC45AF5BEB83C0E2B4C6F81BA1735148DA5AFB188"
        "empty",
        false,
        "plain",
        4,
        "A7F10B7DC3EBFB30A58B77E28C54C8536C2BE530EE024223139E5F08A45D41A3"
        "empty",
        false,
        "plain",
        6,
        "55EABFED51C3B1438F3BA0206F5BE3874464AEDED4A9C2512A22E5233BA3D770"
        "empty",
        false,
        "raw block",
        2,
        "6416342307C178E6A02BC0CE2F8DC1A1F41F6BA77407771B43375724C9EA9A78"
        "empty",
        true,
        "arrow block",
        2,
        "A7FC9ECCF32134EAFF24AD8CCBCD99341BE3766DAD6E400867DC7C6C349E4525"
        "empty",
        true,
        "arrow line",
        2,
        "AE13B371750E8567EB441BB6CBAACE5EAC081783975B5A2B1F368EDCB5AA0EF0"
        "empty",
        true,
        "comma",
        2,
        "25F9DA4EDA846B425D3D2BD490A1C0930649428D0105EC825501725279EEA093"
        "empty",
        true,
        "ignored",
        2,
        "FB1EF09BC61974EAC26D0697A1FB1FC7120D3C0C7C3DB72623246F48C85A2354"
        "empty",
        true,
        "plain",
        2,
        "25F9DA4EDA846B425D3D2BD490A1C0930649428D0105EC825501725279EEA093"
        "empty",
        true,
        "plain",
        4,
        "76272AAFB99E2B5760CFA18A5895210C2956DABCADDE44D50263BD782DFB9DBD"
        "empty",
        true,
        "plain",
        6,
        "19082316F39506815970FB3558BEAFBA136FFA033EE522F2BBA9A0A536DF2F76"
        "empty",
        true,
        "raw block",
        2,
        "9F884F62BAEF925A806FDA4E2F161F44DC0F7B7DD1C6010F1D7E5E07ADF1FAC2"
        "simple",
        false,
        "arrow block",
        2,
        "C855F9357727781F8EE6B30EE681D51672C7F8BADF4EBCF15A00A80BE9611DFB"
        "simple",
        false,
        "arrow line",
        2,
        "401A6FC92B17166A34FE665CAB0271765C9B2D08180FE342D03706CB01463E74"
        "simple",
        false,
        "comma",
        2,
        "13ACB78109DA285632612EF61A04B68BBE0B69143FD7996BE6C8D6F47ADB5B43"
        "simple",
        false,
        "ignored",
        2,
        "D2A72EE852AA9DC907990C068CB01229F466AD2359FAF880CB83B60384AA35C0"
        "simple",
        false,
        "plain",
        2,
        "13ACB78109DA285632612EF61A04B68BBE0B69143FD7996BE6C8D6F47ADB5B43"
        "simple",
        false,
        "plain",
        4,
        "B8D886C1A8B71AE0F203E33DC1121ECD384717369F125F43BD7BEABCCC47BAE8"
        "simple",
        false,
        "plain",
        6,
        "81BCD69CAD33DAB296E101301B9E31E982E3F187055177D797E38C3BC7D4A105"
        "simple",
        false,
        "raw block",
        2,
        "081EDC0AC09047B638B27C13B1EF93E953B5A64A6DF17847C2DE12B6F4D4A507"
        "simple",
        true,
        "arrow block",
        2,
        "342E5E24603BF2316E7E726948215AEE1117B5DFC03DC76AC77AB7E8102910BA"
        "simple",
        true,
        "arrow line",
        2,
        "D29E45E12B48D03829DF17C9C73BB04BC354B02DF4217BDBD2DE8125FF31EAC2"
        "simple",
        true,
        "comma",
        2,
        "79B69BA9C58A82D4EC4D6E1DAE37F9C9E8B5B936406650D98B60D3B3008C4CAF"
        "simple",
        true,
        "ignored",
        2,
        "435911F1C2216A10516CE84A3C0F2BEE5D70F3286CD172F3298F43DB5D94C4FB"
        "simple",
        true,
        "plain",
        2,
        "79B69BA9C58A82D4EC4D6E1DAE37F9C9E8B5B936406650D98B60D3B3008C4CAF"
        "simple",
        true,
        "plain",
        4,
        "C0B3C0EC24756AC83FCC2FB5933C64EC4A32599205DE3E24314C9F548A67E78F"
        "simple",
        true,
        "plain",
        6,
        "71812E6289F60E22D7324DB7DDEE8F549F2761EF3AC22D064FE3F35CA0DCB7D5"
        "simple",
        true,
        "raw block",
        2,
        "75F55BFB9EAC6D74D544444650C3627EE49A3A410CEAD3EDE692614A829D2191"
        "trailing",
        false,
        "arrow block",
        2,
        "7EFC72AEC2E67079279918CBA241A81A9A15EC516A5748B5E240714AC6099C25"
        "trailing",
        false,
        "arrow line",
        2,
        "E1B85EF5245BFDCB4B349F018DFBDE15845ADF769BA0D010C952F1A41C90F209"
        "trailing",
        false,
        "comma",
        2,
        "D3CBFDF594A6255F1610B1329AD372CA2C0EF5F9743D60236871ABE22E1EFB27"
        "trailing",
        false,
        "ignored",
        2,
        "43D6E30E73C379FCC9FEA8319BB16206550E769E02A389CB0C1FAA59A351F8DC"
        "trailing",
        false,
        "plain",
        2,
        "689236455161EED4A630F72C733A7A60C7F0F4271BA6B8C80CA5CB1ADAD9ABE9"
        "trailing",
        false,
        "plain",
        4,
        "CFA5162CE3E99D48CA0F9DD722AB4F28DD734CC084ABF41BE0B411C5A9A3EE44"
        "trailing",
        false,
        "plain",
        6,
        "ED78F3531B4E1153AB4961D74A0E10C275F359C5D11D1ED722FD65C671713025"
        "trailing",
        false,
        "raw block",
        2,
        "42B2FAA19806A558F3CD3AB2FE22BDACB747AF5783622E89CBC0A991BEA9BEDB"
        "trailing",
        true,
        "arrow block",
        2,
        "9AE3B9223EBAB6E4C2490B8C24CF234B9120224BF38307694BEEC060CAEFA146"
        "trailing",
        true,
        "arrow line",
        2,
        "C17A8B349837C707EF583AC18712AC93DD17E1CC83776D9DA925C440EAF3EF4B"
        "trailing",
        true,
        "comma",
        2,
        "656A18B81234013AF0E3192C87CC20E553C3D185BECC11A4BBB02DD99934B4D6"
        "trailing",
        true,
        "ignored",
        2,
        "BD1969CE2F162A73583C7F3B085210E9273A2B7E05E3576EA4E2193D1D9C1C65"
        "trailing",
        true,
        "plain",
        2,
        "FCB52732A74C7F3F3A28128ECDA352539D9A6D3F4DFF123523CE59E7F0E87742"
        "trailing",
        true,
        "plain",
        4,
        "75FCF60DE92FE2094927D90EA7393A2A959C34A2BAD24508048CC8E6941789F9"
        "trailing",
        true,
        "plain",
        6,
        "6ACA2F83FA9AEF3048F03492DA6B1BC25EF4A74DAB302F801B8C5A1AC5F0C1B6"
        "trailing",
        true,
        "raw block",
        2,
        "434E6FC7E1A35B3877829BD310AEA5233C061B762F5F2B7DB4CF6997016BF4A9"
    ]

let private fixtures =
    [
        test "the UTF-16 output length counts every printed UTF-16 unit" {
            let literal = "@\"\u4E16\U0001F600\u2028\""
            let source = "class C { string S = " + literal + "; }"
            use d = new DocumentBuffer()
            use printer = new Printer()

            group d (fun () ->
                text d source "class C"
                d.AddLine(LineKind.Normal)
                text d source literal
                d.AddToken(StaticToken.Semicolon))
            |> ignore

            printer.Print(source, d, PrinterOptions.Default)
            let printed = outputText printer

            Expect.stringContains
                printed
                literal
                "The fixture prints the wide, astral and line-separator characters."

            Expect.equal
                printer.OutputUtf16Length
                printed.Length
                "The UTF-16 output length counts the printed text's UTF-16 units."
        }
        test "printer elements occupy 16 reference-free bytes" {
            Expect.equal (Unsafe.SizeOf<FormatElement>()) 16 "The flat IR fits in sixteen bytes."

            Expect.isFalse
                (RuntimeHelpers.IsReferenceOrContainsReferences<FormatElement>())
                "The GC cannot scan elements."

            Expect.equal (Unsafe.SizeOf<ElementKind>()) 1 "Element kinds are bytes."
        }
        test "a trimmed blank run lays out the same however long it is" {
            let blanks = 320
            let source = String(' ', blanks) + String('x', 60) + " tail"

            let printRun run =
                print
                    source
                    { PrinterOptions.Default with
                        Width = 100
                    }
                    (fun (d: DocumentBuffer) ->
                        group d (fun () ->
                            d.AddText(source, blanks - run, run)
                            d.AddTrim()
                            d.AddText(source, blanks, 60)
                            d.AddLine(LineKind.Normal)
                            d.AddText(source, blanks + 61, 4))
                        |> ignore)

            let reference = printRun 5

            for run in [ 254; 255; 256; 301; 320 ] do
                Expect.equal
                    (printRun run)
                    reference
                    "A trimmed blank run cannot change what follows it."
        }
        test "source slices and static tokens concatenate inline" {
            expect "name" 100 "public name;\n" (fun d ->
                d.AddToken(StaticToken.Public)
                d.AddToken(StaticToken.Space)
                d.AddText("name", 0, 4)
                d.AddToken(StaticToken.Semicolon))
        }
        test "a trim after a skipped break refunds only what that line spent" {
            let source = "/*p*/aaabbb"

            let build (d: DocumentBuffer) =
                group d (fun () ->
                    d.AddLine(LineKind.Normal)
                    d.AddComment(source, 0, 5, true, false)
                    d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                    d.AddTrim()
                    d.AddText(source, 5, 3)
                    d.AddLine(LineKind.Normal)
                    d.AddText(source, 8, 3))
                |> ignore

                d.AddLine(LineKind.Hard)

            for width = 5 to 8 do
                let actual =
                    print
                        source
                        { PrinterOptions.Default with
                            Width = width
                        }
                        build

                for line in actual.Split('\n') do
                    if line.Length > width then
                        failtestf
                            "At width %d a %d-column line was printed: %s"
                            width
                            line.Length
                            line
        }
        test "a trim inside an indent refunds the indentation it removed" {
            let source = "/*p*/aaabbb"

            let build (d: DocumentBuffer) =
                scope d Tag.StartIndent Tag.EndIndent (fun () ->
                    group d (fun () ->
                        d.AddLine(LineKind.Normal)
                        d.AddComment(source, 0, 5, true, false)
                        d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                        d.AddTrim()
                        d.AddText(source, 5, 3)
                        d.AddLine(LineKind.Normal)
                        d.AddText(source, 8, 3))
                    |> ignore

                    d.AddLine(LineKind.Hard))

            for width = 9 to 12 do
                let actual =
                    print
                        source
                        { PrinterOptions.Default with
                            Width = width
                        }
                        build

                Expect.stringContains actual "aaa bbb" $"At width {width} the flat line still fits."
        }
        test "a trimmed skippable line leaves a comment guarding its line" {
            expect "a //c b" 100 "\na\n//c\nb\n" (fun d ->
                group d (fun () ->
                    d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                    d.AddTrim()
                    d.AddText("a //c b", 0, 1)
                    d.AddComment("a //c b", 2, 3, true, false)
                    d.AddLine(LineKind.Normal)
                    d.AddText("a //c b", 6, 1))
                |> ignore)
        }
        test "a comment after a single-line comment takes a line of its own" {
            let source = "a// first/* second */// third"

            expect source 100 "a // first\n/* second */ // third\n" (fun d ->
                text d source "a"
                d.AddComment(source, 1, 8, false, false)
                d.AddComment(source, 9, 12, false, true)
                d.AddComment(source, 21, 8, false, false))
        }
        test "code after a single-line comment takes a line of its own" {
            let source = "a// first/* second */b"

            expect source 100 "a // first\n/* second */b\n" (fun d ->
                scope d Tag.StartForceFlat Tag.EndForceFlat (fun () ->
                    text d source "a"
                    d.AddComment(source, 1, 8, false, false)
                    d.AddComment(source, 9, 12, false, true)
                    d.AddText(source, 21, 1)))
        }
        test "ungrouped lines break" {
            expect "13" 100 "1\n3\n" (fun d ->
                text d "13" "1"
                d.AddLine(LineKind.Normal)
                text d "13" "3")
        }
        test "normal and soft lines flatten in groups" {
            expect "123" 100 "1 23\n" (fun d ->
                group d (fun () ->
                    text d "123" "1"
                    d.AddLine(LineKind.Normal)
                    text d "123" "2"
                    d.AddLine(LineKind.Soft)
                    text d "123" "3")
                |> ignore)
        }
        test "soft lines break when the group does not fit" {
            expect "123" 2 "1\n2\n3\n" (fun d ->
                group d (fun () ->
                    text d "123" "1"
                    d.AddLine(LineKind.Soft)
                    text d "123" "2"
                    d.AddLine(LineKind.Normal)
                    text d "123" "3")
                |> ignore)
        }
        test "fit at document end uses the oracle's strict boundary" {
            for width, expected in [ 3, "1\n3\n"; 4, "1 3\n" ] do
                expect "13" width expected (fun d ->
                    group d (fun () ->
                        text d "13" "1"
                        d.AddLine(LineKind.Normal)
                        text d "13" "3")
                    |> ignore)
        }
        test "exact width fits when followed by a hard line" {
            expect "13" 3 "1 3\n" (fun d ->
                group d (fun () ->
                    text d "13" "1"
                    d.AddLine(LineKind.Normal)
                    text d "13" "3")
                |> ignore

                d.AddLine(LineKind.Hard))
        }
        test "hard lines propagate through nested groups" {
            expect "123" 100 "1\n2\n3\n" (fun d ->
                group d (fun () ->
                    text d "123" "1"
                    d.AddLine(LineKind.Normal)

                    group d (fun () ->
                        text d "123" "2"
                        d.AddLine(LineKind.Hard))
                    |> ignore

                    text d "123" "3")
                |> ignore)
        }
        test "break parent propagates through indentation" {
            expect "0123" 100 "0\n    1\n    2\n    3\n" (fun d ->
                text d "0123" "0"

                group d (fun () ->
                    scope d Tag.StartIndent Tag.EndIndent (fun () ->
                        d.AddLine(LineKind.Soft)
                        text d "0123" "1"
                        d.AddLine(LineKind.Normal)
                        text d "0123" "2"
                        d.AddLine(LineKind.Normal)
                        text d "0123" "3"
                        d.AddBreakParent()))
                |> ignore)
        }
        test "forced groups and no-expand groups" {
            expect "12" 100 "1\n2\n" (fun d ->
                d.StartGroup(ElementFlags.Break) |> ignore
                text d "12" "1"
                d.AddLine(LineKind.Normal)
                text d "12" "2"
                d.EndGroup())

            expect "12" 1 "1 2\n" (fun d ->
                d.StartGroup(ElementFlags.NoExpand) |> ignore
                text d "12" "1"
                d.AddLine(LineKind.Hard)
                text d "12" "2"
                d.EndGroup())
        }
        test "force-flat prevents hard and normal breaks" {
            expect "123" 1 "1 2 3\n" (fun d ->
                scope d Tag.StartForceFlat Tag.EndForceFlat (fun () ->
                    text d "123" "1"
                    d.AddLine(LineKind.Hard)
                    text d "123" "2"
                    d.AddLine(LineKind.Normal)
                    text d "123" "3"))
        }
        test "force-flat preserves literal lines and their break propagation" {
            expect "123" 100 "1\n2\n3\n" (fun d ->
                group d (fun () ->
                    scope d Tag.StartForceFlat Tag.EndForceFlat (fun () ->
                        text d "123" "1"
                        d.AddLine(LineKind.Literal)
                        text d "123" "2")

                    d.AddLine(LineKind.Normal)
                    text d "123" "3")
                |> ignore)
        }
        test "literal lines preserve whitespace and omit indentation" {
            expect "(123)" 100 "(\n    1 \n2\n    3)\n" (fun d ->
                text d "(123)" "("

                scope d Tag.StartIndent Tag.EndIndent (fun () ->
                    d.AddLine(LineKind.Hard)
                    text d "(123)" "1"
                    d.AddToken(StaticToken.Space)
                    d.AddLine(LineKind.Literal)
                    text d "(123)" "2"
                    d.AddLine(LineKind.Hard)
                    text d "(123)" "3")

                text d "(123)" ")")
        }
        test "initial literal lines are omitted" {
            expect "1" 100 "1\n" (fun d ->
                d.AddLine(LineKind.Literal)
                text d "1" "1")
        }
        test "a layout CR cannot consume a copied LF" {
            let source = "a\nb"

            for eol, ending in [ EndOfLine.Lf, "\n"; EndOfLine.CrLf, "\r\n"; EndOfLine.Cr, "\r" ] do
                let actual =
                    print
                        source
                        { PrinterOptions.Default with
                            EndOfLine = eol
                        }
                        (fun d ->
                            d.AddText(source, 0, 1)
                            d.AddLine LineKind.Hard
                            d.AddText(source, 1, 2))

                let layoutEnding = if eol = EndOfLine.Cr then "\r\n" else ending

                Expect.equal
                    actual
                    ("a" + layoutEnding + "\nb" + ending)
                    "Completing the layout break leaves the copied LF unchanged."

                Expect.equal
                    (actual.Replace("\r\n", "\n").Replace("\r", "\n"))
                    "a\n\nb\n"
                    "The layout and source each contribute a physical line break."

                let split = "a\r\nb"

                let actual =
                    print
                        split
                        { PrinterOptions.Default with
                            EndOfLine = eol
                        }
                        (fun d ->
                            d.AddText(split, 0, 2)
                            d.AddText(split, 2, 2))

                Expect.equal
                    actual
                    (split + ending)
                    "A CRLF split between source slices stays one break."
        }
        test "hard-line no-trim preserves trailing whitespace" {
            expect "12" 100 "1 \n2\n" (fun d ->
                text d "12" "1"
                d.AddToken(StaticToken.Space)
                d.AddLine(LineKind.Hard, ElementFlags.NoTrim)
                text d "12" "2")
        }
        test "squash lines detect a newline through indentation" {
            expect "12" 100 "1\n    2\n" (fun d ->
                scope d Tag.StartIndent Tag.EndIndent (fun () ->
                    text d "12" "1"
                    d.AddLine(LineKind.Hard)
                    d.AddLine(LineKind.Hard, ElementFlags.Squash)
                    text d "12" "2"))

            for spaces = 1 to 24 do
                let src = String(' ', spaces) + "x"

                expect src 100 "\nx\n" (fun d ->
                    d.AddText(src, 0, spaces)
                    d.AddLine(LineKind.Hard, ElementFlags.Squash)
                    d.AddText(src, spaces, 1))
        }
        test "skip-break first line leaves the inner group flat" {
            expect "12" 100 "\n1 2\n" (fun d ->
                group d (fun () ->
                    d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                    text d "12" "1"
                    d.AddLine(LineKind.Normal)
                    text d "12" "2")
                |> ignore)
        }
        test "skip-break first line still breaks its enclosing group" {
            expect "123" 100 "1\n2\n3\n" (fun d ->
                group d (fun () ->
                    text d "123" "1"
                    d.AddLine(LineKind.Normal)
                    text d "123" "2"

                    group d (fun () ->
                        d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                        text d "123" "3")
                    |> ignore)
                |> ignore)
        }
        test "skip-break first line marks a conditional parent without breaking its inner group" {
            expect "123" 100 "\n1 2 3\n" (fun d ->
                conditional
                    d
                    [
                        (fun () ->
                            text d "123" "1"
                            d.AddLine(LineKind.Normal)
                            text d "123" "2"
                            d.AddLine(LineKind.Normal)
                            text d "123" "3")
                        (fun () ->
                            group d (fun () ->
                                d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                                text d "123" "1"
                                d.AddLine(LineKind.Normal)
                                text d "123" "2"
                                d.AddLine(LineKind.Normal)
                                text d "123" "3")
                            |> ignore)
                    ])
        }
        test "a broken conditional cannot be measured as part of a flat alternative" {
            let source = "alpha beta gamma delta"

            let inner (d: DocumentBuffer) =
                conditional
                    d
                    [
                        (fun () -> text d source "alpha beta")
                        (fun () ->
                            group d (fun () ->
                                d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                                text d source "alpha"
                                d.AddLine(LineKind.Normal)
                                text d source "beta")
                            |> ignore)
                    ]

            let fallback (d: DocumentBuffer) words =
                words
                |> List.iteri (fun index word ->
                    if index > 0 then
                        d.AddLine(LineKind.Hard)

                    text d source word)

            expect source 8 "alpha\nbeta\n" (fun d ->
                conditional d [ (fun () -> inner d); (fun () -> fallback d [ "alpha"; "beta" ]) ])

            expect source 8 "alpha\nbeta\ngamma\ndelta\n" (fun d ->
                conditional
                    d
                    [
                        (fun () ->
                            inner d
                            d.AddLine(LineKind.Normal)
                            text d source "gamma"
                            d.AddLine(LineKind.Normal)
                            text d source "delta")
                        (fun () -> fallback d [ "alpha"; "beta"; "gamma"; "delta" ])
                    ])
        }
        test "first-line skip still measures the following text" {
            expect "someValue" 10 "\nsomeValue\nsomeValue\n" (fun d ->
                group d (fun () ->
                    d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                    text d "someValue" "someValue"
                    d.AddLine(LineKind.Normal)
                    text d "someValue" "someValue")
                |> ignore)
        }
        test "directive text does not consume fit width or first-line status" {
            expect "#pragma12" 5 "#pragma\n1 2\n" (fun d ->
                group d (fun () ->
                    d.AddText("#pragma12", 0, 7, ElementFlags.Directive)
                    d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                    text d "#pragma12" "1"
                    d.AddLine(LineKind.Normal)
                    text d "#pragma12" "2")
                |> ignore)
        }
        test "trim refunds fit whitespace" {
            expect "test    " 10 "test test\n" (fun d ->
                group d (fun () ->
                    text d "test    " "test    "
                    d.AddTrim()
                    d.AddLine(LineKind.Normal)
                    text d "test    " "test")
                |> ignore)
        }
        test "trim removes indentation before directives" {
            expect "{1#if}" 100 "{\n    1\n#if\n}\n" (fun d ->
                text d "{1#if}" "{"

                scope d Tag.StartIndent Tag.EndIndent (fun () ->
                    d.AddLine(LineKind.Hard)
                    text d "{1#if}" "1"
                    d.AddLine(LineKind.Hard)
                    d.AddTrim()
                    text d "{1#if}" "#if")

                d.AddLine(LineKind.Hard)
                text d "{1#if}" "}")
        }
        test "fit includes the real continuation outside the group" {
            expect "abcde123456" 10 "ab\ncd123456\n" (fun d ->
                text d "abcde123456" "ab"

                group d (fun () ->
                    d.AddLine(LineKind.Normal)
                    text d "abcde123456" "cd")
                |> ignore

                text d "abcde123456" "123456")
        }
        test "fit stops at the next line before unrelated long text" {
            expect "12longlonglong" 10 "1 2\nlonglonglong\n" (fun d ->
                text d "12longlonglong" "1"

                group d (fun () ->
                    d.AddLine(LineKind.Normal)
                    text d "12longlonglong" "2")
                |> ignore

                d.AddLine(LineKind.Hard)
                text d "12longlonglong" "longlonglong")
        }
        test "hard line in flattened alternative forces subsequent group remeasurement" {
            expect "123456" 4 "1\n2\n3456\n" (fun d ->
                group d (fun () ->
                    conditional
                        d
                        [
                            (fun () ->
                                text d "123456" "1"
                                d.AddLine(LineKind.Hard)
                                text d "123456" "2")
                        ]

                    group d (fun () ->
                        d.AddLine(LineKind.Normal)
                        text d "123456" "3456")
                    |> ignore)
                |> ignore)
        }
        test "if-break selects flat or broken contents" {
            for width, expected in [ 100, "another flat\n"; 10, "another\nbreak\n" ] do
                expect "anotherbreakflat" width expected (fun d ->
                    group d (fun () ->
                        text d "anotherbreakflat" "another"
                        d.AddLine(LineKind.Normal)

                        ifBreak d -1 (fun () -> text d "anotherbreakflat" "break") (fun () ->
                            text d "anotherbreakflat" "flat"))
                    |> ignore)
        }
        test "if-break can target a finished group by integer ID" {
            for forced, expected in [ false, "1flat\n"; true, "1\nbreak\n" ] do
                expect "1breakflat" 100 expected (fun d ->
                    let id =
                        group d (fun () ->
                            text d "1breakflat" "1"

                            if forced then
                                d.AddLine(LineKind.Hard))

                    ifBreak d id (fun () -> text d "1breakflat" "break") (fun () ->
                        text d "1breakflat" "flat"))
        }
        test "if-break inside candidate group sees its speculative mode" {
            expect "1breakflat" 100 "1flat\n" (fun d ->
                let id = d.StartGroup()
                text d "1breakflat" "1"

                ifBreak d id (fun () -> text d "1breakflat" "break") (fun () ->
                    text d "1breakflat" "flat")

                d.EndGroup())
        }
        test "if-break before its target is rejected even after speculative fitting" {
            use d = new DocumentBuffer()
            use printer = new Printer()
            let id = d.NewGroupId()

            group d (fun () -> ifBreak d id (fun () -> text d "bf" "b") (fun () -> text d "bf" "f"))
            |> ignore

            d.AddTag(Tag.StartGroup, id)
            text d "bf" "f"
            d.EndGroup()

            Expect.throws
                (fun () -> printer.Print("bf", d, PrinterOptions.Default))
                "Fitting cannot publish future group modes."
        }
        test "both if-break branches participate in break propagation" {
            for hardInFlat in [ true; false ] do
                expect "1breakflat" 100 "1\nbreak\n" (fun d ->
                    group d (fun () ->
                        text d "1breakflat" "1"
                        d.AddLine(LineKind.Normal)

                        ifBreak
                            d
                            -1
                            (fun () ->
                                text d "1breakflat" "break"

                                if not hardInFlat then
                                    d.AddLine(LineKind.Hard))
                            (fun () ->
                                text d "1breakflat" "flat"

                                if hardInFlat then
                                    d.AddLine(LineKind.Hard)))
                    |> ignore)
        }
        test "conditional groups choose a fitting alternative" {
            expect "tooLong" 10 "tooLong\ntooLong\n" (fun d ->
                conditional
                    d
                    [
                        (fun () ->
                            text d "tooLong" "tooLong"
                            d.AddToken(StaticToken.Space)
                            text d "tooLong" "tooLong")
                        (fun () ->
                            text d "tooLong" "tooLong"
                            d.AddLine(LineKind.Hard)
                            text d "tooLong" "tooLong")
                    ])
        }
        test "single conditional fallback retains its flat candidate even when too wide" {
            expect "12" 1 "1 2\n" (fun d ->
                conditional
                    d
                    [
                        (fun () ->
                            text d "12" "1"
                            d.AddLine(LineKind.Normal)
                            text d "12" "2")
                    ])
        }
        test "conditional alternatives do not propagate breaks to the parent" {
            expect "123" 100 "1 2\n" (fun d ->
                group d (fun () ->
                    conditional
                        d
                        [
                            (fun () ->
                                text d "123" "1"
                                d.AddLine(LineKind.Normal)
                                text d "123" "2")
                            (fun () ->
                                text d "123" "1"
                                d.AddLine(LineKind.Hard)
                                text d "123" "3")
                        ])
                |> ignore)
        }
        test "conditional parent isolates an ordinary hard line in a same-token alternative" {
            expect "12" 100 "1 2\n" (fun d ->
                conditional
                    d
                    [
                        (fun () ->
                            text d "12" "1"
                            d.AddLine(LineKind.Normal)
                            text d "12" "2")
                        (fun () ->
                            group d (fun () ->
                                text d "12" "1"
                                d.AddLine(LineKind.Hard)
                                text d "12" "2")
                            |> ignore)
                    ])
        }
        test "conditional group fallback retains breaks inside nested groups" {
            expect "ThisContentIsTooLong123" 10 "1\n2\n3\n" (fun d ->
                conditional
                    d
                    [
                        (fun () -> text d "ThisContentIsTooLong123" "ThisContentIsTooLong")
                        (fun () ->
                            group d (fun () ->
                                text d "ThisContentIsTooLong123" "1"
                                d.AddLine(LineKind.Normal)
                                text d "ThisContentIsTooLong123" "2"
                                d.AddLine(LineKind.Hard)
                                text d "ThisContentIsTooLong123" "3")
                            |> ignore)
                    ])
        }
        test "forced conditional group selects its final alternative" {
            expect "123" 100 "3\n" (fun d ->
                let id = d.NewGroupId()
                d.AddTag(Tag.StartConditionalGroup, id, ElementFlags.Break)
                scope d Tag.StartAlternative Tag.EndAlternative (fun () -> text d "123" "1")
                scope d Tag.StartAlternative Tag.EndAlternative (fun () -> text d "123" "3")
                d.AddTag(Tag.EndConditionalGroup))
        }
        test "always-fits content is printed but excluded from measurement" {
            expect "12verylong" 4 "1 2verylong\n" (fun d ->
                group d (fun () ->
                    text d "12verylong" "1"
                    d.AddLine(LineKind.Normal)
                    text d "12verylong" "2"

                    scope d Tag.StartAlwaysFits Tag.EndAlwaysFits (fun () ->
                        text d "12verylong" "verylong"))
                |> ignore)
        }
        test "always-fits hides its contents from break propagation" {
            expect "12" 100 "1\n 2\n" (fun d ->
                group d (fun () ->
                    text d "12" "1"
                    d.AddLine(LineKind.Normal)

                    scope d Tag.StartAlwaysFits Tag.EndAlwaysFits (fun () ->
                        d.AddLine(LineKind.Hard))

                    d.AddLine(LineKind.Normal)
                    text d "12" "2")
                |> ignore)
        }
        test "trailing comments suppress a following space and force a newline" {
            for line in [ false; true ] do
                expect "xy// comment" 100 "x // comment\ny\n" (fun d ->
                    group d (fun () ->
                        text d "xy// comment" "x"
                        d.AddComment("xy// comment", 2, 10, false, false)

                        if line then
                            d.AddLine(LineKind.Normal)
                        else
                            d.AddToken(StaticToken.Space)

                        text d "xy// comment" "y")
                    |> ignore)
        }
        test "leading comments preserve first-line skip status" {
            let source = "// commenttrue|| false"

            expect source 100 "// comment\n// comment\ntrue || false\n" (fun d ->
                group d (fun () ->
                    for _ = 1 to 2 do
                        d.AddComment(source, 0, 10, true, false)
                        d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)

                    text d source "true"
                    d.AddLine(LineKind.Normal)
                    text d source "|| false")
                |> ignore)
        }
        test "a force-flat trailing comment keeps the column it leaves" {
            let source = "aa/*xxxxxxxx*/bb cc"

            for width, expected in [ 25, "aa /*xxxxxxxx*/bb cc\n"; 18, "aa /*xxxxxxxx*/bb\ncc\n" ] do
                expect source width expected (fun d ->
                    scope d Tag.StartForceFlat Tag.EndForceFlat (fun () ->
                        text d source "aa"
                        d.AddComment(source, 2, 12, false, true))

                    group d (fun () ->
                        text d source "bb"
                        d.AddLine(LineKind.Normal)
                        text d source "cc")
                    |> ignore)
        }
        test "a force-flat trailing comment ends on the line it printed last" {
            let source = "aa/*cc\nxx*/bb dd"

            for width, expected in [ 10, "aa /*cc\nxx*/bb dd\n"; 8, "aa /*cc\nxx*/bb\ndd\n" ] do
                expect source width expected (fun d ->
                    scope d Tag.StartForceFlat Tag.EndForceFlat (fun () ->
                        text d source "aa"
                        d.AddComment(source, 2, 9, false, true))

                    group d (fun () ->
                        text d source "bb"
                        d.AddLine(LineKind.Normal)
                        text d source "dd")
                    |> ignore)
        }
        test "trimming an indentation away leaves the column at zero" {
            let source = "ab c"

            for width, expected in [ 5, "\nab c\n"; 4, "\nab\n\tc\n" ] do
                let options =
                    { PrinterOptions.Default with
                        Width = width
                        UseTabs = true
                    }

                let actual =
                    print source options (fun d ->
                        scope d Tag.StartIndent Tag.EndIndent (fun () ->
                            d.AddLine(LineKind.Hard)
                            d.AddTrim()

                            group d (fun () ->
                                text d source "ab"
                                d.AddLine(LineKind.Normal)
                                text d source "c")
                            |> ignore))

                Expect.equal actual expected "Clearing the indentation returns its whole column."
        }
        test "text on a leading comment's line continues from its end" {
            let source = "/*xxxxxxxx*/bb cc"

            for width, expected in [ 20, "/*xxxxxxxx*/bb cc\n"; 16, "/*xxxxxxxx*/bb\ncc\n" ] do
                expect source width expected (fun d ->
                    d.AddComment(source, 0, 12, true, true)

                    group d (fun () ->
                        text d source "bb"
                        d.AddLine(LineKind.Normal)
                        text d source "cc")
                    |> ignore)
        }
        test "a multiline leading comment leaves the cursor on its last line" {
            let source = "/* a\n   */bb cc"

            for width, expected in [ 12, "/* a\n   */bb cc\n"; 9, "/* a\n   */bb\ncc\n" ] do
                expect source width expected (fun d ->
                    d.AddComment(source, 0, 10, true, true)

                    group d (fun () ->
                        text d source "bb"
                        d.AddLine(LineKind.Normal)
                        text d source "cc")
                    |> ignore)
        }
        test "multiline leading comments adjust all lines by the first indentation delta" {
            let source = "  /* a\r\n   * b\r\n   */"

            expect source 100 "    /* a\n     * b\n     */\n" (fun d ->
                scope d Tag.StartIndent Tag.EndIndent (fun () ->
                    d.AddComment(source, 0, source.Length, true, true)))
        }
        test "regions reuse their starting indentation" {
            let source = "#region R#endregion"

            expect source 100 "    #region R\n    #endregion\n" (fun d ->
                scope d Tag.StartIndent Tag.EndIndent (fun () -> d.AddRegion(source, 0, 9, false))
                d.AddLine(LineKind.Hard)
                d.AddRegion(source, 9, 10, true))
        }
        test "wide UTF-16 characters match CSharpier widths" {
            for source, expected in
                [
                    "", 0u
                    "someValue", 9u
                    "가", 2u
                    "가가가", 6u
                    "var x = \"가가\";", 15u
                    "😀", 2u
                    "e\u0301", 2u
                ] do
                use d = new DocumentBuffer()
                d.AddText(source, 0, source.Length)
                Expect.equal d.Elements[0].Width expected "Display width is computed at build time."

            expect "가가" 5 "가\n가\n" (fun d ->
                group d (fun () ->
                    text d "가가" "가"
                    d.AddLine(LineKind.Normal)
                    text d "가가" "가")
                |> ignore)
        }
        test "multiline source is copied without string materialization" {
            let source = "\"\"\"\r\nraw text\r\n\"\"\""
            use d = new DocumentBuffer()
            d.AddText(source, 0, source.Length)

            Expect.isTrue
                (d.Elements[0].Flags &&& ElementFlags.Multiline <> 0uy)
                "Multiline text is flagged."

            use printer = new Printer()
            printer.Print(source, d, PrinterOptions.Default)

            Expect.equal
                (outputText printer)
                (source + "\n")
                "Literal source remains byte for byte."
        }
        test "multiline text is as wide as the line it ends on" {
            let source = "\"\"\"\naaaaaaaaaa\n\"\"\""
            use d = new DocumentBuffer()
            d.AddText(source, 0, source.Length)
            d.AddGeneratedText(source.AsSpan())

            for i in [ 0; 1 ] do
                Expect.equal
                    d.Elements[i].Width
                    3u
                    "The breaks it prints reset the column, so earlier lines are not on it."
        }
        test "text after multiline text shares the line that text ended on" {
            let literal = "\"\"\"\naaaaaaaaaa\n\"\"\""
            let source = literal + ", first second"

            expect source 20 (source + "\n") (fun d ->
                text d source literal

                group d (fun () ->
                    text d source ", first"
                    d.AddLine(LineKind.Normal)
                    text d source "second")
                |> ignore)
        }
        test "a group holding multiline text measures the lines it prints" {
            let literal = "\"\"\"\naaaaaaaaaa\n\"\"\""

            for tail, expected in
                [
                    ", tail", "head" + literal + ", tail x\n"
                    ", taaaaaaaaaaaaaaail", "head" + literal + ", taaaaaaaaaaaaaaail\nx\n"
                ] do
                let source = "head" + literal + tail + " x"

                expect source 20 expected (fun d ->
                    group d (fun () ->
                        text d source "head"
                        text d source literal
                        text d source tail
                        d.AddLine(LineKind.Normal)
                        text d source "x")
                    |> ignore)
        }
        test "tabs have the configured indentation width" {
            let options =
                { PrinterOptions.Default with
                    UseTabs = true
                    Width = 8
                }

            let actual =
                print "0123" options (fun d ->
                    text d "0123" "0"

                    scope d Tag.StartIndent Tag.EndIndent (fun () ->
                        d.AddLine(LineKind.Hard)

                        group d (fun () ->
                            text d "0123" "1"
                            d.AddLine(LineKind.Normal)
                            text d "0123" "23")
                        |> ignore))

            Expect.equal actual "0\n\t1\n\t23\n" "Tabs consume IndentSize columns in fit."
        }
        test "single final newline and optional initial-line trimming" {
            for eol, suffix in [ EndOfLine.Lf, "\n"; EndOfLine.CrLf, "\r\n" ] do
                for source in [ "1"; "1\n"; "1\r\n\r\n"; "" ] do
                    let actual =
                        print
                            source
                            { PrinterOptions.Default with
                                EndOfLine = eol
                            }
                            (fun d -> d.AddText(source, 0, source.Length))

                    Expect.equal
                        actual
                        (if source.Length = 0 then "" else "1" + suffix)
                        "Exactly one final newline for nonempty output; empty output stays empty."

            let actual =
                print
                    "1"
                    { PrinterOptions.Default with
                        TrimInitialLines = true
                    }
                    (fun d ->
                        d.AddLine(LineKind.Hard)
                        text d "1" "1")

            Expect.equal actual "1\n" "Initial blank lines are trimmed on request."
        }
        test "unbalanced documents are rejected" {
            for start, finish in [ Tag.StartGroup, Tag.EndIndent; Tag.StartIndent, Tag.EndGroup ] do
                use d = new DocumentBuffer()
                use printer = new Printer()

                if start = Tag.StartGroup then
                    d.StartGroup() |> ignore
                else
                    d.AddTag(start)

                d.AddTag(finish)

                Expect.throws
                    (fun () -> printer.Print("", d, PrinterOptions.Default))
                    "Do not silently print mismatched scopes."

            use unclosed = new DocumentBuffer()
            use printer = new Printer()
            unclosed.StartGroup() |> ignore

            Expect.throws
                (fun () -> printer.Print("", unclosed, PrinterOptions.Default))
                "An opening tag needs a closing tag."
        }
        test "deep documents use iterative propagation and fitting" {
            let source = "a"
            use d = new DocumentBuffer(16)
            use printer = new Printer()

            for _ = 1 to 4096 do
                d.StartGroup() |> ignore

            text d source "a"

            for _ = 1 to 4096 do
                d.EndGroup()

            printer.Print(source, d, PrinterOptions.Default)
            Expect.equal (outputText printer) "a\n" "No recursive tree walk."
            let before = d.Elements.ToArray()

            printer.Print(
                source,
                d,
                { PrinterOptions.Default with
                    Width = 1
                }
            )

            Expect.equal
                (d.Elements.ToArray())
                before
                "Fitting and propagation leave the document unchanged."
        }
        test "reset and print reuse retained buffers without stale modes" {
            use d = new DocumentBuffer(16)
            use printer = new Printer()
            d.StartGroup() |> ignore
            text d "12" "1"
            d.AddLine(LineKind.Hard)
            text d "12" "2"
            d.EndGroup()
            printer.Print("12", d, PrinterOptions.Default)
            Expect.equal (outputText printer) "1\n2\n" "Initial group breaks."
            d.Reset()
            Expect.equal (d.StartGroup()) 0 "Group IDs reset with the document."
            text d "12" "1"
            d.AddLine(LineKind.Normal)
            text d "12" "2"
            d.EndGroup()
            printer.Print("12", d, PrinterOptions.Default)
            Expect.equal (outputText printer) "1 2\n" "No prior break state survives."
        }
        test "generated pass characters survive growth and reset" {
            use d = new DocumentBuffer(16)
            use printer = new Printer()
            let first = String.replicate 300 "a"
            let second = String.replicate 1000 "b"
            d.AddGeneratedText(first.AsSpan())
            d.AddGeneratedText(second.AsSpan())
            printer.Print("unrelated source", d, PrinterOptions.Default)

            Expect.equal
                (outputText printer)
                (first + second + "\n")
                "Growing the generated arena preserves every existing slice."

            d.Reset()
            d.AddGeneratedText("next pass".AsSpan())
            printer.Print("", d, PrinterOptions.Default)
            Expect.equal (outputText printer) "next pass\n" "Reset discards prior passes."
        }
        test "disposed pooled buffers reject access" {
            let d = new DocumentBuffer()
            let printer = new Printer()
            d.Dispose()

            Expect.throws
                (fun () -> d.AddLine(LineKind.Hard))
                "Returned IR storage cannot be written."

            Expect.throws
                (fun () -> d.AddGeneratedText("pass".AsSpan()))
                "Returned character storage cannot be written."

            Expect.throws
                (fun () -> printer.Print("", d, PrinterOptions.Default))
                "Returned IR storage cannot be read."

            printer.Dispose()
            use live = new DocumentBuffer()

            Expect.throws
                (fun () -> printer.Print("", live, PrinterOptions.Default))
                "Returned output storage cannot be written."
        }
        test "a one-off syntax build without directives allocates no conditional-pass storage" {
            let source = "class C { }\n"
            let tree = SyntaxTree()
            Parser.parse source tree
            use document = new DocumentBuffer()

            let build () =
                document.Reset()
                SyntaxPrinter.build source tree document PrinterOptions.Default

            build ()
            let before = GC.GetAllocatedBytesForCurrentThread()
            build ()
            let allocated = GC.GetAllocatedBytesForCurrentThread() - before

            Expect.isLessThan
                allocated
                65536L
                "A file without directives needs only the node printer."
        }
        for constructor in [ false; true ] do
            test (
                "trailing lambda argument build allocation scales linearly / "
                + (if constructor then "constructor" else "invocation")
            ) {
                let measure count =
                    let parameters = [ for i in 0 .. count - 1 -> $"int p{i}" ] |> String.concat ","

                    let arguments = Array.create count "0" |> String.concat ","

                    let source =
                        if constructor then
                            $"class C{{C({parameters},System.Func<int> f){{}} void M(){{var c=new C({arguments},()=>0);}}}}"
                        else
                            $"class C{{static void F({parameters},System.Func<int> f){{}} void M(){{F({arguments},()=>0);}}}}"

                    let tree = SyntaxTree()
                    Parser.parse source tree
                    use document = new DocumentBuffer()
                    use syntax = new SyntaxDocumentBuilder()

                    let build () =
                        document.Reset()
                        syntax.Build(source, tree, document, PrinterOptions.Default)

                    for _ = 1 to 32 do
                        build ()

                    Array.init 5 (fun _ ->
                        let before = GC.GetAllocatedBytesForCurrentThread()

                        for _ = 1 to 8 do
                            build ()

                        GC.GetAllocatedBytesForCurrentThread() - before)

                let smallSamples = measure 128
                let largeSamples = measure 1024
                let small = Array.min smallSamples
                let large = Array.min largeSamples

                printfn
                    "trailing lambda build allocation, bytes per 8 builds: 128=%A; 1024=%A"
                    smallSamples
                    largeSamples

                Expect.isLessThanOrEqual
                    large
                    (12L * small)
                    $"Preparing separators once keeps an eightfold list within linear growth. Best of five 8-build batches: 128=%A{smallSamples}; 1024=%A{largeSamples}."
            }
        for constructor in [ false; true ] do
            for family in [ "simple"; "empty"; "trailing" ] do
                test (
                    $"nested lambda construction stays linear / {family} / constructor={constructor}"
                ) {
                    let tree = SyntaxTree()
                    use document = new DocumentBuffer()
                    use syntax = new SyntaxDocumentBuilder()
                    use printer = new Printer()
                    let allocations = ResizeArray<int64>()

                    for depth in [ 2; 4; 6; 8; 10; 12; 16 ] do
                        let source = nestedLambdaSource family constructor "plain" depth
                        Parser.parse source tree

                        let build () =
                            document.Reset()
                            syntax.Build(source, tree, document, PrinterOptions.Default)

                        for _ = 1 to 32 do
                            build ()

                        let samples =
                            Array.init 5 (fun _ ->
                                let before = GC.GetAllocatedBytesForCurrentThread()

                                for _ = 1 to 8 do
                                    build ()

                                (GC.GetAllocatedBytesForCurrentThread() - before) / 8L)

                        let bytes = Array.min samples
                        allocations.Add bytes

                        printfn
                            "nested %s constructor=%b d=%d visits=%d elements=%d bytes=%d"
                            family
                            constructor
                            depth
                            syntax.LambdaBodyVisits
                            document.Count
                            bytes

                        Expect.equal syntax.LambdaBodyVisits depth "Emit each body once."

                        Expect.isLessThanOrEqual
                            document.Count
                            (80 * depth + 64)
                            "Alternatives retain ranges rather than expanded copies."

                        for options in nestedLambdaOptions do
                            printer.Print(source, document, options)

                            Expect.isLessThanOrEqual
                                printer.SharedPreparationWork
                                (4 * depth * document.Count)
                                "Cached boundary summaries keep preparation at most quadratic."

                            let formatted = outputText printer
                            Parser.parse formatted tree
                            document.Reset()
                            syntax.Build(formatted, tree, document, options)
                            printer.Print(formatted, document, options)

                            Expect.equal
                                (outputText printer)
                                formatted
                                "Nested layouts are idempotent."

                            Parser.parse source tree
                            build ()

                    Expect.isLessThanOrEqual
                        allocations[allocations.Count - 1]
                        (10L * allocations[0])
                        "Eight times the nesting has linear warmed allocation."
                }
        test "nested call arguments stay linear" {
            let tree = SyntaxTree()
            use document = new DocumentBuffer()
            use syntax = new SyntaxDocumentBuilder()
            use printer = new Printer()
            let checker = TokenPreservation.Checker()

            for depth in [ 2; 4; 8; 16; 32 ] do
                let mutable expression = "0"

                for level = depth downto 1 do
                    expression <- $"Hash.Combine(this.CheckOverflowProperty{level}, {expression})"

                let source = $"class C {{ int M() {{ return {expression}; }} }}"
                Parser.parse source tree
                document.Reset()
                syntax.Build(source, tree, document, PrinterOptions.Default)
                printfn "nested calls d=%d elements=%d" depth document.Count

                Expect.isLessThanOrEqual
                    document.Count
                    (40 * depth + 64)
                    "Alternatives replay each chain part rather than copying it."

                printer.Print(source, document, PrinterOptions.Default)
                let formatted = outputText printer

                Expect.equal
                    (checker.Check(PrinterOptions.Default, "nested.cs", source, formatted))
                    (Ok())
                    "Every token survives."

                Parser.parse formatted tree
                document.Reset()
                syntax.Build(formatted, tree, document, PrinterOptions.Default)
                printer.Print(formatted, document, PrinterOptions.Default)
                Expect.equal (outputText printer) formatted "Nested calls are idempotent."
        }
        test "deep nesting indents at every level" {
            let levels = 300
            let source = nestedIfSource levels "int x = 1;"

            let format (input: string) =
                let tree = SyntaxTree()
                Parser.parse input tree
                use doc = new DocumentBuffer()
                use syntax = new SyntaxDocumentBuilder()
                use printer = new Printer()
                syntax.Build(input, tree, doc, PrinterOptions.Default)
                printer.Print(input, doc, PrinterOptions.Default)
                outputText printer

            let mutable formatted = ""
            let mutable again = ""

            onStack Worker.StackSize (fun () ->
                formatted <- format source
                again <- format formatted)

            let openingIndents =
                [
                    for line in formatted.Split '\n' do
                        if line.Trim() = "{" then
                            line.Length - line.TrimStart().Length
                ]

            Expect.equal
                openingIndents
                [ for level in 0 .. levels + 1 -> 4 * level ]
                "Every block opens one indent level inside the block above it."

            Expect.equal again formatted "Deep nesting is idempotent."

            let checker = TokenPreservation.Checker()

            Expect.equal
                (checker.Check(PrinterOptions.Default, "deep.cs", source, formatted))
                (Ok())
                "Every token survives."
        }
        test "the stack guard reads a deeper frame as a lower address" {
            let rec descend depth =
                let here = StackGuard.entry ()

                if depth = 0 then [ here ] else here :: descend (depth - 1)

            let frames = descend 32

            for i = 1 to frames.Length - 1 do
                Expect.isTrue
                    (frames[i] < frames[i - 1])
                    $"Frame {i} must lie below frame {i - 1} for the floor to mean depth."

            Expect.equal
                (StackGuard.proven StackGuard.Unproven > 0n)
                true
                "A probe that succeeds returns this frame as the new floor."
        }
        test "preprocessor expression selection fails safely on a small stack" {
            let depth = 20_000

            for condition in
                [ String('!', depth) + "A"; String('(', depth) + "A" + String(')', depth) ] do
                let source = "#if " + condition + "\nclass C {}\n#endif\n"
                let tree = SyntaxTree()
                onStack Worker.StackSize (fun () -> Parser.parse source tree)

                Expect.throwsT<InsufficientExecutionStackException>
                    (fun () ->
                        onStack (1024 * 1024) (fun () ->
                            Preprocessor.symbolSets source tree |> ignore))
                    "Witness selection must fail one file instead of overflowing the process stack."
        }
        test "nesting past the stack fails rather than printing raw" {
            let chain = String.Join(" + ", Array.init 15000 string)

            for levels, statement in [ 6000, "int x = 1;"; 120, $"int x = {chain};" ] do
                let source = nestedIfSource levels statement
                let tree = SyntaxTree()
                onStack Worker.StackSize (fun () -> Parser.parse source tree)
                let mutable thrown: exn = null

                onStack (1024 * 1024) (fun () ->
                    try
                        use doc = new DocumentBuffer()
                        use syntax = new SyntaxDocumentBuilder()
                        syntax.Build(source, tree, doc, PrinterOptions.Default)
                    with error ->
                        thrown <- error)

                Expect.equal
                    (if isNull thrown then
                         "no exception"
                     else
                         thrown.GetType().Name)
                    "InsufficientExecutionStackException"
                    "Nesting the stack cannot hold is an error, not silently raw output."
        }
        test "shared alternatives preserve boundary breaks and relocated group targets" {
            for scoped in [ false; true ] do
                for line in
                    [ LineKind.Normal; LineKind.Hard; LineKind.Literal; LineKind.IndentedLiteral ] do
                    for flags in [ 0uy; ElementFlags.SkipBreakIfFirst ] do
                        for wrapper in [ Tag.StartIndent; Tag.StartForceFlat; Tag.StartAlwaysFits ] do
                            let build shared (d: DocumentBuffer) =
                                let emit () =
                                    if scoped then
                                        let id =
                                            group d (fun () ->
                                                d.AddLine(line, flags)
                                                text d "ab" "a")

                                        ifBreak d id (fun () -> text d "ab" "b") (fun () ->
                                            text d "ab" "a")
                                    else
                                        d.AddLine(line, flags)
                                        text d "ab" "a"

                                group d (fun () ->
                                    let mutable start = 0
                                    let mutable length = 0

                                    ifBreak
                                        d
                                        -1
                                        (fun () ->
                                            start <- d.Count
                                            emit ()
                                            length <- d.Count - start)
                                        (fun () ->
                                            if shared then d.AddShared(start, length) else emit ())

                                    text d "ab" "b")
                                |> ignore

                            use original = new DocumentBuffer()
                            use shared = new DocumentBuffer()
                            use copied = new DocumentBuffer()
                            use printer = new Printer()
                            build false original
                            build true shared

                            let finish =
                                match wrapper with
                                | Tag.StartForceFlat -> Tag.EndForceFlat
                                | Tag.StartAlwaysFits -> Tag.EndAlwaysFits
                                | _ -> Tag.EndIndent

                            group copied (fun () -> copied.AddToken StaticToken.Space) |> ignore

                            scope copied wrapper finish (fun () ->
                                copied.Append(shared, 0, shared.Count))

                            for options in nestedLambdaOptions do
                                let expected =
                                    print "ab" options (fun d ->
                                        group d (fun () -> d.AddToken StaticToken.Space) |> ignore

                                        scope d wrapper finish (fun () ->
                                            d.Append(original, 0, original.Count)))

                                printer.Print("ab", copied, options)

                                Expect.equal
                                    (outputText printer)
                                    expected
                                    "Shared preparation matches expanded scopes."

                            printer.Print("ab", copied, PrinterOptions.Default)

                            let bytes =
                                allocatedWhilePrinting "ab" copied printer PrinterOptions.Default 8

                            Expect.equal
                                bytes
                                0L
                                "Warmed shared preparation and replay allocate nothing."
        }
        test "nested lambda alternatives retain exact baseline bytes" {
            let tree = SyntaxTree()
            use document = new DocumentBuffer()
            use syntax = new SyntaxDocumentBuilder()
            use printer = new Printer()

            for family, constructor, variant, depth, expected in
                nestedLambdaOutput @ deepLambdaOutput do
                let source = nestedLambdaSource family constructor variant depth
                Parser.parse source tree
                document.Reset()
                syntax.Build(source, tree, document, PrinterOptions.Default)

                use digest =
                    System.Security.Cryptography.IncrementalHash.CreateHash(
                        System.Security.Cryptography.HashAlgorithmName.SHA256
                    )

                for options in nestedLambdaOptions do
                    printer.Print(source, document, options)
                    let bytes = System.Text.Encoding.UTF8.GetBytes(outputText printer)
                    digest.AppendData(System.Security.Cryptography.SHA256.HashData bytes)

                Expect.equal
                    (Convert.ToHexString(digest.GetHashAndReset()))
                    expected
                    ($"Unchanged sixteen-configuration bytes: {family}/{constructor}/{variant}/{depth}")
        }

        test "trailing lambda head trivia work stays linear" {
            let tree = SyntaxTree()
            use document = new DocumentBuffer()
            use syntax = new SyntaxDocumentBuilder()

            let samples =
                [
                    for comments in [ false; true ] do
                        for padding in [ 0; 4096 ] do
                            for count in [ 64; 128; 256; 512 ] do
                                let unrelated =
                                    String.replicate
                                        padding
                                        (if comments then "/* outside */\n" else " \n")

                                let calls = String.replicate count "        F(0, () => 0);\n"

                                let source =
                                    "class C {\n    static int F(int n, System.Func<int> f) => f();\n    void M() {\n"
                                    + calls
                                    + "    }\n"
                                    + unrelated
                                    + "}\n"

                                Parser.parse source tree
                                document.Reset()
                                syntax.Build(source, tree, document, PrinterOptions.Default)
                                let struct (records, queries, comparisons) = syntax.HeadTriviaWork

                                printfn
                                    "head trivia: q=%d padding=%d comments=%b T=%d records=%d queries=%d comparisons=%d"
                                    count
                                    padding
                                    comments
                                    tree.TriviaCount
                                    records
                                    queries
                                    comparisons

                                yield
                                    tree.TriviaCount,
                                    count,
                                    records,
                                    queries,
                                    comparisons,
                                    comments && padding > 0
                ]

            for trivia, count, records, queries, comparisons, hasComments in samples do
                Expect.equal records trivia "Inspect trivia once per pass, including whitespace."
                Expect.equal queries count "One range query per eligible trailing lambda."

                let bound = if hasComments then count * 13 else 0
                Expect.isLessThanOrEqual comparisons bound "Query work is logarithmic in comments."

            let source = "class C { }"
            Parser.parse source tree
            document.Reset()
            syntax.Build(source, tree, document, PrinterOptions.Default)
            Expect.equal syntax.HeadTriviaWork (struct (0, 0, 0)) "No query needs no index."
        }
        for scope in [ "compilation unit"; "block namespace"; "file-scoped namespace" ] do
            test ($"namespace child classification stays linear / {scope}") {
                let tree = SyntaxTree()
                use document = new DocumentBuffer()
                use syntax = new SyntaxNodePrinter("", tree)

                for count in [ 128; 256; 512; 1024 ] do
                    let usings =
                        [
                            for i = 0 to count - 1 do
                                $"using A{i:D4} = System.Int32;\n"
                        ]
                        |> String.concat ""

                    let contents = usings + "class C { }\n"

                    let source, children =
                        match scope with
                        | "block namespace" -> "namespace N {\n" + contents + "}\n", count + 3
                        | "file-scoped namespace" -> "namespace N;\n" + contents, count + 3
                        | _ -> contents, count + 1

                    Parser.parse source tree
                    document.Reset()
                    syntax.Reset(source, tree)
                    syntax.Build(document)

                    printfn
                        "namespace classification: %s U=%d probes=%d sort comparisons=%d"
                        scope
                        count
                        syntax.NamespaceClassificationProbes
                        syntax.UsingSortComparisons

                    Expect.isLessThanOrEqual
                        syntax.NamespaceClassificationProbes
                        (8L * int64 children)
                        "Classification work is linear independently of using sorting."

                    Expect.isGreaterThan
                        syntax.UsingSortComparisons
                        0L
                        "The deliberate using sort is exercised and counted separately."
            }
        test "namespace using trivia work stays linear" {
            let tree = SyntaxTree()
            use document = new DocumentBuffer()
            use syntax = new SyntaxNodePrinter("", tree)

            for conditional in [ false; true ] do
                for padding in [ 0; 4096 ] do
                    for count in [ 64; 128; 256; 512 ] do
                        let namespaces =
                            String.concat
                                ""
                                [
                                    for i = 1 to count do
                                        $"namespace N{i} {{ using Zebra; using System; using Alpha; }}\n"
                                ]

                        let source =
                            String.replicate padding "/* unrelated */\n"
                            + (if conditional then "#if true\n#if true\n" else "")
                            + namespaces
                            + (if conditional then "#endif\n#endif\n" else "")

                        Parser.parse source tree
                        document.Reset()
                        syntax.Reset(source, tree)
                        syntax.Build(document)

                        printfn
                            "using trivia: namespaces=%d padding=%d conditional=%b T=%d probes=%d"
                            count
                            padding
                            conditional
                            tree.TriviaCount
                            syntax.UsingTriviaProbes

                        Expect.isLessThanOrEqual
                            syntax.UsingTriviaProbes
                            (2L * int64 tree.TriviaCount)
                            "Inspect trivia once for the index and once within using runs."
        }
        test "namespace using depth cache resets with the tree" {
            let tree = SyntaxTree()
            use document = new DocumentBuffer()
            use syntax = new SyntaxNodePrinter("", tree)
            use printer = new Printer()
            let namespaces = "namespace N{using Zebra;using System;}\n"
            let sorted = "namespace N\n{\n    using System;\n    using Zebra;\n}\n"

            for source, expected in
                [
                    "#if true\n" + namespaces + "#endif\n", "#if true\n" + sorted + "#endif\n"
                    namespaces, sorted
                    "#if true\nextern alias X;\n#endif\n" + namespaces,
                    "#if true\nextern alias X;\n#endif\n" + sorted
                    "#if true\n" + namespaces + "#endif\n", "#if true\n" + sorted + "#endif\n"
                ] do
                Parser.parse source tree
                document.Reset()
                syntax.Reset(source, tree)
                syntax.Build(document)
                printer.Print(source, document, PrinterOptions.Default)
                Expect.equal (outputText printer) expected "Depths belong to the current parse."
        }
        test "trailing lambda head ranges preserve source positions and boundaries" {
            let source =
                "/* before */ F(0, (/* head */) => /* body */ 0); // after\n"
                + "#region outside\n#endregion\n"
                + "var s = $\"{F(0, (/* hole head */) => 0)}\"; // outer\n"
                + "F(0, (\n/// documentation\n) => 0);\n"

            let tree = SyntaxTree()
            Parser.parse source tree

            Expect.isTrue
                ([ 1 .. tree.TriviaCount - 1 ]
                 |> List.exists (fun i -> (tree.Trivia i).Start < (tree.Trivia(i - 1)).Start))
                "Interpolation trivia really is appended out of source order."

            use syntax = new SyntaxNodePrinter(source, tree)

            let reference first finish =
                [ 0 .. tree.TriviaCount - 1 ]
                |> List.exists (fun i ->
                    let item = tree.Trivia i

                    item.Start >= first
                    && item.Start < finish
                    && (SyntaxFacts.comment item.Kind || SyntaxFacts.directive item.Kind))

            for first = 0 to source.Length do
                for finish in [ first; min source.Length (first + 1); source.Length ] do
                    Expect.equal
                        (syntax.HeadHasTrivia(first, finish))
                        (reference first finish)
                        $"Comment/directive starts in [{first}, {finish})."

            let nextSource = "F(0, () => 0);"
            Parser.parse nextSource tree
            syntax.Reset(nextSource, tree)
            Expect.isFalse (syntax.HeadHasTrivia(0, nextSource.Length)) "Reset removes old ranges."
        }
        for family in
            [
                "class"
                "abstract class"
                "enum"
                "enum with final comma"
                "ignored enum ranges"
            ] do
            for count in [ 128; 256; 512; 1024 ] do
                test ($"member metadata probes stay linear / {family} / {count}") {
                    let source =
                        match family with
                        | "class" ->
                            "class C{"
                            + String.concat "" [ for i in 1..count -> $"void M{i}(){{}}" ]
                            + "}"
                        | "abstract class" ->
                            "abstract class C{"
                            + String.concat "" [ for i in 1..count -> $"abstract void M{i}();" ]
                            + "}"
                        | "ignored enum ranges" ->
                            "enum E{\n"
                            + String.concat
                                ""
                                [
                                    for i in 1..count ->
                                        $"// csff-ignore-start\nM{i} = {i},\n// csff-ignore-end\nN{i} = {i},\n"
                                ]
                            + "}"
                        | _ ->
                            "enum E{"
                            + String.concat "," [ for i in 1..count -> $"V{i}" ]
                            + (if family = "enum" then "}" else ",}")

                    let tree = SyntaxTree()
                    Parser.parse source tree
                    use document = new DocumentBuffer()
                    use syntax = new SyntaxNodePrinter(source, tree)
                    syntax.Build(document)

                    printfn
                        "member metadata probes: %s / %d = %d"
                        family
                        count
                        syntax.MemberMetadataProbes

                    if family = "ignored enum ranges" then
                        use printer = new Printer()
                        printer.Print(source, document, PrinterOptions.Default)

                        Expect.stringContains
                            (outputText printer)
                            "\nM1 = 1,"
                            "Every generated range is actually ignored."

                    let allowance =
                        if family = "ignored enum ranges" then
                            6L * int64 count + 8L
                        else
                            2L * int64 count + 8L

                    Expect.isLessThanOrEqual
                        syntax.MemberMetadataProbes
                        allowance
                        "Parent modifier and enum separator searches grow linearly."
                }
        test "representative printing allocates zero steady-state bytes" {
            let source = "alpha beta gamma delta epsilon zeta"
            use d = new DocumentBuffer()
            use printer = new Printer()

            group d (fun () ->
                for i = 0 to 63 do
                    if i > 0 then
                        d.AddLine(LineKind.Normal)

                    group d (fun () ->
                        text d source "alpha"
                        d.AddLine(LineKind.Normal)

                        scope d Tag.StartIndent Tag.EndIndent (fun () ->
                            group d (fun () ->
                                text d source "beta"
                                d.AddLine(LineKind.Normal)
                                text d source "gamma")
                            |> ignore)

                        d.AddLine(LineKind.Normal)

                        conditional
                            d
                            [
                                (fun () ->
                                    text d source "delta"
                                    d.AddToken(StaticToken.Space)
                                    text d source "epsilon")
                                (fun () ->
                                    text d source "delta"
                                    d.AddLine(LineKind.Hard)
                                    text d source "epsilon")
                            ])
                    |> ignore)
            |> ignore

            let options =
                { PrinterOptions.Default with
                    Width = 24
                }

            for _ = 1 to 1000 do
                printer.Print(source, d, options)

            let bytes = allocatedWhilePrinting source d printer options 1000
            Expect.equal bytes 0L "No allocations in pooled output, propagation, commands, or fits."

            printfn
                "allocation: %d elements; %d output chars; %d bytes / 1000 prints = %.1f bytes/print"
                d.Count
                printer.OutputUtf16Length
                bytes
                (float bytes / 1000.0)
        }
    ]

let private fixtureTokens (source: string) =
    let buffer = Csff.Lexer.TokenBuffer()
    Csff.Lexer.Lexer.lex source buffer
    buffer

let private tokenTexts (source: string) =
    let buffer = fixtureTokens source

    Array.init (buffer.TokenCount - 1) (fun index ->
        let token = buffer.Token index
        source.Substring(token.Start, token.Length))

let private wordDocument (source: string) indent =
    let d = new DocumentBuffer()
    let tokens = fixtureTokens source
    let count = tokens.TokenCount - 1

    for _ = 1 to indent do
        d.AddTag(Tag.StartIndent)

    d.StartGroup() |> ignore

    for index = 0 to count - 1 do
        if index > 0 then
            d.AddLine(LineKind.Normal)

        if index % 2 = 0 then
            d.StartGroup() |> ignore

        let token = tokens.Token index
        d.AddText(source, token.Start, token.Length)

        if index % 2 = 1 then
            d.EndGroup()

    if count % 2 = 1 then
        d.EndGroup()

    d.EndGroup()

    for _ = 1 to indent do
        d.AddTag(Tag.EndIndent)

    d

let private propertyInput (samples: uint16 list) (widthSeed: byte) (indentSeed: byte) =
    let samples =
        if List.isEmpty samples then
            [ 1us ]
        else
            List.truncate 40 samples

    let words =
        samples
        |> List.mapi (fun i n ->
            let value = String((if i % 3 = 0 then '가' else 'x'), 1 + int n % 120)

            if i % 4 = 0 then
                "\"" + value + " " + value + "\""
            else
                value)

    String.Join(" \t\n", words), 20 + int widthSeed % 81, int indentSeed % 4

let private properties =
    [
        testProperty
            "printer idempotency after rebuilding from printed source"
            (fun (samples: uint16 list) (widthSeed: byte) (indentSeed: byte) ->
                let source, width, indent = propertyInput samples widthSeed indentSeed

                let options =
                    { PrinterOptions.Default with
                        Width = width
                    }

                use first = wordDocument source indent
                use printer = new Printer()
                printer.Print(source, first, options)
                let printed = outputText printer
                use second = wordDocument printed indent
                printer.Print(printed, second, options)

                Expect.equal
                    (outputText printer)
                    printed
                    "Rebuilding source slices must preserve layout.")
        testProperty
            "printer width permits only individually overlong tokens"
            (fun (samples: uint16 list) (widthSeed: byte) (indentSeed: byte) ->
                let source, width, indent = propertyInput samples widthSeed indentSeed
                use d = wordDocument source indent
                use printer = new Printer()

                printer.Print(
                    source,
                    d,
                    { PrinterOptions.Default with
                        Width = width
                    }
                )

                let printed = outputText printer

                for line in printed.Split('\n') do
                    let widthOfLine = PrintedWidth.measure (line.AsSpan()) |> int

                    if widthOfLine > width then
                        let tokens = tokenTexts line

                        Expect.equal
                            tokens.Length
                            1
                            "Overflow cannot be caused by a collection of smaller tokens."

                        let leading = line.Length - line.TrimStart(' ').Length

                        Expect.isGreaterThan
                            (int (PrintedWidth.measure (tokens[0].AsSpan())))
                            (width - leading)
                            "One indivisible token exceeds the available space."

                let originalWords = tokenTexts source

                let printedWords = tokenTexts printed

                Expect.equal
                    printedWords
                    originalWords
                    "The invariant may not discard or split tokens.")
    ]

let private printSyntax source options =
    let tree = SyntaxTree()
    Parser.parse source tree
    use document = new DocumentBuffer()
    use printer = new Printer()
    SyntaxPrinter.build source tree document options
    printer.Print(source, document, options)
    outputText printer

let private printSequentialSyntax source options =
    let tree = SyntaxTree()
    Parser.parse source tree
    use document = new DocumentBuffer()
    use printer = new Printer()
    use builder = new SyntaxDocumentBuilder()
    builder.BatchIndependentRegions <- false
    builder.Build(source, tree, document, options)
    printer.Print(source, document, options)
    outputText printer

let private commentIndentFixtures =
    [
        test "every documentation line takes the enclosing indentation" {
            let printed = printSyntax "class C{\n/// a\n/// b\nint x;}\n" PrinterOptions.Default

            Expect.equal
                printed
                "class C\n{\n    /// a\n    /// b\n    int x;\n}\n"
                "Both documentation lines are indented."
        }
        test "a multiline comment keeps its relative indent under tabs" {
            let options =
                { PrinterOptions.Default with
                    UseTabs = true
                }

            let printed =
                printSyntax "class C\n{\n    void M()\n    {\n/* a\n * b\n */\n    }\n}\n" options

            Expect.stringContains printed "\t\t/* a\n" "The comment opens at its indent."
            Expect.stringContains printed "\t\t * b\n" "A continuation keeps its extra column."
            Expect.stringContains printed "\t\t */\n" "So does the closing line."
        }
        test "a trim refunds every whitespace element before it" {
            let build (d: DocumentBuffer) =
                group d (fun () ->
                    d.AddText("ab", 0, 1)
                    d.AddToken StaticToken.Space
                    d.AddToken StaticToken.Space
                    d.AddTrim()
                    d.AddLine(LineKind.Normal)
                    d.AddText("ab", 1, 1))
                |> ignore

            let printed =
                print
                    "ab"
                    { PrinterOptions.Default with
                        Width = 4
                    }
                    build

            Expect.equal printed "a b\n" "The flat layout fits once both spaces are refunded."
        }
    ]

let private commentScaling =
    [
        test "many leading comments on one line locate that line once" {
            let scans count =
                let comments = String.concat "" [ for i in 1..count -> $"/*c{i}*/" ]

                let text =
                    "class C\n{\n    void M()\n    {\n        " + comments + "x();\n    }\n}\n"

                let tree = SyntaxTree()
                Parser.parse text tree
                use document = new DocumentBuffer()
                use printer = new Printer()
                SyntaxPrinter.build text tree document PrinterOptions.Default
                printer.Print(text, document, PrinterOptions.Default)
                printer.SourceLineScans

            let few = scans 10
            let many = scans 2000
            printfn "leading comments: 10 comments = %d scans, 2000 = %d scans" few many

            Expect.equal many few "Comments sharing a source line must locate it once between them."

            Expect.isLessThan few 8 "Locating one line is a constant number of scans."
        }
    ]

let private commentLineGuards =
    [
        test "consecutive leading comments take a line each" {
            let options =
                { PrinterOptions.Default with
                    Width = 20
                }

            let printed = printSyntax "/*1234567890*//*1234567890*/\nclass C { }\n" options

            for line in printed.Split('\n') do
                if line.Length > 20 then
                    failtestf "A %d-column line was printed at width 20: %s" line.Length line

            Expect.stringContains
                printed
                "/*1234567890*/\n/*1234567890*/\n"
                "Each comment takes its own line."
        }
        test "a run of blank lines costs about linearly" {
            let source count =
                "class C\n{\n    const string S = @\""
                + String.replicate count "\n"
                + "\";\n}\n"

            let milliseconds count =
                let text = source count
                let tree = SyntaxTree()
                Parser.parse text tree
                use document = new DocumentBuffer()
                use printer = new Printer()
                SyntaxPrinter.build text tree document PrinterOptions.Default

                for _ = 1 to 2 do
                    printer.Print(text, document, PrinterOptions.Default)

                let attempt () =
                    let start = System.Diagnostics.Stopwatch.GetTimestamp()
                    let mutable iteration = 0

                    while iteration < 3 do
                        printer.Print(text, document, PrinterOptions.Default)
                        iteration <- iteration + 1

                    System.Diagnostics.Stopwatch.GetElapsedTime(start).TotalMilliseconds / 3.0

                List.min [ for _ in 1..3 -> attempt () ]

            let tiny = milliseconds 1000
            let small = milliseconds 8000
            let large = milliseconds 32000
            let ratio = large / max tiny 0.001

            printfn
                "blank lines: 1000 = %.3f, 8000 = %.3f, 32000 = %.3f ms, 32x ratio %.2f"
                tiny
                small
                large
                ratio

            Expect.isLessThan ratio 48.0 "A new line must not re-examine every earlier one."
        }
    ]

let private optionGuards =
    [
        test "printing rejects options it cannot honour, and says which" {
            let build (d: DocumentBuffer) = d.AddText("a", 0, 1)

            let reject fragment options =
                let mutable message = null

                try
                    print "a" options build |> ignore
                with :? ArgumentException as error ->
                    message <- error.Message

                Expect.isNotNull message $"Options with {fragment} raise an ArgumentException."
                Expect.stringContains message fragment "The message names the field at fault."

            reject
                "Width must be greater than zero"
                { PrinterOptions.Default with
                    Width = 0
                }

            reject
                "Width must be greater than zero"
                { PrinterOptions.Default with
                    Width = -1
                }

            reject
                "IndentSize must be greater than zero"
                { PrinterOptions.Default with
                    IndentSize = 0
                }

            reject
                "IndentSize must be greater than zero"
                { PrinterOptions.Default with
                    IndentSize = 0
                    UseTabs = true
                }

            reject
                "EndOfLine must be Lf, CrLf or Cr"
                { PrinterOptions.Default with
                    EndOfLine = enum<EndOfLine> 99
                }
        }
    ]

let private lineCommentGuards =
    [
        test "code never follows a line comment onto its line" {
            let source = "//cF();"

            let build (d: DocumentBuffer) =
                group d (fun () ->
                    d.AddLine(LineKind.Normal)
                    d.AddComment(source, 0, 3, true, false)
                    d.AddLine(LineKind.Normal)
                    d.AddText(source, 3, 4))
                |> ignore

            let printed = print source PrinterOptions.Default build

            Expect.equal printed "\n//c\nF();\n" "The call keeps its own line."
        }
    ]

let private blockExteriorTriviaFixtures =
    [
        for name, body, comments in
            [
                "trailing block comment", "{} /* tail */", [ "/* tail */" ]
                "trailing line comment", "{} // tail\n", [ "// tail" ]
                "leading block comment", "\n/* lead */{}", [ "/* lead */" ]
                "leading line comment", "\n// lead\n{}", [ "// lead" ]
                "exterior and interior comments",
                "\n/* lead */{ /* inside */ Work(); } /* tail */",
                [ "/* lead */"; "/* inside */"; "/* tail */" ]
            ] do
            test ($"block exterior trivia: {name}") {
                let checker = TokenPreservation.Checker()

                for head in [ "x =>"; "() =>"; "delegate"; "delegate()" ] do
                    let expression = head + body

                    for source in
                        [
                            $"Call(first, Wrap({expression}), last).Next();After();"
                            "/* outer lead */var s = $\"{Call("
                            + expression
                            + ")}\"; // outer tail\nAfter();"
                        ] do
                        let exterior =
                            if source.Contains("/* outer lead */", StringComparison.Ordinal) then
                                [ "/* outer lead */"; "// outer tail" ]
                            else
                                []

                        for _, configuration in OutputConfigurations.all do
                            for endOfLine in [ EndOfLine.Lf; EndOfLine.CrLf ] do
                                let options =
                                    { configuration with
                                        EndOfLine = endOfLine
                                    }

                                let newline = if endOfLine = EndOfLine.CrLf then "\r\n" else "\n"
                                let source = source.Replace("\n", newline)
                                let actual = printSyntax source options

                                for comment in comments @ exterior do
                                    Expect.equal
                                        (actual.Split([| comment |], StringSplitOptions.None).Length
                                         - 1)
                                        1
                                        $"Comment survives exactly once / {head} / {options}"

                                match checker.Check(options, $"{name}.cs", source, actual) with
                                | Ok() -> ()
                                | Error error -> failtest error

                                Expect.equal
                                    (printSyntax actual options)
                                    actual
                                    $"Block exterior trivia is idempotent / {head} / {options}"
            }
    ]

let private trailingLambdaFixtures =
    [
        for name, width, source, expected in
            [
                "named and ref/out",
                100,
                "Call(first:1,ref value,out var result,callback:()=>0);",
                "Call(first: 1, ref value, out var result, callback: () => 0);\n"
                "wrap",
                60,
                "Call(first:1,ref value,out var result,callback:()=>CalculateSomethingVeryLong());",
                "Call(first: 1, ref value, out var result, callback: () =>\n    CalculateSomethingVeryLong()\n);\n"
                "chop",
                25,
                "Call(first:1,ref value,out var result,callback:()=>CalculateSomethingVeryLong());",
                "Call(\n    first: 1,\n    ref value,\n    out var result,\n    callback: () =>\n        CalculateSomethingVeryLong()\n);\n"
                "constructor flat",
                100,
                "new C(first:1,ref value,out var result,callback:()=>0);",
                "new C(first: 1, ref value, out var result, callback: () => 0);\n"
                "constructor wrap",
                60,
                "new C(first:1,ref value,out var result,callback:()=>CalculateSomethingVeryLong());",
                "new C(first: 1, ref value, out var result, callback: () =>\n    CalculateSomethingVeryLong()\n);\n"
                "constructor chop",
                25,
                "new C(first:1,ref value,out var result,callback:()=>CalculateSomethingVeryLong());",
                "new C(\n    first: 1,\n    ref value,\n    out var result,\n    callback: () =>\n        CalculateSomethingVeryLong()\n);\n"
                "comma trivia",
                100,
                "Call(first:1/*before*/,/*after*/ref value,out var result,//comma\ncallback:()=>0);",
                "Call(\n    first: 1 /*before*/\n    , /*after*/\n    ref value,\n    out var result, //comma\n    callback: () => 0\n);\n"
                "arrow fallback",
                100,
                "Call(first:1,ref value,out var result,callback:()=>//arrow\n0);",
                "Call(\n    first: 1,\n    ref value,\n    out var result,\n    callback: () => //arrow\n        0\n);\n"
                "simple lambda block",
                60,
                "Call(first:1,ref value,out var result,callback:x=>{return x;});",
                "Call(first: 1, ref value, out var result, callback: x =>\n{\n    return x;\n});\n"
                "nested lists",
                25,
                "Call(Inner(1,2,()=>0),3,()=>0);",
                "Call(\n    Inner(1, 2, () => 0),\n    3,\n    () => 0\n);\n"
                "head block comment",
                100,
                "F(0, (/* head */) => 0);",
                "F(\n    0,\n    ( /* head */\n    ) => 0\n);\n"
                "head line comment",
                100,
                "F(0, (// head\n) => 0);",
                "F(\n    0,\n    ( // head\n    ) => 0\n);\n"
                "head documentation comment",
                100,
                "F(0, (\n/// head\n) => 0);",
                "F(\n    0,\n    (\n    /// head\n    ) => 0\n);\n"
                "outside comments",
                100,
                "/* before */ F(0, () => 0); // after\n",
                "/* before */F(0, () => 0); // after\n"
                "head directive",
                100,
                "F(0, (\n#region head\n#endregion\n) => 0);",
                "F(0, (\n    #region head\n    #endregion\n    ) => 0);\n"
                "interpolation head comment",
                100,
                "var s = $\"{F(0, (/* head */) => 0)}\"; // outside\n",
                "var s = $\"{F(0, ( /* head */) => 0)}\"; // outside\n"
                "interpolation outside comment",
                100,
                "var s = $\"{/* outside */ F(0, () => 0)}\"; // after\n",
                "var s = $\"{ /* outside */F(0, () => 0)}\"; // after\n"
                "interpolation arrow comment",
                100,
                "var s = $\"{F(0, () => // arrow\n0)}\"; // after\n",
                "var s = $\"{F(0, () => // arrow\n0)}\"; // after\n"
            ] do
            test ($"trailing lambda separators preserve output / {name}") {
                let options =
                    { PrinterOptions.Default with
                        Width = width
                    }

                let actual = printSyntax source options
                Expect.equal actual expected "Separator extraction leaves the layout unchanged."

                Expect.equal
                    (printSyntax actual options)
                    actual
                    "Trailing lambda layouts remain idempotent."

                let expectConforms result =
                    match result with
                    | Ok() -> ()
                    | Error message -> failtest message

                TokenPreservation.Checker().Check(options, "trailing-lambda.cs", source, actual)
                |> expectConforms

                for text in [ source; actual ] do
                    RoslynOracle.check "trailing-lambda.cs" text (Csff.Lexer.TokenBuffer())
                    |> expectConforms

                    NodeOracle.check "trailing-lambda.cs" text (SyntaxTree()) |> expectConforms
            }
    ]

let private commentBoundaryFixtures =
    [
        for name, source, expected in
            [
                "lambda arrow",
                "x(x,()=>// p\nx);x;",
                "x(\n    x,\n    () => // p\n        x\n);\nx;\n"
                "argument separator", "x(a,// p\nb);", "x(\n    a, // p\n    b\n);\n"
                "binary operator", "var y = a +// p\nb;", "var y =\n    a\n    + // p\n    b;\n"
                "assignment", "var y =// p\n1;", "var y = // p\n    1;\n"
                "block opening",
                "class C{void M(){// p\nint a=1;}}",
                "class C\n{\n    void M()\n    { // p\n        int a = 1;\n    }\n}\n"
                "member chain", "x.A()// p\n.B();", "x.A() // p\n    .B();\n"
                "condition", "if(a&&// p\nb){}", "if (\n    a\n    && // p\n    b\n) { }\n"
                "conditional operator",
                "var y = a ?// p\nb : c;",
                "var y = a\n    ? // p\n    b\n    : c;\n"
                "initializer separator",
                "var y = new D{A=1,// p\nB=2};",
                "var y = new D\n{\n    A = 1, // p\n    B = 2,\n};\n"
                "lambda block comment", "x(x,()=>/* p */x);x;", "x(x, () => /* p */ x);\nx;\n"
                "simple lambda arrow",
                "x(x,a=>// p\nx);x;",
                "x(\n    x,\n    a => // p\n        x\n);\nx;\n"
                "lambda arrow before block",
                "x(x,()=>// p\n{});x;",
                "x(\n    x,\n    () => // p\n    { }\n);\nx;\n"
                "lambda body leading comment",
                "x(x,()=>\n// p\nx);x;",
                "x(\n    x,\n    () =>\n        // p\n        x\n);\nx;\n"
                "XML documentation first argument",
                "class C\n{\n    void M()\n    {\n        Call(\n            /// note\n            42);\n    }\n    void Call(int x) { }\n}\n",
                "class C\n{\n    void M()\n    {\n        Call(\n            /// note\n            42\n        );\n    }\n\n    void Call(int x) { }\n}\n"
                "XML documentation non-first argument",
                "Call(1,\n    /// note\n    42);\n",
                "Call(\n    1,\n    /// note\n    42\n);\n"
                "XML documentation binary operand",
                "var y = 1 +\n    /// note\n    42;\n",
                "var y =\n    1\n    +\n    /// note\n    42;\n"
            ] do
            test ($"comment boundary: {name}") {
                let checker = TokenPreservation.Checker()

                for width, tabs in
                    [
                        for width in [ 40; 55; 60; 70; 80; 90; 100; 120; 150; 200 ] do
                            yield width, false
                        yield 100, true
                    ] do
                    for endOfLine in [ EndOfLine.Lf; EndOfLine.CrLf ] do
                        let options =
                            { PrinterOptions.Default with
                                Width = width
                                UseTabs = tabs
                                EndOfLine = endOfLine
                            }

                        let newline = if endOfLine = EndOfLine.CrLf then "\r\n" else "\n"
                        let source = source.Replace("\n", newline)

                        let expected =
                            (if tabs then expected.Replace("    ", "\t") else expected)
                                .Replace("\n", newline)

                        let actual = printSyntax source options
                        Expect.equal actual expected $"Comment boundary / {options}"

                        match checker.Check(options, $"{name}.cs", source, actual) with
                        | Ok() -> ()
                        | Error error -> failtest error

                        Expect.equal
                            (printSyntax actual options)
                            actual
                            "Idempotent comment boundary."
            }
    ]

let private expressionFixtures =
    [
        for name, width, source, expected in
            [
                "binary precedence",
                100,
                "alpha+beta*gamma-delta;",
                "alpha + beta * gamma - delta;\n"
                "binary equality asymmetry",
                100,
                "left==right&&one!=two||yes==no;",
                "left == right && one != two || yes == no;\n"
                "coalesce", 100, "alpha??beta??gamma;", "alpha ?? beta ?? gamma;\n"
                "terminal coalesce",
                100,
                "receiver.Method()??fallback;",
                "receiver.Method() ?? fallback;\n"
                "nonterminal coalesce",
                100,
                "receiver.Method().Next()??fallback;",
                "receiver.Method().Next() ?? fallback;\n"
                "conditional",
                100,
                "Call(condition?whenTrue:whenFalse);",
                "Call(condition ? whenTrue : whenFalse);\n"
                "chained conditional",
                100,
                "Call(one?first:two?second:third);",
                "Call(\n    one ? first\n    : two ? second\n    : third\n);\n"
                "nested conditional",
                100,
                "one?(two?first:second):third;",
                "one ? (two ? first : second) : third;\n"
                "simple chain",
                100,
                "service.Foo(alpha,beta).Bar(gamma).Baz();",
                "service.Foo(alpha, beta).Bar(gamma).Baz();\n"
                "merged chain",
                100,
                "this.Foo(alpha,beta).Bar(gamma).Baz();",
                "this.Foo(alpha, beta).Bar(gamma).Baz();\n"
                "conditional chain",
                100,
                "instance?.Foo(alpha)?.Bar(beta)[index]!;",
                "instance?.Foo(alpha)?.Bar(beta)[index]!;\n"
                "property chain",
                100,
                "something?.Alpha.Beta!.Gamma.Delta;",
                "something?.Alpha.Beta!.Gamma.Delta;\n"
                "then include",
                100,
                "query.Include(x=>x.Parent).ThenInclude(x=>x.Child).ThenInclude(x=>x.Name).Where(x=>x.Flag);",
                "query.Include(x => x.Parent).ThenInclude(x => x.Child).ThenInclude(x => x.Name).Where(x => x.Flag);\n"
                "arguments", 100, "Call(one,two,three);", "Call(one, two, three);\n"
                "named arguments",
                100,
                "Call(name:one,ref two,out var three);",
                "Call(name: one, ref two, out var three);\n"
                "simple lambda", 100, "Call(x=>x.Property+1);", "Call(x => x.Property + 1);\n"
                "lambda object",
                100,
                "Call(x=>new Thing{Value=x});",
                "Call(x => new Thing\n{\n    Value = x,\n});\n"
                "lambda anonymous",
                100,
                "Call(x=>new{ x.Property });",
                "Call(x => new\n{\n    x.Property,\n});\n"
                "parenthesized lambda", 100, "Call((x,y)=>x+y);", "Call((x, y) => x + y);\n"
                "empty lambda", 100, "Call(()=>Calculate());", "Call(() => Calculate());\n"
                "trailing lambda",
                100,
                "Call(first,second,x=>x.Property+1);",
                "Call(first, second, x => x.Property + 1);\n"
                "trailing empty lambda",
                100,
                "Call(first,second,()=>Calculate());",
                "Call(first, second, () => Calculate());\n"
                "object one property",
                100,
                "new Thing(){Value=1};",
                "new Thing()\n{\n    Value = 1,\n};\n"
                "implicit object", 100, "new(){Value=1};", "new()\n{\n    Value = 1,\n};\n"
                "empty object", 100, "new Thing{};", "new Thing { };\n"
                "anonymous one property", 100, "new{Value=1};", "new\n{\n    Value = 1,\n};\n"
                "anonymous empty", 100, "new{};", "new { };\n"
                "array", 100, "new int[]{1,2,3};", "new int[] { 1, 2, 3 };\n"
                "implicit array", 100, "new[]{1,2,3};", "new[] { 1, 2, 3 };\n"
                "nested arrays",
                100,
                "new int[][]{new[]{1,2},new[]{3,4}};",
                "new int[][] { new[] { 1, 2 }, new[] { 3, 4 } };\n"
                "complex initializer",
                100,
                "new Dictionary<int,int>{{1,2},{3,4},{5,6}};",
                "new Dictionary<int, int>\n{\n    { 1, 2 },\n    { 3, 4 },\n    { 5, 6 },\n};\n"
                "nested initializer",
                100,
                "new Thing{Property={X=1}};",
                "new Thing\n{\n    Property =\n    {\n        X = 1,\n    },\n};\n"
                "with", 100, "Call(value with{A=1,B=2});", "Call(value with { A = 1, B = 2 });\n"
                "collection", 100, "Call([one,two,three]);", "Call([one, two, three]);\n"
                "nested collection",
                100,
                "Call([[one,two],[three,four]]);",
                "Call([\n    [one, two],\n    [three, four],\n]);\n"
                "spread", 100, "Call([one,..other,two]);", "Call([one, .. other, two]);\n"
                "cast",
                100,
                "(Dictionary<int,string>)value.Method();",
                "(Dictionary<int, string>)value.Method();\n"
                "compact cast", 100, "(int)value;", "(int)value;\n"
                "unary", 100, "-a+~b+ ++c;", "-a + ~b + ++c;\n"
                "range",
                100,
                "Call(values[1..^2],values[..3],values[2..],values[..]);",
                "Call(values[1..^2], values[..3], values[2..], values[..]);\n"
                "tuple",
                100,
                "Call((first:one,second:two),((int X,string Y))tuple);",
                "Call((first: one, second: two), ((int X, string Y))tuple);\n"
                "switch",
                100,
                "value switch{1=>one,2 when flag=>two,_=>other};",
                "value switch\n{\n    1 => one,\n    2 when flag => two,\n    _ => other,\n};\n"
                "patterns",
                100,
                "Call(value is Thing{Property:>0 and <10,Other:not null});",
                "Call(value is Thing { Property: > 0 and < 10, Other: not null });\n"
                "positional patterns",
                100,
                "Call(value is Point(1,2));",
                "Call(value is Point(1, 2));\n"
                "list patterns",
                100,
                "Call(value is [one,..var rest]);",
                "Call(value is [one, .. var rest]);\n"
                "interpolation", 100, "$\"value={a+b,10:X}\";", "$\"value={a + b, 10:X}\";\n"
                "interpolation chain",
                100,
                "$\"{value.Foo().Bar().Baz()}\";",
                "$\"{value.Foo().Bar().Baz()}\";\n"
                "verbatim string", 100, "@\"a\nb\";", "@\"a\nb\";\n"
                "raw string",
                100,
                "\"\"\"\n  one\n  two\n  \"\"\";",
                "\"\"\"\n    one\n    two\n    \"\"\";\n"
                "raw interpolation",
                100,
                "$\"\"\"\n  one {a+b}\n  two\n  \"\"\";",
                "$\"\"\"\n    one {a + b}\n    two\n    \"\"\";\n"
                "await", 100, "await Call(one,two);", "await Call(one, two);\n"
                "checked", 100, "checked(a+b);", "checked(a + b);\n"
                "typeof",
                100,
                "typeof(Dictionary<string,int>);",
                "typeof(Dictionary<string, int>);\n"
                "assignment", 100, "a=b=c=d;", "a = b = c = d;\n"
                "initializer comment",
                100,
                "new Thing{Value=1 // value\n};",
                "new Thing\n{\n    Value = 1, // value\n};\n"
                "arguments comment",
                100,
                "Call(one, // one\ntwo);",
                "Call(\n    one, // one\n    two\n);\n"
                "property pattern comment",
                100,
                "Call(value is { // test\nProperty:1});",
                "Call(\n    value\n        is { // test\n            Property: 1\n        }\n);\n"
                "binary precedence",
                35,
                "alpha+beta*gamma-delta;",
                "alpha + beta * gamma - delta;\n"
                "binary equality asymmetry",
                35,
                "left==right&&one!=two||yes==no;",
                "left == right && one != two\n    || yes == no;\n"
                "coalesce", 35, "alpha??beta??gamma;", "alpha ?? beta ?? gamma;\n"
                "terminal coalesce",
                35,
                "receiver.Method()??fallback;",
                "receiver.Method() ?? fallback;\n"
                "nonterminal coalesce",
                35,
                "receiver.Method().Next()??fallback;",
                "receiver.Method().Next()\n    ?? fallback;\n"
                "conditional",
                35,
                "Call(condition?whenTrue:whenFalse);",
                "Call(\n    condition\n        ? whenTrue\n        : whenFalse\n);\n"
                "chained conditional",
                35,
                "Call(one?first:two?second:third);",
                "Call(\n    one ? first\n    : two ? second\n    : third\n);\n"
                "nested conditional",
                35,
                "one?(two?first:second):third;",
                "one\n    ? (two ? first : second)\n    : third;\n"
                "simple chain",
                35,
                "service.Foo(alpha,beta).Bar(gamma).Baz();",
                "service\n    .Foo(alpha, beta)\n    .Bar(gamma)\n    .Baz();\n"
                "merged chain",
                35,
                "this.Foo(alpha,beta).Bar(gamma).Baz();",
                "this.Foo(alpha, beta)\n    .Bar(gamma)\n    .Baz();\n"
                "conditional chain",
                35,
                "instance?.Foo(alpha)?.Bar(beta)[index]!;",
                "instance\n    ?.Foo(alpha)\n    ?.Bar(beta)[index]!;\n"
                "property chain",
                35,
                "something?.Alpha.Beta!.Gamma.Delta;",
                "something?.Alpha.Beta!.Gamma.Delta;\n"
                "then include",
                35,
                "query.Include(x=>x.Parent).ThenInclude(x=>x.Child).ThenInclude(x=>x.Name).Where(x=>x.Flag);",
                "query\n    .Include(x => x.Parent)\n        .ThenInclude(x => x.Child)\n            .ThenInclude(x =>\n                x.Name\n            )\n    .Where(x => x.Flag);\n"
                "arguments", 35, "Call(one,two,three);", "Call(one, two, three);\n"
                "named arguments",
                35,
                "Call(name:one,ref two,out var three);",
                "Call(\n    name: one,\n    ref two,\n    out var three\n);\n"
                "simple lambda", 35, "Call(x=>x.Property+1);", "Call(x => x.Property + 1);\n"
                "lambda object",
                35,
                "Call(x=>new Thing{Value=x});",
                "Call(x => new Thing\n{\n    Value = x,\n});\n"
                "lambda anonymous",
                35,
                "Call(x=>new{ x.Property });",
                "Call(x => new\n{\n    x.Property,\n});\n"
                "parenthesized lambda", 35, "Call((x,y)=>x+y);", "Call((x, y) => x + y);\n"
                "empty lambda", 35, "Call(()=>Calculate());", "Call(() => Calculate());\n"
                "trailing lambda",
                35,
                "Call(first,second,x=>x.Property+1);",
                "Call(first, second, x =>\n    x.Property + 1\n);\n"
                "trailing empty lambda",
                35,
                "Call(first,second,()=>Calculate());",
                "Call(first, second, () =>\n    Calculate()\n);\n"
                "object one property",
                35,
                "new Thing(){Value=1};",
                "new Thing()\n{\n    Value = 1,\n};\n"
                "implicit object", 35, "new(){Value=1};", "new()\n{\n    Value = 1,\n};\n"
                "empty object", 35, "new Thing{};", "new Thing { };\n"
                "anonymous one property", 35, "new{Value=1};", "new\n{\n    Value = 1,\n};\n"
                "anonymous empty", 35, "new{};", "new { };\n"
                "array", 35, "new int[]{1,2,3};", "new int[] { 1, 2, 3 };\n"
                "implicit array", 35, "new[]{1,2,3};", "new[] { 1, 2, 3 };\n"
                "nested arrays",
                35,
                "new int[][]{new[]{1,2},new[]{3,4}};",
                "new int[][]\n{\n    new[] { 1, 2 },\n    new[] { 3, 4 },\n};\n"
                "complex initializer",
                35,
                "new Dictionary<int,int>{{1,2},{3,4},{5,6}};",
                "new Dictionary<int, int>\n{\n    { 1, 2 },\n    { 3, 4 },\n    { 5, 6 },\n};\n"
                "nested initializer",
                35,
                "new Thing{Property={X=1}};",
                "new Thing\n{\n    Property =\n    {\n        X = 1,\n    },\n};\n"
                "with", 35, "Call(value with{A=1,B=2});", "Call(value with { A = 1, B = 2 });\n"
                "collection", 35, "Call([one,two,three]);", "Call([one, two, three]);\n"
                "nested collection",
                35,
                "Call([[one,two],[three,four]]);",
                "Call([\n    [one, two],\n    [three, four],\n]);\n"
                "spread", 35, "Call([one,..other,two]);", "Call([one, .. other, two]);\n"
                "cast",
                35,
                "(Dictionary<int,string>)value.Method();",
                "(Dictionary<int, string>)\n    value.Method();\n"
                "compact cast", 35, "(int)value;", "(int)value;\n"
                "unary", 35, "-a+~b+ ++c;", "-a + ~b + ++c;\n"
                "range",
                35,
                "Call(values[1..^2],values[..3],values[2..],values[..]);",
                "Call(\n    values[1..^2],\n    values[..3],\n    values[2..],\n    values[..]\n);\n"
                "tuple",
                35,
                "Call((first:one,second:two),((int X,string Y))tuple);",
                "Call(\n    (first: one, second: two),\n    ((int X, string Y))tuple\n);\n"
                "switch",
                35,
                "value switch{1=>one,2 when flag=>two,_=>other};",
                "value switch\n{\n    1 => one,\n    2 when flag => two,\n    _ => other,\n};\n"
                "patterns",
                35,
                "Call(value is Thing{Property:>0 and <10,Other:not null});",
                "Call(\n    value\n        is Thing\n        {\n            Property: > 0 and < 10,\n            Other: not null\n        }\n);\n"
                "positional patterns",
                35,
                "Call(value is Point(1,2));",
                "Call(value is Point(1, 2));\n"
                "list patterns",
                35,
                "Call(value is [one,..var rest]);",
                "Call(value is [one, .. var rest]);\n"
                "interpolation", 35, "$\"value={a+b,10:X}\";", "$\"value={a + b, 10:X}\";\n"
                "interpolation chain",
                35,
                "$\"{value.Foo().Bar().Baz()}\";",
                "$\"{value.Foo().Bar().Baz()}\";\n"
                "verbatim string", 35, "@\"a\nb\";", "@\"a\nb\";\n"
                "raw string",
                35,
                "\"\"\"\n  one\n  two\n  \"\"\";",
                "\"\"\"\n    one\n    two\n    \"\"\";\n"
                "raw interpolation",
                35,
                "$\"\"\"\n  one {a+b}\n  two\n  \"\"\";",
                "$\"\"\"\n    one {a + b}\n    two\n    \"\"\";\n"
                "await", 35, "await Call(one,two);", "await Call(one, two);\n"
                "checked", 35, "checked(a+b);", "checked(a + b);\n"
                "typeof",
                35,
                "typeof(Dictionary<string,int>);",
                "typeof(Dictionary<string, int>);\n"
                "assignment", 35, "a=b=c=d;", "a = b = c = d;\n"
                "initializer comment",
                35,
                "new Thing{Value=1 // value\n};",
                "new Thing\n{\n    Value = 1, // value\n};\n"
                "arguments comment",
                35,
                "Call(one, // one\ntwo);",
                "Call(\n    one, // one\n    two\n);\n"
                "property pattern comment",
                35,
                "Call(value is { // test\nProperty:1});",
                "Call(\n    value\n        is { // test\n            Property: 1\n        }\n);\n"
                "binary precedence",
                20,
                "alpha+beta*gamma-delta;",
                "alpha\n    + beta * gamma\n    - delta;\n"
                "binary equality asymmetry",
                20,
                "left==right&&one!=two||yes==no;",
                "left == right\n    && one != two\n    || yes == no;\n"
                "coalesce", 20, "alpha??beta??gamma;", "alpha\n    ?? beta\n    ?? gamma;\n"
                "terminal coalesce",
                20,
                "receiver.Method()??fallback;",
                "receiver.Method()\n    ?? fallback;\n"
                "nonterminal coalesce",
                20,
                "receiver.Method().Next()??fallback;",
                "receiver\n    .Method()\n    .Next()\n    ?? fallback;\n"
                "conditional",
                20,
                "Call(condition?whenTrue:whenFalse);",
                "Call(\n    condition\n        ? whenTrue\n        : whenFalse\n);\n"
                "chained conditional",
                20,
                "Call(one?first:two?second:third);",
                "Call(\n    one ? first\n    : two ? second\n    : third\n);\n"
                "nested conditional",
                20,
                "one?(two?first:second):third;",
                "one\n    ? (\n        two\n            ? first\n            : second\n    )\n    : third;\n"
                "simple chain",
                20,
                "service.Foo(alpha,beta).Bar(gamma).Baz();",
                "service\n    .Foo(\n        alpha,\n        beta\n    )\n    .Bar(gamma)\n    .Baz();\n"
                "merged chain",
                20,
                "this.Foo(alpha,beta).Bar(gamma).Baz();",
                "this.Foo(\n        alpha,\n        beta\n    )\n    .Bar(gamma)\n    .Baz();\n"
                "conditional chain",
                20,
                "instance?.Foo(alpha)?.Bar(beta)[index]!;",
                "instance\n    ?.Foo(alpha)\n    ?.Bar(beta)[\n        index\n    ]!;\n"
                "property chain",
                20,
                "something?.Alpha.Beta!.Gamma.Delta;",
                "something\n    ?.Alpha\n    .Beta!\n    .Gamma\n    .Delta;\n"
                "then include",
                20,
                "query.Include(x=>x.Parent).ThenInclude(x=>x.Child).ThenInclude(x=>x.Name).Where(x=>x.Flag);",
                "query\n    .Include(x =>\n        x.Parent\n    )\n        .ThenInclude(\n            x =>\n                x.Child\n        )\n            .ThenInclude(\n                x =>\n                    x.Name\n            )\n    .Where(x =>\n        x.Flag\n    );\n"
                "arguments",
                20,
                "Call(one,two,three);",
                "Call(\n    one,\n    two,\n    three\n);\n"
                "named arguments",
                20,
                "Call(name:one,ref two,out var three);",
                "Call(\n    name: one,\n    ref two,\n    out var three\n);\n"
                "simple lambda", 20, "Call(x=>x.Property+1);", "Call(x =>\n    x.Property + 1\n);\n"
                "lambda object",
                20,
                "Call(x=>new Thing{Value=x});",
                "Call(x => new Thing\n{\n    Value = x,\n});\n"
                "lambda anonymous",
                20,
                "Call(x=>new{ x.Property });",
                "Call(x => new\n{\n    x.Property,\n});\n"
                "parenthesized lambda", 20, "Call((x,y)=>x+y);", "Call(\n    (x, y) => x + y\n);\n"
                "empty lambda", 20, "Call(()=>Calculate());", "Call(() =>\n    Calculate()\n);\n"
                "trailing lambda",
                20,
                "Call(first,second,x=>x.Property+1);",
                "Call(\n    first,\n    second,\n    x =>\n        x.Property\n        + 1\n);\n"
                "trailing empty lambda",
                20,
                "Call(first,second,()=>Calculate());",
                "Call(\n    first,\n    second,\n    () =>\n        Calculate()\n);\n"
                "object one property",
                20,
                "new Thing(){Value=1};",
                "new Thing()\n{\n    Value = 1,\n};\n"
                "implicit object", 20, "new(){Value=1};", "new()\n{\n    Value = 1,\n};\n"
                "empty object", 20, "new Thing{};", "new Thing { };\n"
                "anonymous one property", 20, "new{Value=1};", "new\n{\n    Value = 1,\n};\n"
                "anonymous empty", 20, "new{};", "new { };\n"
                "array", 20, "new int[]{1,2,3};", "new int[]\n{\n    1,\n    2,\n    3,\n};\n"
                "implicit array", 20, "new[]{1,2,3};", "new[] { 1, 2, 3 };\n"
                "nested arrays",
                20,
                "new int[][]{new[]{1,2},new[]{3,4}};",
                "new int[][]\n{\n    new[] { 1, 2 },\n    new[] { 3, 4 },\n};\n"
                "complex initializer",
                20,
                "new Dictionary<int,int>{{1,2},{3,4},{5,6}};",
                "new Dictionary<\n    int,\n    int\n>\n{\n    { 1, 2 },\n    { 3, 4 },\n    { 5, 6 },\n};\n"
                "nested initializer",
                20,
                "new Thing{Property={X=1}};",
                "new Thing\n{\n    Property =\n    {\n        X = 1,\n    },\n};\n"
                "with",
                20,
                "Call(value with{A=1,B=2});",
                "Call(\n    value with\n    {\n        A = 1,\n        B = 2,\n    }\n);\n"
                "collection",
                20,
                "Call([one,two,three]);",
                "Call([\n    one,\n    two,\n    three,\n]);\n"
                "nested collection",
                20,
                "Call([[one,two],[three,four]]);",
                "Call([\n    [one, two],\n    [three, four],\n]);\n"
                "spread",
                20,
                "Call([one,..other,two]);",
                "Call([\n    one,\n    .. other,\n    two,\n]);\n"
                "cast",
                20,
                "(Dictionary<int,string>)value.Method();",
                "(Dictionary<\n    int,\n    string\n>)\n    value.Method();\n"
                "compact cast", 20, "(int)value;", "(int)value;\n"
                "unary", 20, "-a+~b+ ++c;", "-a + ~b + ++c;\n"
                "range",
                20,
                "Call(values[1..^2],values[..3],values[2..],values[..]);",
                "Call(\n    values[1..^2],\n    values[..3],\n    values[2..],\n    values[..]\n);\n"
                "tuple",
                20,
                "Call((first:one,second:two),((int X,string Y))tuple);",
                "Call(\n    (\n        first: one,\n        second: two\n    ),\n    ((\n        int X,\n        string Y\n    ))tuple\n);\n"
                "switch",
                20,
                "value switch{1=>one,2 when flag=>two,_=>other};",
                "value switch\n{\n    1 => one,\n    2 when flag =>\n        two,\n    _ => other,\n};\n"
                "patterns",
                20,
                "Call(value is Thing{Property:>0 and <10,Other:not null});",
                "Call(\n    value\n        is Thing\n        {\n            Property: > 0\n                and < 10,\n            Other: not null\n        }\n);\n"
                "positional patterns",
                20,
                "Call(value is Point(1,2));",
                "Call(\n    value\n        is Point(\n            1,\n            2\n        )\n);\n"
                "list patterns",
                20,
                "Call(value is [one,..var rest]);",
                "Call(\n    value\n        is [\n            one,\n            .. var rest,\n        ]\n);\n"
                "interpolation", 20, "$\"value={a+b,10:X}\";", "$\"value={a + b, 10:X}\";\n"
                "interpolation chain",
                20,
                "$\"{value.Foo().Bar().Baz()}\";",
                "$\"{value.Foo().Bar().Baz()}\";\n"
                "verbatim string", 20, "@\"a\nb\";", "@\"a\nb\";\n"
                "raw string",
                20,
                "\"\"\"\n  one\n  two\n  \"\"\";",
                "\"\"\"\n    one\n    two\n    \"\"\";\n"
                "raw interpolation",
                20,
                "$\"\"\"\n  one {a+b}\n  two\n  \"\"\";",
                "$\"\"\"\n    one {a + b}\n    two\n    \"\"\";\n"
                "await", 20, "await Call(one,two);", "await Call(\n    one,\n    two\n);\n"
                "checked", 20, "checked(a+b);", "checked(a + b);\n"
                "typeof",
                20,
                "typeof(Dictionary<string,int>);",
                "typeof(Dictionary<\n    string,\n    int\n>);\n"
                "assignment", 20, "a=b=c=d;", "a = b = c = d;\n"
                "initializer comment",
                20,
                "new Thing{Value=1 // value\n};",
                "new Thing\n{\n    Value = 1, // value\n};\n"
                "arguments comment",
                20,
                "Call(one, // one\ntwo);",
                "Call(\n    one, // one\n    two\n);\n"
                "property pattern comment",
                20,
                "Call(value is { // test\nProperty:1});",
                "Call(\n    value\n        is { // test\n            Property: 1\n        }\n);\n"
                "switch blank first arm",
                100,
                "value switch{\n\n1=>one,\n\n_=>other};",
                "value switch\n{\n    1 => one,\n\n    _ => other,\n};\n"
                "switch arrow comment",
                100,
                "value switch{1 /* arrow */ =>one,_=>other};",
                "value switch\n{\n    1 /* arrow */\n    => one,\n    _ => other,\n};\n"
                "switch discard when",
                100,
                "value switch{_ when condition=>one,_=>other};",
                "value switch\n{\n    _ when condition => one,\n    _ => other,\n};\n"
                "typed recursive pattern",
                100,
                "Call(value is Thing{Property:>0 and <10} instance);",
                "Call(value is Thing { Property: > 0 and < 10 } instance);\n"
                "positional named pattern",
                100,
                "Call(value is Point(X:1,Y:2) point);",
                "Call(value is Point(X: 1, Y: 2) point);\n"
                "list closing comment",
                100,
                "Call(value is [1,2 // comment\n]);",
                "Call(\n    value\n        is [\n            1,\n            2, // comment\n        ]\n);\n"
                "collection closing comment",
                100,
                "Call([1,2 // comment\n]);",
                "Call([\n    1,\n    2, // comment\n]);\n"
                "array closing comment",
                100,
                "new int[]{1,2 // comment\n};",
                "new int[]\n{\n    1,\n    2, // comment\n};\n"
                "array multiline comment",
                100,
                "new int[]{1, /* comment */2};",
                "new int[]\n{\n    1, /* comment */\n    2,\n};\n"
                "argument multiline comment",
                100,
                "Call(first, /* comment */ second);",
                "Call(\n    first, /* comment */\n    second\n);\n"
                "coalesce await",
                100,
                "await receiver.Method()??fallback;",
                "await receiver.Method() ?? fallback;\n"
                "coalesce parenthesized",
                100,
                "(firstCall().SecondCall())??fallback;",
                "(firstCall().SecondCall()) ?? fallback;\n"
                "coalesce cast",
                100,
                "(Thing)(receiver.Method())??fallback;",
                "(Thing)(receiver.Method()) ?? fallback;\n"
                "coalesce conditional call",
                100,
                "receiver?.Method()??fallback;",
                "receiver?.Method() ?? fallback;\n"
                "coalesce conditional nonterminal",
                100,
                "receiver?.First()?.Second()??fallback;",
                "receiver?.First()?.Second() ?? fallback;\n"
                "generic assignment",
                100,
                "target=new Dictionary<long,string>();",
                "target = new Dictionary<long, string>();\n"
                "literal assignment",
                100,
                "target=100000+200000*300000;",
                "target = 100000 + 200000 * 300000;\n"
                "binary ternary",
                100,
                "Call(first==second?whenTrue:whenFalse);",
                "Call(first == second ? whenTrue : whenFalse);\n"
                "collection assignment",
                100,
                "target=[one,two,three];",
                "target = [one, two, three];\n"
                "interpolated raw indentation",
                100,
                "Call($\"\"\"\n    one {first+second}\n      two\n    \n    \"\"\");",
                "Call(\n    $\"\"\"\n    one {first + second}\n      two\n\n    \"\"\"\n);\n"
                "raw indentation",
                100,
                "Call(\"\"\"\n    one\n      two\n    \n    \"\"\");",
                "Call(\n    \"\"\"\n    one\n      two\n\n    \"\"\"\n);\n"
                "function pointer cast",
                100,
                "Call((delegate* unmanaged[Cdecl]<int,int>)value);",
                "Call((delegate* unmanaged[Cdecl]<int, int>)value);\n"
                "lambda typed parameters",
                100,
                "Call((ref int x,out string y)=>x+y.Length);",
                "Call((ref int x, out string y) => x + y.Length);\n"
                "bracket arguments",
                100,
                "Call(items[first,second,third]);",
                "Call(items[first, second, third]);\n"
                "generic type args",
                100,
                "Call<TypeOne,Dictionary<TypeTwo,TypeThree>,TypeFour>();",
                "Call<TypeOne, Dictionary<TypeTwo, TypeThree>, TypeFour>();\n"
                "omitted type args", 100, "typeof(Dictionary<,>);", "typeof(Dictionary<,>);\n"
                "switch blank first arm",
                35,
                "value switch{\n\n1=>one,\n\n_=>other};",
                "value switch\n{\n    1 => one,\n\n    _ => other,\n};\n"
                "switch arrow comment",
                35,
                "value switch{1 /* arrow */ =>one,_=>other};",
                "value switch\n{\n    1 /* arrow */\n    => one,\n    _ => other,\n};\n"
                "switch discard when",
                35,
                "value switch{_ when condition=>one,_=>other};",
                "value switch\n{\n    _ when condition => one,\n    _ => other,\n};\n"
                "typed recursive pattern",
                35,
                "Call(value is Thing{Property:>0 and <10} instance);",
                "Call(\n    value\n        is Thing\n        {\n            Property: > 0 and < 10\n        } instance\n);\n"
                "positional named pattern",
                35,
                "Call(value is Point(X:1,Y:2) point);",
                "Call(\n    value\n        is Point(X: 1, Y: 2) point\n);\n"
                "list closing comment",
                35,
                "Call(value is [1,2 // comment\n]);",
                "Call(\n    value\n        is [\n            1,\n            2, // comment\n        ]\n);\n"
                "collection closing comment",
                35,
                "Call([1,2 // comment\n]);",
                "Call([\n    1,\n    2, // comment\n]);\n"
                "array closing comment",
                35,
                "new int[]{1,2 // comment\n};",
                "new int[]\n{\n    1,\n    2, // comment\n};\n"
                "array multiline comment",
                35,
                "new int[]{1, /* comment */2};",
                "new int[]\n{\n    1, /* comment */\n    2,\n};\n"
                "argument multiline comment",
                35,
                "Call(first, /* comment */ second);",
                "Call(\n    first, /* comment */\n    second\n);\n"
                "coalesce await",
                35,
                "await receiver.Method()??fallback;",
                "await receiver.Method()\n    ?? fallback;\n"
                "coalesce parenthesized",
                35,
                "(firstCall().SecondCall())??fallback;",
                "(firstCall().SecondCall())\n    ?? fallback;\n"
                "coalesce cast",
                35,
                "(Thing)(receiver.Method())??fallback;",
                "(Thing)(receiver.Method())\n    ?? fallback;\n"
                "coalesce conditional call",
                35,
                "receiver?.Method()??fallback;",
                "receiver?.Method() ?? fallback;\n"
                "coalesce conditional nonterminal",
                35,
                "receiver?.First()?.Second()??fallback;",
                "receiver?.First()?.Second()\n    ?? fallback;\n"
                "generic assignment",
                35,
                "target=new Dictionary<long,string>();",
                "target =\n    new Dictionary<long, string>();\n"
                "literal assignment",
                35,
                "target=100000+200000*300000;",
                "target = 100000 + 200000 * 300000;\n"
                "binary ternary",
                35,
                "Call(first==second?whenTrue:whenFalse);",
                "Call(\n    first == second\n        ? whenTrue\n        : whenFalse\n);\n"
                "collection assignment",
                35,
                "target=[one,two,three];",
                "target = [one, two, three];\n"
                "interpolated raw indentation",
                35,
                "Call($\"\"\"\n    one {first+second}\n      two\n    \n    \"\"\");",
                "Call(\n    $\"\"\"\n    one {first + second}\n      two\n\n    \"\"\"\n);\n"
                "raw indentation",
                35,
                "Call(\"\"\"\n    one\n      two\n    \n    \"\"\");",
                "Call(\n    \"\"\"\n    one\n      two\n\n    \"\"\"\n);\n"
                "function pointer cast",
                35,
                "Call((delegate* unmanaged[Cdecl]<int,int>)value);",
                "Call(\n    (delegate* unmanaged[Cdecl]<\n        int,\n        int>)value\n);\n"
                "lambda typed parameters",
                35,
                "Call((ref int x,out string y)=>x+y.Length);",
                "Call(\n    (ref int x, out string y) =>\n        x + y.Length\n);\n"
                "bracket arguments",
                35,
                "Call(items[first,second,third]);",
                "Call(items[first, second, third]);\n"
                "generic type args",
                35,
                "Call<TypeOne,Dictionary<TypeTwo,TypeThree>,TypeFour>();",
                "Call<\n    TypeOne,\n    Dictionary<TypeTwo, TypeThree>,\n    TypeFour\n>();\n"
                "omitted type args", 35, "typeof(Dictionary<,>);", "typeof(Dictionary<,>);\n"
                "switch blank first arm",
                20,
                "value switch{\n\n1=>one,\n\n_=>other};",
                "value switch\n{\n    1 => one,\n\n    _ => other,\n};\n"
                "switch arrow comment",
                20,
                "value switch{1 /* arrow */ =>one,_=>other};",
                "value switch\n{\n    1 /* arrow */\n    => one,\n    _ => other,\n};\n"
                "switch discard when",
                20,
                "value switch{_ when condition=>one,_=>other};",
                "value switch\n{\n    _ when condition =>\n        one,\n    _ => other,\n};\n"
                "typed recursive pattern",
                20,
                "Call(value is Thing{Property:>0 and <10} instance);",
                "Call(\n    value\n        is Thing\n        {\n            Property: > 0\n                and < 10\n        } instance\n);\n"
                "positional named pattern",
                20,
                "Call(value is Point(X:1,Y:2) point);",
                "Call(\n    value\n        is Point(\n            X: 1,\n            Y: 2\n        ) point\n);\n"
                "list closing comment",
                20,
                "Call(value is [1,2 // comment\n]);",
                "Call(\n    value\n        is [\n            1,\n            2, // comment\n        ]\n);\n"
                "collection closing comment",
                20,
                "Call([1,2 // comment\n]);",
                "Call([\n    1,\n    2, // comment\n]);\n"
                "array closing comment",
                20,
                "new int[]{1,2 // comment\n};",
                "new int[]\n{\n    1,\n    2, // comment\n};\n"
                "array multiline comment",
                20,
                "new int[]{1, /* comment */2};",
                "new int[]\n{\n    1, /* comment */\n    2,\n};\n"
                "argument multiline comment",
                20,
                "Call(first, /* comment */ second);",
                "Call(\n    first, /* comment */\n    second\n);\n"
                "coalesce await",
                20,
                "await receiver.Method()??fallback;",
                "await receiver.Method()\n    ?? fallback;\n"
                "coalesce parenthesized",
                20,
                "(firstCall().SecondCall())??fallback;",
                "(\n    firstCall()\n        .SecondCall()\n) ?? fallback;\n"
                "coalesce cast",
                20,
                "(Thing)(receiver.Method())??fallback;",
                "(Thing)(\n    receiver.Method()\n) ?? fallback;\n"
                "coalesce conditional call",
                20,
                "receiver?.Method()??fallback;",
                "receiver?.Method()\n    ?? fallback;\n"
                "coalesce conditional nonterminal",
                20,
                "receiver?.First()?.Second()??fallback;",
                "receiver\n    ?.First()\n    ?.Second()\n    ?? fallback;\n"
                "generic assignment",
                20,
                "target=new Dictionary<long,string>();",
                "target =\n    new Dictionary<\n        long,\n        string\n    >();\n"
                "literal assignment",
                20,
                "target=100000+200000*300000;",
                "target =\n    100000\n    + 200000\n        * 300000;\n"
                "binary ternary",
                20,
                "Call(first==second?whenTrue:whenFalse);",
                "Call(\n    first == second\n        ? whenTrue\n        : whenFalse\n);\n"
                "collection assignment",
                20,
                "target=[one,two,three];",
                "target =\n[\n    one,\n    two,\n    three,\n];\n"
                "interpolated raw indentation",
                20,
                "Call($\"\"\"\n    one {first+second}\n      two\n    \n    \"\"\");",
                "Call(\n    $\"\"\"\n    one {first + second}\n      two\n\n    \"\"\"\n);\n"
                "raw indentation",
                20,
                "Call(\"\"\"\n    one\n      two\n    \n    \"\"\");",
                "Call(\n    \"\"\"\n    one\n      two\n\n    \"\"\"\n);\n"
                "function pointer cast",
                20,
                "Call((delegate* unmanaged[Cdecl]<int,int>)value);",
                "Call(\n    (delegate* unmanaged[Cdecl]<\n        int,\n        int>)value\n);\n"
                "lambda typed parameters",
                20,
                "Call((ref int x,out string y)=>x+y.Length);",
                "Call(\n    (\n        ref int x,\n        out string y\n    ) =>\n        x + y.Length\n);\n"
                "bracket arguments",
                20,
                "Call(items[first,second,third]);",
                "Call(\n    items[\n        first,\n        second,\n        third\n    ]\n);\n"
                "generic type args",
                20,
                "Call<TypeOne,Dictionary<TypeTwo,TypeThree>,TypeFour>();",
                "Call<\n    TypeOne,\n    Dictionary<\n        TypeTwo,\n        TypeThree\n    >,\n    TypeFour\n>();\n"
                "omitted type args", 20, "typeof(Dictionary<,>);", "typeof(Dictionary<,>);\n"
            ] do
            test ($"expression: {name} / {width}") {
                let options =
                    { PrinterOptions.Default with
                        Width = width
                    }

                Expect.equal
                    (printSyntax source options)
                    expected
                    "Expression layout matches the expected output byte for byte, \
except where a fixture records a deliberate divergence."
            }
    ]

let private statementFixtures =
    [
        for name, width, source, expected in
            [
                "if_while",
                100,
                "class C{void M(){if(first&&second||third){A();}else if(other)B();else{C();}while(alpha&&beta)while(gamma){D();}}}",
                "class C\n{\n    void M()\n    {\n        if (first && second || third)\n        {\n            A();\n        }\n        else if (other)\n            B();\n        else\n        {\n            C();\n        }\n\n        while (alpha && beta)\n        while (gamma)\n        {\n            D();\n        }\n    }\n}\n"
                "loops",
                100,
                "class C{void M(){for(int i=0;i<upperBound;i++,j++){A();}foreach(var item in collection)foreach(var other in item){B();}do{C();}while(alpha&&beta);}}",
                "class C\n{\n    void M()\n    {\n        for (int i = 0; i < upperBound; i++, j++)\n        {\n            A();\n        }\n\n        foreach (var item in collection)\n        foreach (var other in item)\n        {\n            B();\n        }\n\n        do\n        {\n            C();\n        } while (alpha && beta);\n    }\n}\n"
                "using_lock_fixed",
                100,
                "unsafe class C{void M(){using(var first=Acquire())using(var second=Acquire()){A();}lock(gate){B();}fixed(int* pointer=data){C();}}}",
                "unsafe class C\n{\n    void M()\n    {\n        using (var first = Acquire())\n        using (var second = Acquire())\n        {\n            A();\n        }\n\n        lock (gate)\n        {\n            B();\n        }\n\n        fixed (int* pointer = data)\n        {\n            C();\n        }\n    }\n}\n"
                "switch_try",
                100,
                "class C{void M(){switch(a,b){case(1,2):{A();break;}case(3,4)when first&&second:B();break;default:throw new Exception();}try{A();}catch(Exception e)when(first&&second){B();}finally{C();}}}",
                "class C\n{\n    void M()\n    {\n        switch (a, b)\n        {\n            case (1, 2):\n            {\n                A();\n                break;\n            }\n            case (3, 4) when first && second:\n                B();\n                break;\n            default:\n                throw new Exception();\n        }\n\n        try\n        {\n            A();\n        }\n        catch (Exception e) when (first && second)\n        {\n            B();\n        }\n        finally\n        {\n            C();\n        }\n    }\n}\n"
                "fields",
                100,
                "class C{static public readonly int first=alpha+beta; public int a=1,b=2,c=3;public event Action E;public fixed byte Buffer[100];}",
                "class C\n{\n    public static readonly int first = alpha + beta;\n    public int a = 1,\n        b = 2,\n        c = 3;\n    public event Action E;\n    public fixed byte Buffer[100];\n}\n"
                "methods",
                100,
                "class C<T>:Base,IFoo,IBar where T:class,new(){public C(int first,int second):base(first,second){A();}~C(){B();}public static C operator+(C a,C b)=>a;public static implicit operator int(C value)=>1;public T M<U>(U value)where U:class=>default;}",
                "class C<T> : Base, IFoo, IBar\n    where T : class, new()\n{\n    public C(int first, int second)\n        : base(first, second)\n    {\n        A();\n    }\n\n    ~C()\n    {\n        B();\n    }\n\n    public static C operator +(C a, C b) => a;\n\n    public static implicit operator int(C value) => 1;\n\n    public T M<U>(U value)\n        where U : class => default;\n}\n"
                "properties",
                100,
                "class C{public int P{get;private set;}public int Q{get{return field;}set{field=value;}}public int this[int first,int second]{get=>items[first,second];}public event Action E{add{Register(value);}remove{Unregister(value);}}}",
                "class C\n{\n    public int P { get; private set; }\n    public int Q\n    {\n        get { return field; }\n        set { field = value; }\n    }\n    public int this[int first, int second]\n    {\n        get => items[first, second];\n    }\n    public event Action E\n    {\n        add { Register(value); }\n        remove { Unregister(value); }\n    }\n}\n"
                "attrs",
                100,
                "[One][Two(alphaArgument,betaArgument)]public class C{[A][B]public void M([A][B]int first,[C]in long second){A();}[One]public int P{[A]get;private set;}}",
                "[One]\n[Two(alphaArgument, betaArgument)]\npublic class C\n{\n    [A]\n    [B]\n    public void M([A] [B] int first, [C] in long second)\n    {\n        A();\n    }\n\n    [One]\n    public int P { [A] get; private set; }\n}\n"
                "members",
                100,
                "abstract class C{int a;int b;\n\nint c; // end\n// start\nint d;abstract void M();abstract void N();void O(){}class Nested{}int P{get;} } interface I{void M();void N();int P{get;}} enum E{A,B,\n\n// c\nC}",
                "abstract class C\n{\n    int a;\n    int b;\n\n    int c; // end\n\n    // start\n    int d;\n    abstract void M();\n    abstract void N();\n\n    void O() { }\n\n    class Nested { }\n\n    int P { get; }\n}\n\ninterface I\n{\n    void M();\n    void N();\n    int P { get; }\n}\n\nenum E\n{\n    A,\n    B,\n\n    // c\n    C,\n}\n"
                "namespaces",
                100,
                "extern alias Z;using Z.C;namespace N{using Zebra;using System;class C{void M(){}}}namespace Q{}",
                "extern alias Z;\nusing Z.C;\n\nnamespace N\n{\n    using System;\n    using Zebra;\n\n    class C\n    {\n        void M() { }\n    }\n}\n\nnamespace Q { }\n"
                "return_binary",
                100,
                "class C{bool M(){return first&&second||third;}void N(){yield return value;yield break;goto label;label:checked{A();}unsafe{B();}}}",
                "class C\n{\n    bool M()\n    {\n        return first && second || third;\n    }\n\n    void N()\n    {\n        yield return value;\n        yield break;\n        goto label;\n        label:\n        checked\n        {\n            A();\n        }\n\n        unsafe\n        {\n            B();\n        }\n    }\n}\n"
                "ignore_attributes",
                100,
                "class C{\n// csff-ignore\n[A(  1,2)]\npublic void M(  ){A(  1,2);}\n\n[A]\n// csff-ignore\npublic void N(  ){A(  3,4);}\n}",
                "class C\n{\n    // csff-ignore\n[A(  1,2)]\n    public void M()\n    {\n        A(1, 2);\n    }\n\n    [A]\n    // csff-ignore\npublic void N(  ){A(  3,4);}\n}\n"
                "using_directives",
                100,
                "// header\nusing Z;\n#if WINDOWS\nusing System.X;\nusing A;\n#endif\nusing System.B;\nusing static Z;\nusing A=Z.X;\nclass C{}",
                "// header\nusing System.B;\nusing Z;\nusing static Z;\nusing A = Z.X;\n#if WINDOWS\nusing System.X;\nusing A;\n#endif\nclass C { }\n"
                "ignore_using",
                100,
                "// csff-ignore-start\nusing Z =   Some.Namespace;\nusing A =   Other.Namespace;\n// csff-ignore-end\nclass C{}",
                "// csff-ignore-start\nusing Z =   Some.Namespace;\nusing A =   Other.Namespace;\n// csff-ignore-end\nclass C { }\n"
                "regions",
                100,
                "class C{\n#region Members\nint A;\n\n// comment\nint B;\n#endregion\n\n#region Methods\nvoid M(){A();\n\n// second\nB();}\n#endregion\n}",
                "class C\n{\n    #region Members\n    int A;\n\n    // comment\n    int B;\n    #endregion\n\n    #region Methods\n    void M()\n    {\n        A();\n\n        // second\n        B();\n    }\n    #endregion\n}\n"
                "comments",
                100,
                "// header\n\nclass C{/*first*/int A; // trailing\n\n/// summary\nint B;void M(){A( /* one */ first, second /*two*/ );\n// final\n}\n// last\n}\n// EOF\n",
                "// header\n\nclass C\n{ /*first*/\n    int A; // trailing\n\n    /// summary\n    int B;\n\n    void M()\n    {\n        A( /* one */\n            first,\n            second /*two*/\n        );\n        // final\n    }\n    // last\n}\n// EOF\n"
                "empty_blocks",
                100,
                "class C{void M(){}C(){}int P{get{}set{}}}class D{}",
                "class C\n{\n    void M() { }\n\n    C() { }\n\n    int P\n    {\n        get { }\n        set { }\n    }\n}\n\nclass D { }\n"
                "delegates",
                100,
                "[A]public delegate T Factory<T>(int first,long second)where T:class;internal struct S;public readonly record struct R(int Value);",
                "[A]\npublic delegate T Factory<T>(int first, long second)\n    where T : class;\n\ninternal struct S;\n\npublic readonly record struct R(int Value);\n"
                "nested_directives",
                100,
                "class C{void M(){\n#if A\n#if B\nCall(alphaArgument,betaArgument);\n#elif C\nOther(gammaArgument,deltaArgument);\n#else\nFallback(epsilonArgument,zetaArgument);\n#endif\n#else\nDefault(alphaArgument,betaArgument);\n#endif\n}}",
                "class C\n{\n    void M()\n    {\n#if A\n#if B\n        Call(alphaArgument, betaArgument);\n#elif C\n        Other(gammaArgument, deltaArgument);\n#else\n        Fallback(epsilonArgument, zetaArgument);\n#endif\n#else\n        Default(alphaArgument, betaArgument);\n#endif\n    }\n}\n"
                "ignore",
                100,
                "class C{ // a\n// csff-ignore\nvoid M(  ){A( 1,  2);}\n// csff-ignore-start\nvoid N(  ){B( 3,  4);}\nvoid O(  ){C( 5,  6);}\n// csff-ignore-end\nvoid P(  ){D( 7,  8);}}\n",
                "class C\n{ // a\n    // csff-ignore\nvoid M(  ){A( 1,  2);}\n    // csff-ignore-start\nvoid N(  ){B( 3,  4);}\nvoid O(  ){C( 5,  6);}\n    // csff-ignore-end\n    void P()\n    {\n        D(7, 8);\n    }\n}\n"
                "usings",
                100,
                "// header\nusing Zebra;\n// hello\nusing System.B;\nusing System.A;\nusing static System.Math;\nusing A = Z.X;\nusing Systematic;\nusing static Abc;\nusing Z = A.X;\nclass C{}\n",
                "// header\nusing System.A;\n// hello\nusing System.B;\nusing Systematic;\nusing Zebra;\nusing static System.Math;\nusing static Abc;\nusing A = Z.X;\nusing Z = A.X;\n\nclass C { }\n"
                "trivia",
                100,
                "class C{int P{get;private set;} void M(){\n#region A\n// hello\nA();\n\nB();\n#endregion\n// csff-ignore-start\nvar x = F(  1,  2);\nx ++;\n// csff-ignore-end\nC();\n} }\n",
                "class C\n{\n    int P { get; private set; }\n\n    void M()\n    {\n        #region A\n        // hello\n        A();\n\n        B();\n        #endregion\n// csff-ignore-start\nvar x = F(  1,  2);\nx ++;\n        // csff-ignore-end\n        C();\n    }\n}\n"
                "preprocessor",
                100,
                "class C{\n#if WINDOWS\nvoid M(){Call(alphaArgument,betaArgument,gammaArgument);}\n#else\nvoid N(){Call(deltaArgument,epsilonArgument,zetaArgument);}\n#endif\n}\n",
                "class C\n{\n#if WINDOWS\n    void M()\n    {\n        Call(alphaArgument, betaArgument, gammaArgument);\n    }\n#else\n    void N()\n    {\n        Call(deltaArgument, epsilonArgument, zetaArgument);\n    }\n#endif\n}\n"
                "if_while",
                40,
                "class C{void M(){if(first&&second||third){A();}else if(other)B();else{C();}while(alpha&&beta)while(gamma){D();}}}",
                "class C\n{\n    void M()\n    {\n        if (first && second || third)\n        {\n            A();\n        }\n        else if (other)\n            B();\n        else\n        {\n            C();\n        }\n\n        while (alpha && beta)\n        while (gamma)\n        {\n            D();\n        }\n    }\n}\n"
                "loops",
                40,
                "class C{void M(){for(int i=0;i<upperBound;i++,j++){A();}foreach(var item in collection)foreach(var other in item){B();}do{C();}while(alpha&&beta);}}",
                "class C\n{\n    void M()\n    {\n        for (\n            int i = 0;\n            i < upperBound;\n            i++, j++\n        )\n        {\n            A();\n        }\n\n        foreach (var item in collection)\n        foreach (var other in item)\n        {\n            B();\n        }\n\n        do\n        {\n            C();\n        } while (alpha && beta);\n    }\n}\n"
                "using_lock_fixed",
                40,
                "unsafe class C{void M(){using(var first=Acquire())using(var second=Acquire()){A();}lock(gate){B();}fixed(int* pointer=data){C();}}}",
                "unsafe class C\n{\n    void M()\n    {\n        using (var first = Acquire())\n        using (var second = Acquire())\n        {\n            A();\n        }\n\n        lock (gate)\n        {\n            B();\n        }\n\n        fixed (int* pointer = data)\n        {\n            C();\n        }\n    }\n}\n"
                "switch_try",
                40,
                "class C{void M(){switch(a,b){case(1,2):{A();break;}case(3,4)when first&&second:B();break;default:throw new Exception();}try{A();}catch(Exception e)when(first&&second){B();}finally{C();}}}",
                "class C\n{\n    void M()\n    {\n        switch (a, b)\n        {\n            case (1, 2):\n            {\n                A();\n                break;\n            }\n            case (3, 4)\n                when first && second:\n                B();\n                break;\n            default:\n                throw new Exception();\n        }\n\n        try\n        {\n            A();\n        }\n        catch (Exception e)\n            when (first && second)\n        {\n            B();\n        }\n        finally\n        {\n            C();\n        }\n    }\n}\n"
                "fields",
                40,
                "class C{static public readonly int first=alpha+beta; public int a=1,b=2,c=3;public event Action E;public fixed byte Buffer[100];}",
                "class C\n{\n    public static readonly int first =\n        alpha + beta;\n    public int a = 1,\n        b = 2,\n        c = 3;\n    public event Action E;\n    public fixed byte Buffer[100];\n}\n"
                "methods",
                40,
                "class C<T>:Base,IFoo,IBar where T:class,new(){public C(int first,int second):base(first,second){A();}~C(){B();}public static C operator+(C a,C b)=>a;public static implicit operator int(C value)=>1;public T M<U>(U value)where U:class=>default;}",
                "class C<T> : Base, IFoo, IBar\n    where T : class, new()\n{\n    public C(int first, int second)\n        : base(first, second)\n    {\n        A();\n    }\n\n    ~C()\n    {\n        B();\n    }\n\n    public static C operator +(\n        C a,\n        C b\n    ) => a;\n\n    public static implicit operator int(\n        C value\n    ) => 1;\n\n    public T M<U>(U value)\n        where U : class => default;\n}\n"
                "properties",
                40,
                "class C{public int P{get;private set;}public int Q{get{return field;}set{field=value;}}public int this[int first,int second]{get=>items[first,second];}public event Action E{add{Register(value);}remove{Unregister(value);}}}",
                "class C\n{\n    public int P { get; private set; }\n    public int Q\n    {\n        get { return field; }\n        set { field = value; }\n    }\n    public int this[\n        int first,\n        int second\n    ]\n    {\n        get => items[first, second];\n    }\n    public event Action E\n    {\n        add { Register(value); }\n        remove { Unregister(value); }\n    }\n}\n"
                "attrs",
                40,
                "[One][Two(alphaArgument,betaArgument)]public class C{[A][B]public void M([A][B]int first,[C]in long second){A();}[One]public int P{[A]get;private set;}}",
                "[One]\n[Two(alphaArgument, betaArgument)]\npublic class C\n{\n    [A]\n    [B]\n    public void M(\n        [A] [B] int first,\n        [C] in long second\n    )\n    {\n        A();\n    }\n\n    [One]\n    public int P\n    {\n        [A]\n        get;\n        private set;\n    }\n}\n"
                "members",
                40,
                "abstract class C{int a;int b;\n\nint c; // end\n// start\nint d;abstract void M();abstract void N();void O(){}class Nested{}int P{get;} } interface I{void M();void N();int P{get;}} enum E{A,B,\n\n// c\nC}",
                "abstract class C\n{\n    int a;\n    int b;\n\n    int c; // end\n\n    // start\n    int d;\n    abstract void M();\n    abstract void N();\n\n    void O() { }\n\n    class Nested { }\n\n    int P { get; }\n}\n\ninterface I\n{\n    void M();\n    void N();\n    int P { get; }\n}\n\nenum E\n{\n    A,\n    B,\n\n    // c\n    C,\n}\n"
                "namespaces",
                40,
                "extern alias Z;using Z.C;namespace N{using Zebra;using System;class C{void M(){}}}namespace Q{}",
                "extern alias Z;\nusing Z.C;\n\nnamespace N\n{\n    using System;\n    using Zebra;\n\n    class C\n    {\n        void M() { }\n    }\n}\n\nnamespace Q { }\n"
                "return_binary",
                40,
                "class C{bool M(){return first&&second||third;}void N(){yield return value;yield break;goto label;label:checked{A();}unsafe{B();}}}",
                "class C\n{\n    bool M()\n    {\n        return first && second || third;\n    }\n\n    void N()\n    {\n        yield return value;\n        yield break;\n        goto label;\n        label:\n        checked\n        {\n            A();\n        }\n\n        unsafe\n        {\n            B();\n        }\n    }\n}\n"
                "ignore_attributes",
                40,
                "class C{\n// csff-ignore\n[A(  1,2)]\npublic void M(  ){A(  1,2);}\n\n[A]\n// csff-ignore\npublic void N(  ){A(  3,4);}\n}",
                "class C\n{\n    // csff-ignore\n[A(  1,2)]\n    public void M()\n    {\n        A(1, 2);\n    }\n\n    [A]\n    // csff-ignore\npublic void N(  ){A(  3,4);}\n}\n"
                "using_directives",
                40,
                "// header\nusing Z;\n#if WINDOWS\nusing System.X;\nusing A;\n#endif\nusing System.B;\nusing static Z;\nusing A=Z.X;\nclass C{}",
                "// header\nusing System.B;\nusing Z;\nusing static Z;\nusing A = Z.X;\n#if WINDOWS\nusing System.X;\nusing A;\n#endif\nclass C { }\n"
                "ignore_using",
                40,
                "// csff-ignore-start\nusing Z =   Some.Namespace;\nusing A =   Other.Namespace;\n// csff-ignore-end\nclass C{}",
                "// csff-ignore-start\nusing Z =   Some.Namespace;\nusing A =   Other.Namespace;\n// csff-ignore-end\nclass C { }\n"
                "regions",
                40,
                "class C{\n#region Members\nint A;\n\n// comment\nint B;\n#endregion\n\n#region Methods\nvoid M(){A();\n\n// second\nB();}\n#endregion\n}",
                "class C\n{\n    #region Members\n    int A;\n\n    // comment\n    int B;\n    #endregion\n\n    #region Methods\n    void M()\n    {\n        A();\n\n        // second\n        B();\n    }\n    #endregion\n}\n"
                "comments",
                40,
                "// header\n\nclass C{/*first*/int A; // trailing\n\n/// summary\nint B;void M(){A( /* one */ first, second /*two*/ );\n// final\n}\n// last\n}\n// EOF\n",
                "// header\n\nclass C\n{ /*first*/\n    int A; // trailing\n\n    /// summary\n    int B;\n\n    void M()\n    {\n        A( /* one */\n            first,\n            second /*two*/\n        );\n        // final\n    }\n    // last\n}\n// EOF\n"
                "empty_blocks",
                40,
                "class C{void M(){}C(){}int P{get{}set{}}}class D{}",
                "class C\n{\n    void M() { }\n\n    C() { }\n\n    int P\n    {\n        get { }\n        set { }\n    }\n}\n\nclass D { }\n"
                "delegates",
                40,
                "[A]public delegate T Factory<T>(int first,long second)where T:class;internal struct S;public readonly record struct R(int Value);",
                "[A]\npublic delegate T Factory<T>(\n    int first,\n    long second\n)\n    where T : class;\n\ninternal struct S;\n\npublic readonly record struct R(\n    int Value\n);\n"
                "nested_directives",
                40,
                "class C{void M(){\n#if A\n#if B\nCall(alphaArgument,betaArgument);\n#elif C\nOther(gammaArgument,deltaArgument);\n#else\nFallback(epsilonArgument,zetaArgument);\n#endif\n#else\nDefault(alphaArgument,betaArgument);\n#endif\n}}",
                "class C\n{\n    void M()\n    {\n#if A\n#if B\n        Call(\n            alphaArgument,\n            betaArgument\n        );\n#elif C\n        Other(\n            gammaArgument,\n            deltaArgument\n        );\n#else\n        Fallback(\n            epsilonArgument,\n            zetaArgument\n        );\n#endif\n#else\n        Default(\n            alphaArgument,\n            betaArgument\n        );\n#endif\n    }\n}\n"
                "ignore",
                40,
                "class C{ // a\n// csff-ignore\nvoid M(  ){A( 1,  2);}\n// csff-ignore-start\nvoid N(  ){B( 3,  4);}\nvoid O(  ){C( 5,  6);}\n// csff-ignore-end\nvoid P(  ){D( 7,  8);}}\n",
                "class C\n{ // a\n    // csff-ignore\nvoid M(  ){A( 1,  2);}\n    // csff-ignore-start\nvoid N(  ){B( 3,  4);}\nvoid O(  ){C( 5,  6);}\n    // csff-ignore-end\n    void P()\n    {\n        D(7, 8);\n    }\n}\n"
                "usings",
                40,
                "// header\nusing Zebra;\n// hello\nusing System.B;\nusing System.A;\nusing static System.Math;\nusing A = Z.X;\nusing Systematic;\nusing static Abc;\nusing Z = A.X;\nclass C{}\n",
                "// header\nusing System.A;\n// hello\nusing System.B;\nusing Systematic;\nusing Zebra;\nusing static System.Math;\nusing static Abc;\nusing A = Z.X;\nusing Z = A.X;\n\nclass C { }\n"
                "trivia",
                40,
                "class C{int P{get;private set;} void M(){\n#region A\n// hello\nA();\n\nB();\n#endregion\n// csff-ignore-start\nvar x = F(  1,  2);\nx ++;\n// csff-ignore-end\nC();\n} }\n",
                "class C\n{\n    int P { get; private set; }\n\n    void M()\n    {\n        #region A\n        // hello\n        A();\n\n        B();\n        #endregion\n// csff-ignore-start\nvar x = F(  1,  2);\nx ++;\n        // csff-ignore-end\n        C();\n    }\n}\n"
                "preprocessor",
                40,
                "class C{\n#if WINDOWS\nvoid M(){Call(alphaArgument,betaArgument,gammaArgument);}\n#else\nvoid N(){Call(deltaArgument,epsilonArgument,zetaArgument);}\n#endif\n}\n",
                "class C\n{\n#if WINDOWS\n    void M()\n    {\n        Call(\n            alphaArgument,\n            betaArgument,\n            gammaArgument\n        );\n    }\n#else\n    void N()\n    {\n        Call(\n            deltaArgument,\n            epsilonArgument,\n            zetaArgument\n        );\n    }\n#endif\n}\n"
            ] do
            test ($"statement: {name} / {width}") {
                let options =
                    { PrinterOptions.Default with
                        Width = width
                    }

                Expect.equal
                    (printSyntax source options)
                    expected
                    "Match the historically captured statement and declaration layouts byte for byte."
            }
    ]

let private controlStatementSpacingFixtures =
    let check source expected =
        let options = PrinterOptions.Default
        let actual = printSyntax source options
        Expect.equal actual expected "Separate control statements from their siblings."
        Expect.equal (printSyntax actual options) actual "Spacing is idempotent."

        TokenPreservation.Checker().Check(options, "control-spacing.cs", source, actual)
        |> function
            | Ok() -> ()
            | Error error -> failtest error

    let indent (text: string) =
        text.Split('\n')
        |> Array.map (fun line -> "        " + line)
        |> String.concat "\n"

    [
        for name, statement, expected in
            [
                "if",
                "if(condition){Call();}else if(other){Other();}else{Fallback();}",
                "if (condition)\n{\n    Call();\n}\nelse if (other)\n{\n    Other();\n}\nelse\n{\n    Fallback();\n}"
                "for", "for(;;){Call();}", "for (; ; )\n{\n    Call();\n}"
                "foreach",
                "foreach(var item in items){Call();}",
                "foreach (var item in items)\n{\n    Call();\n}"
                "foreach-variable",
                "foreach(var (a,b) in pairs){Call();}",
                "foreach (var (a, b) in pairs)\n{\n    Call();\n}"
                "while", "while(condition){Call();}", "while (condition)\n{\n    Call();\n}"
                "do", "do{Call();}while(condition);", "do\n{\n    Call();\n} while (condition);"
                "switch",
                "switch(value){default:break;}",
                "switch (value)\n{\n    default:\n        break;\n}"
                "try",
                "try{Call();}catch{Recover();}finally{Finish();}",
                "try\n{\n    Call();\n}\ncatch\n{\n    Recover();\n}\nfinally\n{\n    Finish();\n}"
                "lock", "lock(gate){Call();}", "lock (gate)\n{\n    Call();\n}"
                "fixed", "fixed(int* p=data){Call();}", "fixed (int* p = data)\n{\n    Call();\n}"
                "unsafe", "unsafe{Call();}", "unsafe\n{\n    Call();\n}"
            ] do
            test ($"control-spacing: top-level {name}") {
                check
                    ("Before();" + statement + "After();")
                    ("Before();\n\n" + expected + "\n\nAfter();\n")
            }

            test ($"control-spacing: block {name}") {
                check
                    ("class C{void M(){Before();" + statement + "After();}}")
                    ("class C\n{\n    void M()\n    {\n        Before();\n\n"
                     + indent expected
                     + "\n\n        After();\n    }\n}\n")
            }

            test ($"control-spacing: only top-level {name}") { check statement (expected + "\n") }

            test ($"control-spacing: only block {name}") {
                check
                    ("class C{void M(){" + statement + "}}")
                    ("class C\n{\n    void M()\n    {\n" + indent expected + "\n    }\n}\n")
            }

        for accessor, declaration in
            [
                "get", "int P"
                "set", "int P"
                "init", "int P"
                "add", "event Action P"
                "remove", "event Action P"
            ] do
            test ($"control-spacing: {accessor} accessor") {
                check
                    ("class C{"
                     + declaration
                     + "{"
                     + accessor
                     + "{Before();if(c){Call();}After();}}}")
                    ("class C\n{\n    "
                     + declaration
                     + "\n    {\n        "
                     + accessor
                     + "\n        {\n            Before();\n\n            if (c)\n            {\n                Call();\n            }\n\n            After();\n        }\n    }\n}\n")
            }

        for accessor, declaration in
            [
                "get", "int P"
                "set", "int P"
                "add", "event Action P"
                "remove", "event Action P"
            ] do
            for opening, closing, margin in
                [ "#if X", "#endif", ""; "#region R", "#endregion", "            " ] do
                test ($"control-spacing: {accessor} accessor before {closing}") {
                    check
                        ("class C{"
                         + declaration
                         + "{"
                         + accessor
                         + "{Before();\n"
                         + opening
                         + "\nif(c){Call();}\n"
                         + closing
                         + "\nAfter();}}}")
                        ("class C\n{\n    "
                         + declaration
                         + "\n    {\n        "
                         + accessor
                         + "\n        {\n            Before();\n\n"
                         + margin
                         + opening
                         + "\n            if (c)\n            {\n                Call();\n            }\n"
                         + margin
                         + closing
                         + "\n\n            After();\n        }\n    }\n}\n")
                }

            test ($"control-spacing: {accessor} accessor ignore range") {
                check
                    ("class C{"
                     + declaration
                     + "{"
                     + accessor
                     + "{Before();\n// csff-ignore-start\nif(c){Call();}After();\n// csff-ignore-end\nNext();}}}")
                    ("class C\n{\n    "
                     + declaration
                     + "\n    {\n        "
                     + accessor
                     + "\n        {\n            Before();\n            // csff-ignore-start\nif(c){Call();}After();\n            // csff-ignore-end\n            Next();\n        }\n    }\n}\n")
            }

        test "control-spacing: alternate branch after a closing directive" {
            check
                "class C{void M(){Before();\n#if X\nB();\n#elif Y\nint x\n#region R\nC();\n#endregion\n#else\nif(c){D();}\n#endif\nAfter();}}"
                "class C\n{\n    void M()\n    {\n        Before();\n#if X\n        B();\n#elif Y\nint x\n#region R\nC();\n#endregion\n#else\n        if (c)\n        {\n            D();\n        }\n#endif\n\n        After();\n    }\n}\n"
        }

        let alternate =
            "Before();\n#if false\n#region R\nX();\n#endregion\n#else\nif(c){D();}\n#endif\nAfter();"

        test "control-spacing: top-level alternate branch after a closing directive" {
            check
                alternate
                "Before();\n#if false\n#region R\nX();\n#endregion\n#else\nif (c)\n{\n    D();\n}\n#endif\n\nAfter();\n"
        }

        test "control-spacing: switch section alternate branch after a closing directive" {
            check
                ("class C{void M(int v){switch(v){case 1:" + alternate + "\nbreak;}}}")
                "class C\n{\n    void M(int v)\n    {\n        switch (v)\n        {\n            case 1:\n                Before();\n#if false\n#region R\nX();\n#endregion\n#else\n                if (c)\n                {\n                    D();\n                }\n#endif\n\n                After();\n                break;\n        }\n    }\n}\n"
        }

        test "control-spacing: accessor alternate branch after a closing directive" {
            check
                ("class C{int P{get{" + alternate + "\nreturn 1;}}}")
                "class C\n{\n    int P\n    {\n        get\n        {\n            Before();\n#if false\n#region R\nX();\n#endregion\n#else\n            if (c)\n            {\n                D();\n            }\n#endif\n\n            After();\n            return 1;\n        }\n    }\n}\n"
        }

        test "control-spacing: adjacent, labelled and commented statements" {
            check
                "Before();label:if(c){A();} // tail\n// next\nwhile(c){B();}After();"
                "Before();\n\nlabel:\nif (c)\n{\n    A();\n} // tail\n\n// next\nwhile (c)\n{\n    B();\n}\n\nAfter();\n"
        }

        test "control-spacing: using is excluded" {
            check
                "Before();using(a)using(b){Call();}After();"
                "Before();\nusing (a)\nusing (b)\n{\n    Call();\n}\nAfter();\n"
        }

        test "control-spacing: switch section siblings" {
            check
                "switch(value){case 1:Before();if(c){Call();}After();break;}"
                "switch (value)\n{\n    case 1:\n        Before();\n\n        if (c)\n        {\n            Call();\n        }\n\n        After();\n        break;\n}\n"
        }

        test "control-spacing: complex block path" {
            check
                "#nullable enable\nclass C{void M(){Before();if(c){Call();}After();}}"
                "#nullable enable\nclass C\n{\n    void M()\n    {\n        Before();\n\n        if (c)\n        {\n            Call();\n        }\n\n        After();\n    }\n}\n"
        }

        test "control-spacing: complex top-level path" {
            check
                "#nullable enable\nBefore();if(c){Call();}After();"
                "#nullable enable\nBefore();\n\nif (c)\n{\n    Call();\n}\n\nAfter();\n"
        }

        test "control-spacing: conditional branches" {
            check
                "Before();\n#if A\nif(c){A();}\n#else\nwhile(c){B();}\n#endif\nAfter();"
                "Before();\n\n#if A\nif (c)\n{\n    A();\n}\n#else\nwhile (c)\n{\n    B();\n}\n#endif\n\nAfter();\n"
        }

        test "control-spacing: region boundary" {
            check
                "class C{void M(){Before();\n#region Control\nif(c){A();}\n#endregion\nAfter();}}"
                "class C\n{\n    void M()\n    {\n        Before();\n\n        #region Control\n        if (c)\n        {\n            A();\n        }\n        #endregion\n\n        After();\n    }\n}\n"
        }
    ]

let private retiredMarkerFixtures =
    [
        test "statement: retired csharpier-ignore markers format like any comment" {
            Expect.equal
                (printSyntax
                    "class C{\n// csharpier-ignore\nvoid M(  ){A( 1,  2);}\n// csharpier-ignore-start\nvoid N(  ){B( 3,  4);}\n// csharpier-ignore-end\nvoid O(  ){C( 5,  6);}}\n"
                    PrinterOptions.Default)
                "class C\n{\n    // csharpier-ignore\n    void M()\n    {\n        A(1, 2);\n    }\n\n    // csharpier-ignore-start\n    void N()\n    {\n        B(3, 4);\n    }\n\n    // csharpier-ignore-end\n    void O()\n    {\n        C(5, 6);\n    }\n}\n"
                "Only csff-ignore markers keep source spans unformatted."
        }
    ]

let private configurationFixtures =
    [
        for name, width, tabs, endOfLine, source, expected in
            [
                "query",
                40,
                false,
                EndOfLine.Lf,
                "class C{void M(){var q=from int a in values join b in others on a.Id equals b.Id into matches let c=a.Value where c>lower&&c<upper orderby c descending,a.Id select new{a,c} into result group result by result.c;var r=from component in new[]{\"position\",\"scale\"} from axis in new[]{\"X\",\"Y\",\"Z\"} select GetName(component,axis);}}",
                "class C\n{\n    void M()\n    {\n        var q =\n            from int a in values\n            join b in others\n                on a.Id equals b.Id\n                into matches\n            let c = a.Value\n            where c > lower && c < upper\n            orderby c descending, a.Id\n            select new\n            {\n                a,\n                c,\n            } into result\n            group result by result.c;\n        var r =\n            from component in new[]\n            {\n                \"position\",\n                \"scale\",\n            }\n            from axis in new[]\n            {\n                \"X\",\n                \"Y\",\n                \"Z\",\n            }\n            select GetName(\n                component,\n                axis\n            );\n    }\n}\n"
                "preprocessor_boolean",
                40,
                false,
                EndOfLine.Lf,
                "class C{\n#if FIRST && (SECOND || THIRD)\nvoid M(){Call(alphaArgument,betaArgument,gammaArgument);}\n#elif OTHER != false\nvoid N(){Other(alphaArgument,betaArgument,gammaArgument);}\n#else\nvoid O(){Default(alphaArgument,betaArgument,gammaArgument);}\n#endif\n}",
                "class C\n{\n#if FIRST && (SECOND || THIRD)\n    void M()\n    {\n        Call(\n            alphaArgument,\n            betaArgument,\n            gammaArgument\n        );\n    }\n#elif OTHER != false\n    void N()\n    {\n        Other(\n            alphaArgument,\n            betaArgument,\n            gammaArgument\n        );\n    }\n#else\n    void O()\n    {\n        Default(\n            alphaArgument,\n            betaArgument,\n            gammaArgument\n        );\n    }\n#endif\n}\n"
                "query",
                100,
                false,
                EndOfLine.Lf,
                "class C{void M(){var q=from int a in values join b in others on a.Id equals b.Id into matches let c=a.Value where c>lower&&c<upper orderby c descending,a.Id select new{a,c} into result group result by result.c;var r=from component in new[]{\"position\",\"scale\"} from axis in new[]{\"X\",\"Y\",\"Z\"} select GetName(component,axis);}}",
                "class C\n{\n    void M()\n    {\n        var q =\n            from int a in values\n            join b in others on a.Id equals b.Id into matches\n            let c = a.Value\n            where c > lower && c < upper\n            orderby c descending, a.Id\n            select new\n            {\n                a,\n                c,\n            } into result\n            group result by result.c;\n        var r =\n            from component in new[] { \"position\", \"scale\" }\n            from axis in new[] { \"X\", \"Y\", \"Z\" }\n            select GetName(component, axis);\n    }\n}\n"
                "preprocessor_boolean",
                100,
                false,
                EndOfLine.Lf,
                "class C{\n#if FIRST && (SECOND || THIRD)\nvoid M(){Call(alphaArgument,betaArgument,gammaArgument);}\n#elif OTHER != false\nvoid N(){Other(alphaArgument,betaArgument,gammaArgument);}\n#else\nvoid O(){Default(alphaArgument,betaArgument,gammaArgument);}\n#endif\n}",
                "class C\n{\n#if FIRST && (SECOND || THIRD)\n    void M()\n    {\n        Call(alphaArgument, betaArgument, gammaArgument);\n    }\n#elif OTHER != false\n    void N()\n    {\n        Other(alphaArgument, betaArgument, gammaArgument);\n    }\n#else\n    void O()\n    {\n        Default(alphaArgument, betaArgument, gammaArgument);\n    }\n#endif\n}\n"
                "query",
                40,
                true,
                EndOfLine.Lf,
                "class C{void M(){var q=from int a in values join b in others on a.Id equals b.Id into matches let c=a.Value where c>lower&&c<upper orderby c descending,a.Id select new{a,c} into result group result by result.c;var r=from component in new[]{\"position\",\"scale\"} from axis in new[]{\"X\",\"Y\",\"Z\"} select GetName(component,axis);}}",
                "class C\n{\n\tvoid M()\n\t{\n\t\tvar q =\n\t\t\tfrom int a in values\n\t\t\tjoin b in others\n\t\t\t\ton a.Id equals b.Id\n\t\t\t\tinto matches\n\t\t\tlet c = a.Value\n\t\t\twhere c > lower && c < upper\n\t\t\torderby c descending, a.Id\n\t\t\tselect new\n\t\t\t{\n\t\t\t\ta,\n\t\t\t\tc,\n\t\t\t} into result\n\t\t\tgroup result by result.c;\n\t\tvar r =\n\t\t\tfrom component in new[]\n\t\t\t{\n\t\t\t\t\"position\",\n\t\t\t\t\"scale\",\n\t\t\t}\n\t\t\tfrom axis in new[]\n\t\t\t{\n\t\t\t\t\"X\",\n\t\t\t\t\"Y\",\n\t\t\t\t\"Z\",\n\t\t\t}\n\t\t\tselect GetName(\n\t\t\t\tcomponent,\n\t\t\t\taxis\n\t\t\t);\n\t}\n}\n"
                "preprocessor_boolean",
                40,
                true,
                EndOfLine.Lf,
                "class C{\n#if FIRST && (SECOND || THIRD)\nvoid M(){Call(alphaArgument,betaArgument,gammaArgument);}\n#elif OTHER != false\nvoid N(){Other(alphaArgument,betaArgument,gammaArgument);}\n#else\nvoid O(){Default(alphaArgument,betaArgument,gammaArgument);}\n#endif\n}",
                "class C\n{\n#if FIRST && (SECOND || THIRD)\n\tvoid M()\n\t{\n\t\tCall(\n\t\t\talphaArgument,\n\t\t\tbetaArgument,\n\t\t\tgammaArgument\n\t\t);\n\t}\n#elif OTHER != false\n\tvoid N()\n\t{\n\t\tOther(\n\t\t\talphaArgument,\n\t\t\tbetaArgument,\n\t\t\tgammaArgument\n\t\t);\n\t}\n#else\n\tvoid O()\n\t{\n\t\tDefault(\n\t\t\talphaArgument,\n\t\t\tbetaArgument,\n\t\t\tgammaArgument\n\t\t);\n\t}\n#endif\n}\n"
                "query",
                40,
                false,
                EndOfLine.CrLf,
                "class C{void M(){var q=from int a in values join b in others on a.Id equals b.Id into matches let c=a.Value where c>lower&&c<upper orderby c descending,a.Id select new{a,c} into result group result by result.c;var r=from component in new[]{\"position\",\"scale\"} from axis in new[]{\"X\",\"Y\",\"Z\"} select GetName(component,axis);}}",
                "class C\r\n{\r\n    void M()\r\n    {\r\n        var q =\r\n            from int a in values\r\n            join b in others\r\n                on a.Id equals b.Id\r\n                into matches\r\n            let c = a.Value\r\n            where c > lower && c < upper\r\n            orderby c descending, a.Id\r\n            select new\r\n            {\r\n                a,\r\n                c,\r\n            } into result\r\n            group result by result.c;\r\n        var r =\r\n            from component in new[]\r\n            {\r\n                \"position\",\r\n                \"scale\",\r\n            }\r\n            from axis in new[]\r\n            {\r\n                \"X\",\r\n                \"Y\",\r\n                \"Z\",\r\n            }\r\n            select GetName(\r\n                component,\r\n                axis\r\n            );\r\n    }\r\n}\r\n"
                "preprocessor_boolean",
                40,
                false,
                EndOfLine.CrLf,
                "class C{\n#if FIRST && (SECOND || THIRD)\nvoid M(){Call(alphaArgument,betaArgument,gammaArgument);}\n#elif OTHER != false\nvoid N(){Other(alphaArgument,betaArgument,gammaArgument);}\n#else\nvoid O(){Default(alphaArgument,betaArgument,gammaArgument);}\n#endif\n}",
                "class C\r\n{\r\n#if FIRST && (SECOND || THIRD)\r\n    void M()\r\n    {\r\n        Call(\r\n            alphaArgument,\r\n            betaArgument,\r\n            gammaArgument\r\n        );\r\n    }\r\n#elif OTHER != false\r\n    void N()\r\n    {\r\n        Other(\r\n            alphaArgument,\r\n            betaArgument,\r\n            gammaArgument\r\n        );\r\n    }\r\n#else\r\n    void O()\r\n    {\r\n        Default(\r\n            alphaArgument,\r\n            betaArgument,\r\n            gammaArgument\r\n        );\r\n    }\r\n#endif\r\n}\r\n"
            ] do
            test ($"configuration: {name} / {width} / tabs {tabs} / {endOfLine}") {
                let options =
                    { PrinterOptions.Default with
                        Width = width
                        UseTabs = tabs
                        EndOfLine = endOfLine
                    }

                Expect.equal
                    (printSyntax source options)
                    expected
                    "All conditional branches and query clauses match the historically captured oracle output."
            }
    ]

let private memberListFixtures =
    [
        "attributes and separator comments",
        "enum E{[A] One /* first */, // comma\n/// two\n[B] Two=2, /* next */ Three // final\n}",
        "enum E\n{\n    [A]\n    One /* first */\n    , // comma\n\n    /// two\n    [B]\n    Two = 2, /* next */\n    Three, // final\n}\n"
        "ignored middle range",
        "enum E{A,\n// csff-ignore-start\nB  =  2, C  =  3,\n// csff-ignore-end\n[D] D /* keep */, E}",
        "enum E\n{\n    A,\n    // csff-ignore-start\nB  =  2, C  =  3,\n    // csff-ignore-end\n    [D]\n    D /* keep */\n    ,\n    E,\n}\n"
        "ignored initial range",
        "enum E{\n// csff-ignore-start\nA  =  1, B  =  2,\n// csff-ignore-end\nC, D,}",
        "enum E\n{\n    // csff-ignore-start\nA  =  1, B  =  2,\n    // csff-ignore-end\n    C,\n    D,\n}\n"
        "ignored final range",
        "enum E{A,\n// csff-ignore-start\nB  =  2, C  =  3,}",
        "enum E\n{\n    A,\n    // csff-ignore-start\nB  =  2, C  =  3,\n}\n"
        "alias order ignores the equals token",
        "using A1=System.String;\nusing A=System.Int32;\nclass C{void M(){}}",
        "using A = System.Int32;\nusing A1 = System.String;\n\nclass C\n{\n    void M() { }\n}\n"
        "individually ignored member",
        "enum E{A,\n// csff-ignore\nB  =  2,\n[C] C,D}",
        "enum E\n{\n    A,\n\n    // csff-ignore\nB  =  2,\n\n    [C]\n    C,\n    D,\n}\n"
        "conditional members",
        "enum E{\n[A] A,\n#if DEBUG\n[B] B,\n#else\nC,\n#endif\n[D] D // keep\n}",
        "enum E\n{\n    [A]\n    A,\n\n#if DEBUG\n    [B]\n    B,\n#else\n    C,\n#endif\n\n    [D]\n    D, // keep\n}\n"
        "mixed method grouping",
        "abstract class C{int a;abstract void A();abstract void B();void M(){}abstract void D();class Nested{void A(){}void B(){}}} interface I{void A();void B();} class Plain{void A(){}void B(){}}",
        "abstract class C\n{\n    int a;\n    abstract void A();\n    abstract void B();\n\n    void M() { }\n\n    abstract void D();\n\n    class Nested\n    {\n        void A() { }\n\n        void B() { }\n    }\n}\n\ninterface I\n{\n    void A();\n    void B();\n}\n\nclass Plain\n{\n    void A() { }\n\n    void B() { }\n}\n"
    ]
    |> List.map (fun (name, source, expected) ->
        test ($"member list metadata preserves output / {name}") {
            let options = PrinterOptions.Default
            let actual = printSyntax source options
            Expect.equal actual expected "Member spacing and original separators keep their bytes."

            TokenPreservation.Checker().Check(options, "member-list.cs", source, actual)
            |> function
                | Ok() -> ()
                | Error error -> failtest error

            Expect.equal (printSyntax actual options) actual "Member lists stay idempotent."
        })

let private anonymousMethodFixtures =
    [
        "anonymous method blocks are formatted"
        "class C\n{\n    void M()\n    {\n        Call(delegate { });\n        Call(delegate { return; });\n        Call(delegate (int x) { });\n        Func<bool, bool> f1 = delegate (bool a) { return !a; };\n    }\n}\n"
        "class C\n{\n    void M()\n    {\n        Call(delegate { });\n        Call(\n            delegate\n            {\n                return;\n            }\n        );\n        Call(delegate(int x) { });\n        Func<bool, bool> f1 = delegate(bool a)\n        {\n            return !a;\n        };\n    }\n}\n"
    ]
    |> List.chunkBySize 3
    |> List.map (fun chunk ->
        let name = chunk[0]
        let source = chunk[1]
        let expected = chunk[2]

        test ($"anonymous method / {name}") {
            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "An anonymous method's block is formatted."

            TokenPreservation.Checker().Check(PrinterOptions.Default, "anon.cs", source, actual)
            |> function
                | Ok() -> ()
                | Error error -> failtest error

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        })

let private solverReachabilityRegressions =
    [
        "a skipped redefinition inside a comment beside a real one"
        "#if A\n/*\n#undef B\n*/\n#undef A\n#if B == !A\nclass One{}\n#endif\n#endif\nclass Two{}\n"
        "class One { }"

        "a real redefinition in an inactive branch and a commented one outside it"
        "#if A\n#undef A\n#endif\n/*\n#undef C\n*/\n#if !A && C\nclass Three{}\n#endif\nclass Four{}\n"
        "class Three { }"

        "a condition whose path search is expensive, under an enclosing condition"
        "#if ROOT || ALT\n#if CONDITION\nclass Deep{}\n#endif\n#endif\nclass Outer{}\n"
        "class Deep { }"
    ]
    |> List.chunkBySize 3
    |> List.map (fun chunk ->
        let name = chunk[0]

        let source =
            chunk[1]
                .Replace(
                    "CONDITION",
                    "((A||C)&&(A||!C)&&(!A||C)&&(!A||!C)&&(X1==X1)&&(X2==X2)&&(X3==X3)&&(X4==X4)&&(X5==X5)&&(X6==X6)&&(X7==X7)&&(X8==X8)&&(X9==X9)&&(X10==X10))||B"
                )

        let expected = chunk[2]

        test ($"solver reachability / {name}") {
            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                expected
                "A class some configuration makes live code is formatted."

            TokenPreservation.Checker().Check(PrinterOptions.Default, "solver.cs", source, actual)
            |> function
                | Ok() -> ()
                | Error error -> failtest error
        })

let private conditionalLexingRegressions =
    [
        test "a directive after documentation in a skipped branch still counts" {
            let source =
                "#if A\n/** documentation */ #warning @\"\n#if B\nclass Target{}\n#endif\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "Code a configuration makes reachable is formatted."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "hidden directives in a comment cost about linearly" {
            let source count =
                let inner = String.replicate count "#warning\n$@\"{\n"

                "#if A\n/*\n#if B\nclass Target{}\n#endif\n"
                + inner
                + "*/\n#endif\nclass Outer{}\n"

            let allocated count =
                let text = source count
                let tree = SyntaxTree()
                Parser.parse text tree
                use document = new DocumentBuffer()
                use builder = new SyntaxDocumentBuilder()

                for _ = 1 to 2 do
                    document.Reset()
                    builder.Build(text, tree, document, PrinterOptions.Default)

                let before = GC.GetAllocatedBytesForCurrentThread()
                document.Reset()
                builder.Build(text, tree, document, PrinterOptions.Default)
                GC.GetAllocatedBytesForCurrentThread() - before

            let small = allocated 400
            let large = allocated 800
            let ratio = float large / float small

            printfn
                "hidden directives: 400 = %d bytes, 800 = %d bytes, ratio %.2f"
                small
                large
                ratio

            Expect.isLessThan ratio 2.5 "Cost must grow with the file, not with its square."
        }
    ]

let private conditionalPassSeams =
    [
        test "a pass reads the directive index of the text it was handed" {
            let source =
                "{\n{\n#if !C\n// csff-ignore-start - reason\n{\n}\n#elif (FLAG||C)&&C\n"
                + "#if A&&B\n/*\n#endif\n*/\n#endif\n#if B&&FLAG\n#endif\n}\n}\n"

            let expected =
                "{\n    {\n#if !C\n// csff-ignore-start - reason\n{\n}\n#elif (FLAG||C)&&C\n"
                + "#if A&&B\n        /*\n#endif\n        */\n#endif\n#if B&&FLAG\n#endif\n    }\n}\n"

            Expect.equal
                (printSyntax
                    source
                    { PrinterOptions.Default with
                        Width = 100
                    })
                expected
                "The comment keeps the columns the previous pass's scanner gave it."
        }
        test "seeded symbols lex a pass exactly as a define preamble did" {
            let sources =
                [
                    "#if A\nclass T{}\n#endif\nclass U{}\n"
                    "#if A\nclass T{}\n#else\nclass V{}\n#endif\n"
                    "#if A\n/*\n#endif\n*/\nclass W{}\n"
                    "#if A\n#undef A\n#endif\n#if A\nclass X{}\n#endif\n"
                    "#if A&&B\nclass Y{}\n#elif A\nclass Z{}\n#endif\n"
                    "class C{\n#if A\nint a;\n#endif\nstring s = \"#if A\";\n}\n"
                    "#if \\u0041\nclass E{}\n#endif\nclass F{}\n"
                    "#if A\u00ADB\nclass G{}\n#endif\nclass H{}\n"
                    "class I{}\n#define A\n#if A&&B\nclass J{}\n#endif\n"
                ]

            for source in sources do
                let tree = SyntaxTree()
                Parser.parse source tree
                let selected = Preprocessor.symbolSets source tree

                Expect.isNonEmpty selected ("A seeded configuration exists for " + source)

                for symbols in Array.append [| [||] |] selected do
                    let prefix =
                        symbols
                        |> Array.map (fun symbol -> "#define " + symbol + "\n")
                        |> String.concat ""

                    let seeded = SyntaxTree()
                    Parser.parseWith symbols source seeded
                    let prefixed = SyntaxTree()
                    Parser.parse (prefix + source) prefixed

                    let configuration = "symbols " + String.Join(",", symbols) + " of " + source

                    let trivia (tree: SyntaxTree) shift =
                        [
                            for i = 0 to tree.LexerBuffer.TriviaCount - 1 do
                                let item = tree.LexerBuffer.Trivia i

                                if item.Start >= shift then
                                    yield item.Kind, item.Start - shift, item.Length
                        ]

                    let tokens (tree: SyntaxTree) shift =
                        [
                            for i = 0 to tree.TokenCount - 1 do
                                let token = tree.Token i
                                yield token.Kind, token.Start - shift, token.Length
                        ]

                    Expect.equal
                        (trivia seeded 0)
                        (trivia prefixed prefix.Length)
                        ("The trivia stream agrees for " + configuration)

                    Expect.equal
                        (tokens seeded 0)
                        (tokens prefixed prefix.Length)
                        ("The token stream agrees for " + configuration)
        }
        test "malformed #define and #if directives do not invent bogus empty symbol sets" {
            for source in
                [
                    "#define @foo\n#if @foo\nclass A {}\n#else\nclass B {}\n#endif\n"
                    "#if @foo\nclass A {}\n#else\nclass B {}\n#endif\n"
                ] do
                let tree = SyntaxTree()
                Parser.parse source tree
                let sets = Preprocessor.symbolSets source tree

                Expect.isEmpty
                    sets
                    ("Empty symbol key stays internal and does not produce seeded configurations: "
                     + source)
        }
        test "format-char boolean defines and != recovery match lexer symbol sets" {
            let formatCharSource = "#define tr\u200cue\n#if Y && !\nclass Target{}\n#endif\n"
            let formatTree = SyntaxTree()
            Parser.parse formatCharSource formatTree

            Expect.equal
                (Preprocessor.symbolSets formatCharSource formatTree)
                [| [| "Y" |] |]
                "Format character in tr\u200cue keeps it a distinct symbol rather than poisoning empty recovery."

            let formattedFormatChar = printSyntax formatCharSource PrinterOptions.Default

            Expect.stringContains
                formattedFormatChar
                "class Target { }"
                "Reachable branch under {Y} is formatted."

            let notEqualsSource =
                "#define\n#if != false\nclass Target{}\n#else\nclass Alt{}\n#endif\n"

            let printedNotEquals = printSyntax notEqualsSource PrinterOptions.Default

            Expect.stringContains
                printedNotEquals
                "class Target { }"
                "Empty #define with != false compares empty symbol against false and takes the first branch."

            let condNotEquals = "#define\n#if Y && != false\nclass Target{}\n#endif\n"
            let condTree = SyntaxTree()
            Parser.parse condNotEquals condTree

            Expect.equal
                (Preprocessor.symbolSets condNotEquals condTree)
                [| [| "Y" |] |]
                "Solver preserves != with empty recovery operand."
        }
    ]

let private conditionalLexingScaling =
    [
        test "a directive after documentation in an inactive branch stays invisible" {
            let source = "#if false\n/** doc */ #if B\n#endif\n#if C\nclass Target{}\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "Code a configuration makes reachable is formatted."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a comment full of branch transitions costs no worse than quadratically" {
            let source count =
                let inner = String.replicate count "#if B\n#else\n#endif\n$@\"{\n"
                "#if A\n/*\n" + inner + "*/\n#endif\nclass Outer{}\n"

            let allocated count =
                let text = source count
                let tree = SyntaxTree()
                Parser.parse text tree
                use document = new DocumentBuffer()
                use builder = new SyntaxDocumentBuilder()

                for _ = 1 to 2 do
                    document.Reset()
                    builder.Build(text, tree, document, PrinterOptions.Default)

                let before = GC.GetAllocatedBytesForCurrentThread()
                document.Reset()
                builder.Build(text, tree, document, PrinterOptions.Default)
                GC.GetAllocatedBytesForCurrentThread() - before

            let small = allocated 10
            let large = allocated 20
            let ratio = float large / float small

            printfn "branch transitions: 10 = %d bytes, 20 = %d bytes, ratio %.2f" small large ratio

            Expect.isLessThan ratio 6.0 "Cost must stay within a quadratic shape."
        }
    ]

let private conditionalWitnessSelection =
    [
        test "a selected configuration must be one the file can be parsed under" {
            let source =
                "#if B||true\n#endif\n#if (A&&C)||B\nclass Target{}\n#endif\n#if B\nclass Broken{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "Code a usable configuration makes reachable is formatted."
        }
        test "a comment ending inside an apparent documentation opener closes it" {
            let source = "/* x\n/** doc */ #if false\n#if A\nclass Target{}\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."

            Expect.stringContains
                actual
                "class Target { }"
                "Code a configuration makes reachable is formatted."
        }
    ]

let private conditionalWitnessBounds =
    [
        test "folding a complement keeps a usable witness" {
            let source =
                "#if A&&(B||!B)\nclass Target{}\n#endif\n#if A&&!B\nclass Broken{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "A usable configuration is found even when the minimal one is not."
        }
        test "validating configurations does not reparse the file for each one" {
            let guard = String.concat "&&" [ for i in 1..12 -> $"(S{i}||T{i})" ]
            let classes = String.concat "" [ for i in 1..2000 -> $"class C{i} {{ }}\n" ]
            let text = "#if " + guard + "\nclass Broken{\n#endif\n" + classes
            let tree = SyntaxTree()
            Parser.parse text tree
            use document = new DocumentBuffer()
            use builder = new SyntaxDocumentBuilder()

            for _ = 1 to 2 do
                document.Reset()
                builder.Build(text, tree, document, PrinterOptions.Default)

            let before = GC.GetAllocatedBytesForCurrentThread()
            document.Reset()
            builder.Build(text, tree, document, PrinterOptions.Default)
            let megabytes = float (GC.GetAllocatedBytesForCurrentThread() - before) / 1e6

            printfn "witness validation: %.3f MB for %d characters" megabytes text.Length

            Expect.isLessThan megabytes 20.0 "Rejecting a configuration costs one parse."
        }
    ]

let private conditionalPassScaling =
    [
        test "independent conditional regions do not cost worse than they do now" {
            let source count =
                String.concat "" [ for i in 1..count -> $"#if S{i}\nclass C{i} {{ }}\n#endif\n" ]

            let allocated count =
                let text = source count
                let tree = SyntaxTree()
                Parser.parse text tree
                use document = new DocumentBuffer()
                use builder = new SyntaxDocumentBuilder()

                for _ = 1 to 3 do
                    document.Reset()
                    builder.Build(text, tree, document, PrinterOptions.Default)

                let before = GC.GetAllocatedBytesForCurrentThread()
                document.Reset()
                builder.Build(text, tree, document, PrinterOptions.Default)
                GC.GetAllocatedBytesForCurrentThread() - before

            let small = allocated 32
            let large = allocated 64
            let ratio = float large / float small

            printfn
                "conditional regions: 32 = %d bytes, 64 = %d bytes, ratio %.2f"
                small
                large
                ratio

            Expect.isLessThan ratio 2.5 "Independent conditional regions cost linearly."
        }
    ]

let private cleanRoomParityRegressions =
    [
        test "a raw interpolated string keeps a line's trailing spaces after a hole" {
            let source =
                "class C\n{\n    string S = $\"\"\"\n        value {1}   \n        \"\"\";\n}\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "The spaces are the string's value."
        }
        test "raw string blank lines are idempotent across line endings" {
            let checker = TokenPreservation.Checker()

            for prefix in [ ""; "$"; "$$" ] do
                for inputEol in [ "\n"; "\r\n"; "\r" ] do
                    for ending, outputEol in [ EndOfLine.Lf, "\n"; EndOfLine.CrLf, "\r\n" ] do
                        let options =
                            { PrinterOptions.Default with
                                EndOfLine = ending
                            }

                        let source =
                            "class C { string S = "
                            + prefix
                            + "\"\"\""
                            + inputEol
                            + String.concat
                                inputEol
                                [ ""; "    "; "        "; "           "; "        \"\"\"; }" ]

                        let expected =
                            String.concat
                                outputEol
                                [
                                    "class C"
                                    "{"
                                    "    string S = " + prefix + "\"\"\""
                                    ""
                                    ""
                                    ""
                                    "           "
                                    "        \"\"\";"
                                    "}"
                                    ""
                                ]

                        let actual = printSyntax source options

                        Expect.equal
                            actual
                            expected
                            "Only whitespace beyond the raw margin is string content."

                        Expect.equal
                            (printSyntax actual options)
                            actual
                            "Blank lines are idempotent."

                        checker.Check(options, "raw-blank-lines.cs", source, actual)
                        |> function
                            | Ok() -> ()
                            | Error error -> failtest error
        }
        test "modifiers under a directive keep their source order" {
            let source =
                "class C\n{\n#if FLAG\n    static\n#endif\n    public void M() { }\n}\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.equal
                actual
                source
                "Sorting would move static across the directive and change the declaration."
        }
        test "the file modifier sorts into its access-modifier slot" {
            Expect.equal
                (printSyntax "sealed file class T { }\n" PrinterOptions.Default)
                "file sealed class T { }\n"
                "file ranks with the access modifiers, ahead of sealed."

            Expect.equal
                (printSyntax "file sealed class T { }\n" PrinterOptions.Default)
                "file sealed class T { }\n"
                "The sorted order is already canonical."

            Expect.equal
                (printSyntax "sealed file static class T { }\n" PrinterOptions.Default)
                "file static sealed class T { }\n"
                "Ending the run at file left the modifiers behind it unsorted."

            Expect.equal
                (printSyntax
                    "class C\n{\n    void M()\n    {\n        var file = 1;\n    }\n}\n"
                    PrinterOptions.Default)
                "class C\n{\n    void M()\n    {\n        var file = 1;\n    }\n}\n"
                "file is contextual: as an identifier it is not a modifier at all."
        }
        test "no synthetic trailing comma stands in front of a directive" {
            let enumWith (directive: string) =
                "enum E\n{\n    A = 1,\n    B = 2\n" + directive + "\n}\n"

            for directive in
                [
                    "#pragma warning restore format"
                    "#pragma warning restore CS0618"
                    "#line 5"
                    "#nullable enable"
                ] do
                Expect.equal
                    (printSyntax (enumWith directive) PrinterOptions.Default)
                    (enumWith directive)
                    $"The member before {directive} keeps no comma."

            Expect.equal
                (printSyntax "enum E\n{\n    A = 1,\n    B = 2\n}\n" PrinterOptions.Default)
                "enum E\n{\n    A = 1,\n    B = 2,\n}\n"
                "Nothing between the member and the brace: the comma is added."

            Expect.equal
                (printSyntax
                    "enum E\n{\n    A = 1,\n    B = 2\n    // tail\n}\n"
                    PrinterOptions.Default)
                "enum E\n{\n    A = 1,\n    B = 2,\n    // tail\n}\n"
                "A comment is not a directive, and does not hold the comma back."
        }
        test "a global using alias sorts after the global usings that are not aliases" {
            Expect.equal
                (printSyntax
                    "global using Xunit;\nglobal using PInvoke = Windows.Win32.PInvoke;\n"
                    PrinterOptions.Default)
                "global using Xunit;\nglobal using PInvoke = Windows.Win32.PInvoke;\n"
                "An alias goes last however its name sorts."

            Expect.equal
                (printSyntax
                    "global using Zebra;\nglobal using Z = N.Z;\nglobal using static N.SZ;\nglobal using Alpha;\nglobal using A = N.A;\nglobal using static N.SA;\nglobal using System.Text;\n"
                    PrinterOptions.Default)
                "global using System.Text;\nglobal using Alpha;\nglobal using static N.SA;\nglobal using static N.SZ;\nglobal using Zebra;\nglobal using A = N.A;\nglobal using Z = N.Z;\n"
                "System first, then the non-aliases by name, then the aliases by name."

            Expect.equal
                (printSyntax
                    "global using Zebra;\nglobal using static N.SA;\n"
                    PrinterOptions.Default)
                "global using static N.SA;\nglobal using Zebra;\n"
                "A global static sorts in among the plain globals by its name."

            Expect.equal
                (printSyntax
                    "using Zebra;\nusing static N.SA;\nclass C { }\n"
                    PrinterOptions.Default)
                "using Zebra;\nusing static N.SA;\n\nclass C { }\n"
                "An ordinary static still follows every plain ordinary using."

            Expect.equal
                (printSyntax
                    "using Zebra;\nusing B = N.B;\nusing Alpha;\nusing A = N.A;\nclass C { }\n"
                    PrinterOptions.Default)
                "using Alpha;\nusing Zebra;\nusing A = N.A;\nusing B = N.B;\n\nclass C { }\n"
                "The ordinary plain/alias split is unchanged by the renumbering."
        }
        test "a run holding both file and partial keeps its source order" {
            Expect.equal
                (printSyntax "partial file class T { }\n" PrinterOptions.Default)
                "partial file class T { }\n"
                "Sorting this would make it compile, which is a different program."

            Expect.equal
                (printSyntax "sealed file partial class T { }\n" PrinterOptions.Default)
                "sealed file partial class T { }\n"
                "The whole run stands still, so nothing is left for the verifier to refuse."

            Expect.equal
                (printSyntax "file partial sealed class T { }\n" PrinterOptions.Default)
                "file partial sealed class T { }\n"
                "Already fronted by file, and still not sorted: partial pins the run."
        }
        test "no comma is added before a directive that carries its own separator" {
            let source =
                "class C\n{\n    int[] a = new int[]\n    {\n        1\n#if A\n        , 2\n#endif\n    };\n}\n"

            let expected =
                "class C\n{\n    int[] a = new int[]\n    {\n        1\n#if A\n        ,\n        2\n#endif\n    };\n}\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "A doubled separator would not parse when A is defined."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "an identifier spelled with a unicode escape keeps its separating space" {
            Expect.equal
                (printSyntax "class \\u0043 { }\n" PrinterOptions.Default)
                "class \\u0043 { }\n"
                "Merging the keyword and the name changes the program."

            Expect.equal
                (printSyntax "class C\n{\n    void M(int \\u0078) { }\n}\n" PrinterOptions.Default)
                "class C\n{\n    void M(int \\u0078) { }\n}\n"
                "A parameter name is an identifier whatever spells it."
        }
        test "a do statement accepts any embedded statement as its body" {
            Expect.equal
                (printSyntax
                    "class C\n{\n    void M()\n    {\n        do ;\n        while (false);\n    }\n}\n"
                    PrinterOptions.Default)
                "class C\n{\n    void M()\n    {\n        do ;\n        while (false);\n    }\n}\n"
                "An empty statement body held one child and Block read three."

            Expect.equal
                (printSyntax
                    "class C\n{\n    void M(int x)\n    {\n        do x++;\n        while (false);\n    }\n}\n"
                    PrinterOptions.Default)
                "class C\n{\n    void M(int x)\n    {\n        do x++;\n        while (false);\n    }\n}\n"
                "An expression body stays on the do's line."
        }
        test "a singly ignored node keeps its trailing comment" {
            let source = "class C\n{\n    // csff-ignore\n    int    A; // keep\n}\n"
            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "The comment is part of what the marker preserves."
        }
        test "an ignore marker accepts an explanation suffix" {
            let source =
                "class C\n{\n    void M()\n    {\n        // csff-ignore-start\n        X(   1 );\n        // csff-ignore-end - alignment\n        Y(   2 );\n    }\n}\n"

            let expected =
                "class C\n{\n    void M()\n    {\n        // csff-ignore-start\n        X(   1 );\n        // csff-ignore-end - alignment\n        Y(2);\n    }\n}\n"

            Expect.equal
                (printSyntax source PrinterOptions.Default)
                expected
                "A suffixed end marker still closes its range."

            let single = "class C\n{\n    // csff-ignore - spacing\n    int    A;\n}\n"

            Expect.equal
                (printSyntax single PrinterOptions.Default)
                single
                "A suffixed single marker still ignores its node."
        }
        test "a single ignore covers an attributed field whole" {
            let field = "class C\n{\n    // csff-ignore\n    [My]\n    int    A;\n}\n"

            Expect.equal
                (printSyntax field PrinterOptions.Default)
                field
                "Only method-like declarations keep their attributes outside the ignore."

            let method = "class C\n{\n    // csff-ignore\n    [My]\n    void    M() { }\n}\n"

            Expect.equal
                (printSyntax method PrinterOptions.Default)
                "class C\n{\n    // csff-ignore\n    [My]\n    void M() { }\n}\n"
                "A method-like declaration keeps its attribute exemption and formats."
        }
        test "an ignored node's trailing comment keeps its own line break" {
            let source =
                "class C\n{\n    void M(int a, int b)\n    {\n        F(\n            // csff-ignore\n            a // keep\n            , b);\n    }\n}\n"

            let expected =
                "class C\n{\n    void M(int a, int b)\n    {\n        F(\n            // csff-ignore\n            a // keep\n            ,\n            b\n        );\n    }\n}\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The comma survives outside the comment."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a range whose end marker is swallowed runs to the scope's close" {
            let source =
                "class C\n{\n    void M()\n    {\n        // csff-ignore-start\n        X(   1 );\n        {\n            Y(   2 );\n        // csff-ignore-end\n            Z(   3 );\n        }\n        W(   4 );\n    }\n    void N()\n    {\n        Q(   5 );\n    }\n}\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains actual "        W(   4 );" "The scope stays as written."
            Expect.stringContains actual "Q(5);" "Formatting resumes after the scope."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."

            let marked =
                source.Replace(
                    "        {\n            Y",
                    "        // csff-ignore\n        {\n            Y"
                )

            let actualMarked = printSyntax marked PrinterOptions.Default
            Expect.stringContains actualMarked "            Z(   3 );" "The block stays whole."

            Expect.equal
                (printSyntax actualMarked PrinterOptions.Default)
                actualMarked
                "Idempotent."
        }
        test "a masked trailing comment is not copied into the ignored span" {
            let source =
                "class C\n{\n    int[] a = new int[]\n    {\n        // csff-ignore\n        11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111 /* keep */\n    };\n}\n"

            let expected =
                "class C\n{\n    int[] a = new int[]\n    {\n        // csff-ignore\n        11111111111111111111111111111111111111111111111111111111111111111111111111111111111111111, /* keep */\n    };\n}\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "One comma, one comment."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "an extended range consumes the closing token's trivia" {
            let withComment =
                "class C\n{\n    void M()\n    {\n        // csff-ignore-start\n        X(   1 );\n        {\n            Y(   2 );\n        // csff-ignore-end\n            Z(   3 );\n        }\n        // before close\n    }\n}\n"

            let actual = printSyntax withComment PrinterOptions.Default

            Expect.equal (actual.Split("// before close").Length) 2 "The comment prints once."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."

            let withRegion =
                "class C\n{\n    void M()\n    {\n        #region R\n        // csff-ignore-start\n        X(   1 );\n        {\n            Y(   2 );\n        // csff-ignore-end\n            Z(   3 );\n        }\n        #endregion\n    }\n}\n"

            let balanced = printSyntax withRegion PrinterOptions.Default

            Expect.equal
                (balanced.Split("#endregion").Length)
                2
                "The endregion prints once, so the directives stay balanced."

            Expect.equal (printSyntax balanced PrinterOptions.Default) balanced "Idempotent."
        }
        test "a single ignore inside a range keeps its trailing comment" {
            let source =
                "class C\n{\n    void M()\n    {\n        // csff-ignore-start\n        // csff-ignore\n        F(); // keep\n        // csff-ignore-end\n        G(   2 );\n    }\n}\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.stringContains actual "// keep" "The node's trailing comment is its own."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a suffixed end marker behaves exactly like a bare one among usings" {
            let shape marker =
                "// csff-ignore-start\nusing    Z;\n" + marker + "\nusing A;\nclass C { }\n"

            let bare = printSyntax (shape "// csff-ignore-end") PrinterOptions.Default

            let suffixed =
                printSyntax (shape "// csff-ignore-end - note") PrinterOptions.Default

            Expect.equal
                (suffixed.Replace("// csff-ignore-end - note", "// csff-ignore-end"))
                bare
                "The suffix changes nothing but the marker's own text."
        }
        test "a single ignore covers a namespace or a standalone block" {
            let block =
                "class C\n{\n    void M()\n    {\n        // csff-ignore\n        { X(   1 ); }\n    }\n}\n"

            Expect.equal
                (printSyntax block PrinterOptions.Default)
                block
                "A standalone block is a node like any other to a single marker."

            let space = "// csff-ignore\nnamespace N { class    C { } }\n"

            Expect.equal
                (printSyntax space PrinterOptions.Default)
                space
                "A namespace is a node like any other to a single marker."
        }
        test "an ignored enum member keeps its separator and comment inline" {
            let source =
                "enum E\n{\n    // csff-ignore\n    AAAA   =   1, // keep\n    B = 2,\n}\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "The comma's trailing trivia is the member's."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "an ignore range on the first using travels with the sort" {
            let source = "// csff-ignore-start\nusing    Z;\n// csff-ignore-end\nusing A;\n"

            let expected = "using A;\n// csff-ignore-start\nusing    Z;\n// csff-ignore-end\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The marker is not a file header."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a sorted ignored using block arrives without a blank above it" {
            let source =
                "using B;\n// csff-ignore-start\nusing    Z;\n// csff-ignore-end\nusing A;\n"

            let expected =
                "using A;\nusing B;\n// csff-ignore-start\nusing    Z;\n// csff-ignore-end\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The gap follows the block, not the sorted run."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "ignored using gaps retain every blank line" {
            let checker = SyntaxPreservation.Checker()

            for count in [ 0; 1; 2; 3; 8 ] do
                for whitespace in [ ""; " \t  " ] do
                    for eol, endOfLine in
                        [ "\n", EndOfLine.Lf; "\r\n", EndOfLine.CrLf; "\r", EndOfLine.Cr ] do
                        let gap = String.replicate count (whitespace + eol)
                        let opening = "// csff-ignore-start" + eol
                        let body = "using   Z;" + eol + gap
                        let closing = "// csff-ignore-end"
                        let region = opening + body + closing
                        let indentedRegion = "    " + opening + "    " + body + "    " + closing

                        for name, source, protectedText in
                            [
                                "declaration", "using B;" + eol + region + eol + "class C{}", region
                                "end of file", region + eol, region
                                "sorted run", region + eol + "using A;" + eol, region
                                "namespace",
                                "namespace N{"
                                + eol
                                + indentedRegion
                                + eol
                                + "class C{}"
                                + eol
                                + "}",
                                indentedRegion
                                "conditional",
                                "#if X" + eol + region + eol + "#endif" + eol + "class C{}",
                                region
                                "unfinished range",
                                opening + body + "using   Y;" + eol + "class C{}",
                                opening + body + "using   Y;"
                            ] do
                            let options =
                                { PrinterOptions.Default with
                                    EndOfLine = endOfLine
                                }

                            let actual = printSyntax source options

                            let context =
                                $"{name}, {count} blanks, whitespace {whitespace.Length}, {endOfLine}"

                            Expect.stringContains actual protectedText context

                            Expect.equal
                                (printSyntax actual options)
                                actual
                                (context + ": idempotent")

                            Expect.equal
                                (checker.Check(options, "ignored-gaps.cs", source, actual))
                                (Ok())
                                context
        }
        test "ignored using gaps print each blank line once" {
            let checker = SyntaxPreservation.Checker()

            for name, source, expected in
                [
                    "documentation comment",
                    "// csff-ignore-start\nusing Z;\n/// doc\n\n// csff-ignore-end\nclass C { }\n",
                    "// csff-ignore-start\nusing Z;\n/// doc\n\n// csff-ignore-end\nclass C { }\n"
                    "documentation comment, two blanks",
                    "using B;\n// csff-ignore-start\nusing Z;\n/// doc\n\n\n// csff-ignore-end\nclass C { }\n",
                    "using B;\n// csff-ignore-start\nusing Z;\n/// doc\n\n\n// csff-ignore-end\nclass C { }\n"
                    "held-back marker",
                    "namespace N;\n// csff-ignore-start\nusing Z;\n\n// inner\n\n// csff-ignore-end\nusing A;\n",
                    "namespace N;\n\n// inner\nusing A;\n// csff-ignore-start\nusing Z;\n\n// csff-ignore-end\n"
                ] do
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected name

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    (name + ": idempotent")

                Expect.equal
                    (checker.Check(PrinterOptions.Default, "ignored-gaps.cs", source, actual))
                    (Ok())
                    name
        }
        test "other ignored gaps keep the protected layout" {
            let checker = SyntaxPreservation.Checker()
            let header = "// csff-ignore-start\n// csff-ignore-end\n"

            for name, source, expected in
                [
                    "trivia-only range",
                    "using B;\n// csff-ignore-start\n#pragma warning disable CS0168\n\n// csff-ignore-end\nusing A;\n",
                    "using B;\n// csff-ignore-start\n#pragma warning disable CS0168\n\n// csff-ignore-end\nusing A;\n"
                    "trivia-only range, two blanks",
                    "using B;\n// csff-ignore-start\n#pragma warning disable CS0168\n\n\n// csff-ignore-end\nusing A;\n",
                    "using B;\n// csff-ignore-start\n#pragma warning disable CS0168\n\n// csff-ignore-end\nusing A;\n"
                    "trivia-only range, blanks outside",
                    "using B;\n\n\n// csff-ignore-start\n#pragma warning disable CS0168\n\n// csff-ignore-end\nusing A;\n",
                    "using B;\n\n// csff-ignore-start\n#pragma warning disable CS0168\n\n// csff-ignore-end\nusing A;\n"
                    "trailing start marker",
                    "using B; // csff-ignore-start\n#pragma warning disable CS0168\n\n\n// csff-ignore-end\nusing A;\n",
                    "using B; // csff-ignore-start\n#pragma warning disable CS0168\n\n// csff-ignore-end\nusing A;\n"
                    "header marker",
                    header + "using B;\n// csff-ignore-start\nusing A;\n// csff-ignore-end\n",
                    header + "using B;\n// csff-ignore-start\nusing A;\n\n// csff-ignore-end\n"
                    "header marker, two blanks",
                    header + "using B;\n// csff-ignore-start\nusing A;\n\n\n// csff-ignore-end\n",
                    header + "using B;\n// csff-ignore-start\nusing A;\n\n// csff-ignore-end\n"
                    "header marker, held-back marker",
                    header
                    + "using B;\n// csff-ignore-start\nusing Z;\n\n// csff-ignore-end\nusing A;\n",
                    header
                    + "\nusing A;\nusing B;\n// csff-ignore-start\nusing Z;\n\n// csff-ignore-end\n"
                    "range after a held-back marker",
                    "// csff-ignore-start\nusing Z;\n// csff-ignore-end\nusing A;\n"
                    + "// csff-ignore-start\n\n\n// csff-ignore-end\nclass C { }\n",
                    "using A;\n// csff-ignore-start\nusing Z;\n// csff-ignore-end\n\n"
                    + "// csff-ignore-start\n\n// csff-ignore-end\nclass C { }\n"
                    "ignored using after a held-back marker",
                    "// csff-ignore-start\nusing Z;\n// csff-ignore-end\nusing A;\n"
                    + "// csff-ignore-start\nusing Y;\n\n\n// csff-ignore-end\nclass C { }\n",
                    "using A;\n// csff-ignore-start\nusing Z;\n// csff-ignore-start\nusing Y;\n"
                    + "// csff-ignore-end\n\n// csff-ignore-end\nclass C { }\n"
                    "extern alias header",
                    "extern alias E;\nusing A;\n// csff-ignore-start\nusing B;\n\n// csff-ignore-end\n"
                    + "// csff-ignore-start\nusing C;\n// csff-ignore-end\n",
                    "extern alias E;\nusing A;\n\n// csff-ignore-start\nusing C;\n\n"
                    + "// csff-ignore-start\nusing B;\n\n// csff-ignore-end\n// csff-ignore-end\n"
                    "initializer element",
                    "class C\n{\n    int[] a =\n    {\n        // csff-ignore-start\n        1,\n\n\n"
                    + "#pragma warning disable CS0168\n        // csff-ignore-end\n        2,\n    };\n}\n",
                    "class C\n{\n    int[] a =\n    {\n        // csff-ignore-start\n        1,\n\n"
                    + "#pragma warning disable CS0168\n        // csff-ignore-end\n        2,\n    };\n}\n"
                ] do
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected name

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    (name + ": idempotent")

                Expect.equal
                    (checker.Check(PrinterOptions.Default, "ignored-gaps.cs", source, actual))
                    (Ok())
                    name
        }
        test "a comment above an ignored first using moves with its block" {
            let source =
                "// a license\n// csff-ignore-start\nusing    Z;\n// csff-ignore-end\nusing A;\n"

            let expected =
                "using A;\n// a license\n// csff-ignore-start\nusing    Z;\n// csff-ignore-end\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The whole leading run belongs to the ignored using."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
    ]

let private bareSwitchBodyFixtures =
    [
        test "a switch body holding bare statements is a fixed point" {
            let expected =
                "class C\n{\n    void M(int x)\n    {\n        switch (x)\n        {\n\n"
                + "            Work();\n        }\n    }\n}\n"

            let actual =
                printSyntax
                    "class C\n{\n    void M(int x)\n    {\n        switch (x)\n        {\n            Work();\n        }\n    }\n}\n"
                    PrinterOptions.Default

            Expect.equal actual expected "One blank line follows the opening brace."

            for body in
                [
                    "Work();"
                    "Work();\n            Done();"
                    "Work();\n            case 1:\n                break;"
                    "int y = 0;"
                ] do
                let source =
                    "class C\n{\n    void M(int x)\n    {\n        switch (x)\n        {\n            "
                    + body
                    + "\n        }\n    }\n}\n"

                let once = printSyntax source PrinterOptions.Default
                Expect.equal (printSyntax once PrinterOptions.Default) once source
        }
    ]

let private conditionalBatchFixtures =
    [
        test "independent empty conditional regions bound whole-file passes" {
            use builder = new SyntaxDocumentBuilder()
            use document = new DocumentBuffer()
            let tree = SyntaxTree()
            let mutable smallestVolume = 0L

            for count in [ 8; 16; 32; 64 ] do
                let source =
                    String.concat
                        ""
                        [ for i in 0 .. count - 1 -> $"#if S{i}\nclass C{i}{{}}\n#endif\n" ]

                Parser.parse source tree
                document.Reset()
                builder.Build(source, tree, document, PrinterOptions.Default)
                let struct (sets, parses, renders, parsed, rendered) = builder.ConditionalWork

                printfn
                    "conditional work: S=%d sets=%d parses=%d renders=%d parsed=%d rendered=%d"
                    count
                    sets
                    parses
                    renders
                    parsed
                    rendered

                Expect.equal sets count "Witness selection still reaches every independent region."

                Expect.equal
                    parses
                    2
                    "The proven-independent branches share the even and odd reparses."

                Expect.equal
                    renders
                    3
                    "Only the default, even and odd whole-file renders are needed."

                Expect.isLessThan
                    parsed
                    (3L * int64 source.Length)
                    "The defines plus formatted file are linear source volume."

                Expect.equal rendered (parsed + int64 source.Length) "Count both full renders."

                if count = 8 then
                    smallestVolume <- parsed
                elif count = 64 then
                    Expect.isLessThan
                        parsed
                        (12L * smallestVolume)
                        "Eight times as many regions stays linear."

                for _, options in OutputConfigurations.all do
                    let actual = printSyntax source options

                    Expect.equal
                        actual
                        (printSequentialSyntax source options)
                        "Batching preserves every output byte."

                    Expect.equal
                        (printSyntax actual options)
                        actual
                        "The combined pass is idempotent."

            Parser.parse "class C{}" tree
            document.Reset()
            builder.Build("class C{}", tree, document, PrinterOptions.Default)

            Expect.equal
                builder.ConditionalWork
                (struct (0, 0, 0, 0L, 0L))
                "Work counters reset between files."
        }
        test "conditional batching preserves trivia boundaries and falls back conservatively" {
            let eligible =
                [
                    "#if A\nclass X{}\n#endif\n\n#if B\nclass Y{}\n#endif\n"
                    "\n  #if A\n class X {\n }\n #endif\n  #if B\nclass Y{}\n#endif"
                    "#if A\r\nclass LongClassName{}\r\n#endif\r\n#if B\r\nclass Y{}\r\n#endif\r\n"
                    "#if A\\u0042\nclass @class{}\n#endif\n#if C\nclass Y{}\n#endif\n"
                ]

            let fallback =
                [
                    "#if A\nclass X{}\n#endif\n#if A\nclass Y{}\n#endif\n"
                    "#if A\n#if B\nclass X{}\n#endif\n#endif\n#if C\nclass Y{}\n#endif\n"
                    "#if A\nclass X{}\n#elif B\nclass Y{}\n#else\nclass Z{}\n#endif\n"
                    "#if A||B\nclass X{}\n#endif\n#if C\nclass Y{}\n#endif\n"
                    "#if (A != B) C\nclass X{}\n#endif\n#if A\nclass Y{}\n#endif\n#if B\nclass Z{}\n#endif\n"
                    "#define A\n#if A\nclass X{}\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A\n#undef B\nclass X{}\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A\nusing Z;\nusing A;\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A // keep\nclass X{}\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A\n// lead\nclass X{} /* tail */\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A\n/*\n#undef B\n*/\nclass X{}\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A\nclass X{void M(){Call(1,2);}}\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A\nclass X{\n#endif\n#if B\n}\n#endif\n"
                    "class Active{}\n#if A\nclass X{}\n#endif\n#if B\nclass Y{}\n#endif\n"
                    "#if A\nclass X{}\n#endif // end\n#if B\nclass Y{}\n#endif\n"
                    "#if A\nclass X{}\n#endif\n// between\n#if B\nclass Y{}\n#endif\n"
                    for newline in [ "\u0085"; "\u2028"; "\u2029" ] do
                        String.concat
                            newline
                            [ "#if A"; "class X{}"; "#endif"; "#if B"; "class Y{}"; "#endif"; "" ]
                ]

            use builder = new SyntaxDocumentBuilder()
            use document = new DocumentBuffer()
            let tree = SyntaxTree()

            for batch, sources in [ true, eligible; false, fallback ] do
                for source in sources do
                    for _, options in
                        OutputConfigurations.all
                        @ [
                            "CRLF",
                            { PrinterOptions.Default with
                                EndOfLine = EndOfLine.CrLf
                            }
                        ] do
                        Parser.parse source tree
                        document.Reset()
                        builder.Build(source, tree, document, options)
                        let struct (sets, parses, _, _, _) = builder.ConditionalWork

                        if not (source.Contains("class X{\n", StringComparison.Ordinal)) then
                            Expect.equal
                                parses
                                (if batch then min sets 2 else sets)
                                "Unproven files keep the original schedule."

                        let actual = printSyntax source options

                        Expect.equal
                            actual
                            (printSequentialSyntax source options)
                            "The sequential schedule produces identical bytes."

                        if not (source.Contains("class X{\n", StringComparison.Ordinal)) then
                            Expect.equal
                                (printSyntax actual options)
                                actual
                                "Conditional layouts stay idempotent."
        }
    ]

let private conditionalArenaOrder =
    [
        test "interning a repeated condition keeps a usable witness" {
            let source =
                "#if !(B||C)\nclass Ok{}\n#endif\n"
                + "#if (A||B)&&(B||C)\nclass Target{}\n#endif\n"
                + "#if A&&C\nclass Broken{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "Code a usable configuration makes reachable is formatted."
        }
    ]

let private conditionalWitnessRetry =
    [
        test "a rejected configuration is replaced by another witness of the same branch" {
            let source =
                "#if C&&(A||B)\nclass Target{}\n#endif\n#if A&&C\nclass Broken{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "A rejected configuration is replaced, not treated as final."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a retry steps past several broken regions" {
            let source =
                "#if (A||B)||C\nclass Target{}\n#endif\n"
                + "#if A\nclass BrokenA{\n#endif\n"
                + "#if B\nclass BrokenB{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "Selection walks past every broken branch that can be avoided."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "an else branch holding broken code is avoided through its chain" {
            let source =
                "#if C&&(A||B)\nclass Target{}\n#endif\n#if !A\n#else\nclass Broken{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "An else branch is avoided by taking one of the branches before it."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a delimiter closing a comment in one configuration opens one in another" {
            let source =
                "#define X\n#if A\n/*\n#elif B\n/*/\n#if C\nclass Target{}\n#endif\n#endif\n"
                + "#if !A && B\n*/\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "The configuration that reaches Target is the one where its guard is a directive."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a broken branch nested in another region is avoided whole" {
            let source =
                "#if C&&(A||B)\nclass Target{}\n#endif\n#if A\n#if true\nclass Broken{\n#endif\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "An avoided branch carries its enclosing conditions."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a failure that completes by borrowing does not drive the reselection" {
            let source =
                "#if P\nclass Header\n#endif\n#if X\n{\n}\n#endif\n"
                + "#if P&&(A||B)\nclass Target{}\n#endif\n#if A\nclass Broken{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "Only a branch still failing at the stall is avoided."
        }
        test "an avoided condition is read at its own position among the defines" {
            let source =
                "#undef TARGET\n#if A||B\n#define TARGET\n#endif\n#if A\nclass Broken{\n#endif\n"
                + "#undef A\n#if TARGET\nclass Target{}\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "The branch condition is the one its position establishes."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a break is located at its own construct past following code" {
            let source =
                "#if C&&(A||B)\nclass Target{}\n#endif\n#if A&&C\nclass Broken{\n#endif\nclass Other{}\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "The break belongs to the construct that opened it."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a warning directive's argument opens no comment in a gap scan" {
            for head in [ "#warning /*"; "#pragma warning disable /* x" ] do
                let source = "#if false\n/*\n#endif\n" + head + "\n#if A\nclass Target{}\n#endif\n"

                let actual = printSyntax source PrinterOptions.Default

                Expect.stringContains
                    actual
                    "class Target { }"
                    "A directive line's text is not lexical state."

                Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "branch ordinals survive a directive hidden inside an active comment" {
            let source =
                "#if C\n/*\n#if H\n#endif\n*/\n#endif\n"
                + "#if C&&(A||B)\nclass Target{}\n#endif\n#if A&&C\nclass Broken{\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "The avoided branch is the one that broke, in every numbering."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a break in a declaration that starts outside its branch is still located" {
            let source =
                "#if C&&(A||B)\nclass Target{}\n#endif\n"
                + "class Other{\nint x\n#if A&&C\n=1\n#else\n;\n#endif\n}\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "class Target { }"
                "The fallback position identifies the failing branch."
        }
        test "directive lines are read as the lexer reads them" {
            let shapes =
                [ "\f#if Z\nclass Ahead{}\n#endif\n"; "/**doc*/#if Z\nclass Ahead{}\n#endif\n" ]
                |> List.map (fun prefix ->
                    prefix
                    + "#if C&&(A||B)\nclass Target{}\n#endif\n#if A&&C\nclass Broken{\n#endif\n")

            let commented =
                "#if C&&(A||B)\nclass Target{}\n#endif\n"
                + "#if A&&C\n/*\n#elif H\n*/\nclass Broken{\n#endif\n"

            for source in commented :: shapes do
                let actual = printSyntax source PrinterOptions.Default

                Expect.stringContains
                    actual
                    "class Target { }"
                    ("The avoided branch is the broken one.\n" + source)
        }
        test "a branch with no usable witness keeps its text as written" {
            let source = "#if A\nclass Broken{\n#endif\nclass Ok { }\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains actual "class Broken{" "Unreachable repair keeps the text."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
    ]

let private conditionalSkippedText =
    let broken = "#if COND\nthis is not C# at all ((\n#endif\n"

    let placements =
        [
            ("initializer, branch before the list",
             "class C\n{\n    public const int Field =\n"
             + broken
             + "        [1, value];\n}\n")
            ("local, branch before the list",
             "class C\n{\n    int M(int value)\n    {\n        var local =\n"
             + broken
             + "            [1, value];\n        return 0;\n    }\n}\n")
            ("nested type, branch before the list",
             "class Outer\n{\n    class C\n    {\n        public const int Field =\n"
             + broken
             + "            [1, value];\n    }\n}\n")
            ("two adjacent broken branches",
             "class C\n{\n    public const int Field =\n"
             + broken
             + broken
             + "        [1, value];\n}\n")
            ("branch after the list",
             "class C\n{\n    public const int Field = [1, value];\n" + broken + "}\n")
            ("branch at end of file",
             "class C\n{\n    public const int Field = [1, value];\n}\n" + broken)
            ("branch inside the argument list",
             "class C\n{\n    int M(int value)\n    {\n        return Compute(\n"
             + broken
             + "            [1, value]);\n    }\n}\n")
        ]

    let widths = 100 :: [ 16..64 ]

    [
        for label, source in placements do
            test $"an unreadable branch keeps its text and its neighbour's tokens / {label}" {
                let checker = TokenPreservation.Checker()

                for width in widths do
                    let options =
                        { PrinterOptions.Default with
                            Width = width
                        }

                    let actual = printSyntax source options

                    Expect.stringContains
                        actual
                        "\nthis is not C# at all ((\n"
                        $"The unreadable branch keeps its own line at width {width}.\n{actual}"

                    match checker.Check(options, "skipped.cs", source, actual) with
                    | Ok() -> ()
                    | Error message -> failtest $"width {width}: {message}\n{actual}"

                    Expect.equal
                        (printSyntax actual options)
                        actual
                        $"Idempotent at width {width}.\n{actual}"
            }
        test "a branch the lexer can read is still formatted" {
            let source = "class C\n{\n#if COND\n    int  x  =  1;\n#endif\n    int y = 2;\n}\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "    int x = 1;\n"
                $"A readable branch is formatted by its configuration.\n{actual}"

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a skipped run the file already carries blocks no configuration" {
            let source =
                "class C\n{\n    int M() { return 1; } #\n#if COND\n    int  x  =  1;\n#endif\n}\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                "    int x = 1;\n"
                $"A file-level skipped run does not reject a branch.\n{actual}"

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
    ]

let private triviaBlankLines =
    let blankLines (text: string) =
        text.TrimEnd('\n').Split('\n')
        |> Array.filter (fun line -> line.Trim() = "")
        |> Array.length

    let widths = 100 :: [ 16..64 ]

    let holds label source expectedBlanks =
        test $"a blank line inside a construct holds its own line / {label}" {
            let checker = TokenPreservation.Checker()

            for width in widths do
                let options =
                    { PrinterOptions.Default with
                        Width = width
                    }

                let actual = printSyntax source options

                match checker.Check(options, "trivia-blank.cs", source, actual) with
                | Ok() -> ()
                | Error message -> failtest $"width {width}: {message}\n{actual}"

                Expect.equal
                    (printSyntax actual options)
                    actual
                    $"Idempotent at width {width}.\n{actual}"

                Expect.equal
                    (blankLines actual)
                    expectedBlanks
                    $"Blank lines at width {width}.\n{actual}"
        }

    [
        holds
            "blank before a region inside a binary expression"
            "class C\n{\n    int M(int value)\n    {\n        return value +\n\n#region Marker\n#endregion\n            1;\n    }\n}\n"
            1
        holds
            "blank before a comment inside a stackalloc bracket"
            "class C\n{\n    void M(int value)\n    {\n        var span = stackalloc int[\n\n// comment\n            1];\n    }\n}\n"
            1
        holds
            "blank before a comment after return"
            "class C\n{\n    string M(int value)\n    {\n        return\n\n//\n            $\"before {value} after\" + 1;\n    }\n}\n"
            1
        holds
            "blank before a region after a member access dot"
            "class C\n{\n    int M(int value)\n    {\n        return Holder.\n\n#region Marker\n#endregion\n            First + 1 + value;\n    }\n}\n"
            1
        holds
            "two blanks before a region collapse to one"
            "class C\n{\n    int M(int value)\n    {\n        return value +\n\n\n#region Marker\n#endregion\n            1;\n    }\n}\n"
            1
        holds
            "a blank before each of two adjacent regions"
            "class C\n{\n    int M(int value)\n    {\n        return value +\n\n#region One\n#endregion\n\n#region Two\n#endregion\n            1;\n    }\n}\n"
            2
        holds
            "a blank inside a construct nested two deep"
            "class Outer\n{\n    class C\n    {\n        int M(int value)\n        {\n            return Compute(value +\n\n// comment\n                1);\n        }\n    }\n}\n"
            1
        for label, source in
            [
                ("const initializer",
                 "class C\n{\n    public const int Field =\n// comment\n\n        Holder.First;\n}\n")
                ("field initializer",
                 "class C\n{\n    public int field =\n//\n\n        Holder.First;\n}\n")
                ("property initializer",
                 "class C\n{\n    public int Value { get; } =\n/// <summary>text</summary>\n\n        Holder.First;\n}\n")
                ("local initializer",
                 "class C\n{\n    int M(int value)\n    {\n        var local =\n/// <summary>text</summary>\n\n            Holder.First;\n        return 0;\n    }\n}\n")
            ] do
            test $"a flattened scope drops a blank line rather than spending it / {label}" {
                let checker = TokenPreservation.Checker()

                for width in widths do
                    let options =
                        { PrinterOptions.Default with
                            Width = width
                        }

                    let actual = printSyntax source options

                    match checker.Check(options, "flat-blank.cs", source, actual) with
                    | Ok() -> ()
                    | Error message -> failtest $"width {width}: {message}\n{actual}"

                    Expect.equal
                        (printSyntax actual options)
                        actual
                        $"Idempotent at width {width}.\n{actual}"

                    for line in actual.Split('\n') do
                        if line.Contains "Holder.First" then
                            Expect.equal
                                (line.Length - line.TrimStart().Length)
                                (actual.Split('\n')
                                 |> Array.find (fun l -> l.Contains "//")
                                 |> fun l -> l.Length - l.TrimStart().Length)
                                $"The chain sits at the comment's column at width {width}.\n{actual}"
            }
        for label, head, body in
            [
                ("method body", "#pragma warning disable 219", "        var a = 1;\n")
                ("switch body", "#pragma warning disable 1591", "            1 => x,\n")
                ("class body", "#pragma warning disable 219", "    int f = 1;\n")
                ("comment at the head of a method body", "// note", "        var a = 1;\n")
                ("region at the head of a method body",
                 "#region Marker\n#endregion",
                 "        var a = 1;\n")
            ] do
            test $"both spellings of a blank line after head trivia agree / {label}" {
                let checker = TokenPreservation.Checker()

                let wrap gap =
                    match label with
                    | "switch body" ->
                        "class C\n{\n    int M(int x)\n    {\n        return x switch\n        {\n"
                        + head
                        + "\n"
                        + gap
                        + body
                        + "            _ => 0,\n        };\n    }\n}\n"
                    | "class body" -> "class C\n{\n" + head + "\n" + gap + body + "}\n"
                    | _ ->
                        "class C\n{\n    void M()\n    {\n"
                        + head
                        + "\n"
                        + gap
                        + body
                        + "    }\n}\n"

                let spellings = [ "\n"; "    \n"; "\t\n" ]

                for width in 100 :: [ 16..64 ] do
                    let options =
                        { PrinterOptions.Default with
                            Width = width
                        }

                    let outputs =
                        [
                            for gap in spellings do
                                let source = wrap gap
                                let actual = printSyntax source options

                                match checker.Check(options, "head-blank.cs", source, actual) with
                                | Ok() -> ()
                                | Error message -> failtest $"width {width}: {message}\n{actual}"

                                Expect.equal
                                    (printSyntax actual options)
                                    actual
                                    $"Idempotent at width {width}.\n{actual}"

                                yield actual
                        ]

                    Expect.equal
                        (List.distinct outputs).Length
                        1
                        $"Every spelling of the blank line prints the same at width {width}.\n{outputs}"

                    Expect.equal
                        (blankLines (List.head outputs))
                        1
                        $"The blank line after the head trivia survives at width {width}.\n{List.head outputs}"
            }
        test "a blank line directly after an opening brace is still dropped" {
            for gap in [ "\n"; "    \n"; "\t\n"; "\n\n" ] do
                let source =
                    "class C\n{\n    void M()\n    {\n" + gap + "        var a = 1;\n    }\n}\n"

                let actual = printSyntax source PrinterOptions.Default

                Expect.equal
                    actual
                    "class C\n{\n    void M()\n    {\n        var a = 1;\n    }\n}\n"
                    $"A blank after the brace is dropped.\n{actual}"

                Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
        test "a blank line after an accessor brace still expands the accessor" {
            let source = "class C{int P{get{\n\nreturn 1;}}}"

            let actual = printSyntax source PrinterOptions.Default

            Expect.equal
                actual
                "class C\n{\n    int P\n    {\n        get\n        {\n\n            return 1;\n        }\n    }\n}\n"
                "The accessor expands and keeps its blank line."

            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Idempotent."
        }
    ]

let private leadingCommentFit =
    [
        test "a leading comment on its own line spends none of the group's width" {
            let source =
                "class C\n{\n    void M()\n    {\n"
                + "        // ExperimentalAttribute.DiagnosticId is the first (required) constructor argument.\n"
                + "        // Only identifiers are safe to emit into #pragma warning disable directives.\n"
                + "        (experimentalIds ??= new(StringComparer.Ordinal)).Add(diagnosticId);\n"
                + "    }\n}\n"

            let printed = printSyntax source PrinterOptions.Default

            Expect.stringContains
                printed
                "        (experimentalIds ??= new(StringComparer.Ordinal)).Add(diagnosticId);\n"
                "A statement that fits stays on one line."
        }
        test "a leading comment before a group spends its own width" {
            let shapes =
                [
                    "/*p*/{PropertyName:value}pattern"
                    "/*p*//*p*/{PropertyName:value}pattern"
                    "/*longer comment*/{PropertyName:value}pattern"
                ]

            for shape in shapes do
                let source =
                    "class C\n{\n    void M()\n    {\n        if (x is//p\n/*p*/\n"
                    + shape
                    + "&&x) { }\n    }\n}\n"

                for width = 40 to 64 do
                    let options =
                        { PrinterOptions.Default with
                            Width = width
                        }

                    let printed = printSyntax source options

                    for line in printed.Split('\n') do
                        let measured = PrintedWidth.measure (line.AsSpan()) |> int

                        if measured > width then
                            failtestf
                                "At width %d a %d-column line was printed: %s"
                                width
                                measured
                                line

                    Expect.equal (printSyntax printed options) printed "Idempotent."
        }
    ]

let private preservationRegressions =
    [
        test "adjacent property pattern comments remain idempotent near the width limit" {
            for comments in
                [
                    "/*p*/"
                    "/*p*//*p*/"
                    "/*p*/\n/*p*/"
                    "/*p*/\n/*p*//*p*/"
                    "/*p*//*p*//*p*/"
                    "/*longer comment*/"
                ] do
                for width in 30..50 do
                    let source = "if(x is//p\n" + comments + "{PropertyName:value}pattern&&x){}"

                    let options =
                        { PrinterOptions.Default with
                            Width = width
                        }

                    let actual = printSyntax source options

                    Expect.equal
                        (printSyntax actual options)
                        actual
                        ($"Adjacent leading comments must retain their layout at width {width}.")

                    TokenPreservation
                        .Checker()
                        .Check(options, "adjacent-pattern-comments.cs", source, actual)
                    |> function
                        | Ok() -> ()
                        | Error error -> failtest error
        }
        test "leading block comments retain first-line fit status" {
            let source = "/*p*/12"

            expect source 100 "/*p*/\n/*p*/1 2\n" (fun d ->
                group d (fun () ->
                    d.AddComment(source, 0, 5, true, true)
                    d.AddLine(LineKind.Hard, ElementFlags.SkipBreakIfFirst)
                    d.AddComment(source, 0, 5, true, true)
                    text d source "1"
                    d.AddLine(LineKind.Normal)
                    text d source "2")
                |> ignore)
        }
        test "leading block comment fit preserves explicit document boundaries" {
            let source = "/*p*/123"

            expect source 100 "/*p*/1\n2\n" (fun d ->
                group d (fun () ->
                    d.AddToken StaticToken.Space
                    d.AddComment(source, 0, 5, true, true)
                    text d source "1"
                    d.AddLine LineKind.Normal
                    text d source "2")
                |> ignore)

            expect source 100 "1\n/*p*/2\n3\n" (fun d ->
                group d (fun () ->
                    text d source "1"
                    d.AddComment(source, 0, 5, true, true)
                    text d source "2"
                    d.AddLine LineKind.Normal
                    text d source "3")
                |> ignore)
        }
        test "property initializer leading comments remain idempotent" {
            for count in [ 1; 2; 9 ] do
                let source = "class C{int P{get;}// p\n" + String.replicate count "/*p*/" + "=1;}"

                let options =
                    { PrinterOptions.Default with
                        Width = 200
                    }

                let actual = printSyntax source options

                let expected =
                    "class C\n{\n    int P { get; } // p\n"
                    + String.replicate (count - 1) "    /*p*/\n"
                    + "    /*p*/= 1;\n}\n"

                Expect.equal actual expected "Preserve the baseline initializer comment layout."

                Expect.equal
                    (printSyntax actual options)
                    actual
                    "Reparsed initializer stays unchanged."

                TokenPreservation.Checker().Check(options, "property-comments.cs", source, actual)
                |> function
                    | Ok() -> ()
                    | Error error -> failtest error
        }
        test "property pattern leading comments remain idempotent" {
            for count in [ 1; 2; 4; 8 ] do
                let source = "if(x is// p\n" + String.replicate count "/*p*/" + "{x:x}x&&x){}"
                let actual = printSyntax source PrinterOptions.Default

                let expected =
                    "if (\n    x\n        is // p\n"
                    + String.replicate (count - 1) "        /*p*/\n"
                    + "        /*p*/{ x: x } x\n    && x\n) { }\n"

                Expect.equal
                    actual
                    expected
                    "Leading trivia must not falsely reject the flat property pattern."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Reparsed comments retain the same layout."

                TokenPreservation
                    .Checker()
                    .Check(PrinterOptions.Default, "pattern-comments.cs", source, actual)
                |> function
                    | Ok() -> ()
                    | Error error -> failtest error
        }
        test "a keyword keeps its space whatever follows it" {
            for source, expected in
                [
                    "class C{delegate (int A,int B) D();}", "delegate (int A, int B) D();"
                    "class C{static void P(params (int A,int B)[] i){}}",
                    "params (int A, int B)[] i"
                    "class C{int N(int x,bool b)=>x switch{1 when !b=>2,_=>0};}", "1 when !b => 2"
                    "class C{int N(int x)=>x switch{2 when (x&1)==0=>3,_=>0};}",
                    "2 when (x & 1) == 0 => 3"
                    "class C{int N(int x,bool b)=>x switch{3 when b=>4,_=>0};}", "3 when b => 4"
                    "class C{int N(object o)=>o switch{string when o is string=>5,_=>0};}",
                    "when o is string => 5"
                ] do
                let actual = printSyntax source PrinterOptions.Default

                Expect.stringContains
                    actual
                    expected
                    "A keyword and what follows it stay separated."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Spacing is idempotent."

            let anonymous =
                printSyntax
                    "class C{void M(){Action<int> a=delegate (int x){};}}"
                    PrinterOptions.Default

            Expect.stringContains anonymous "delegate(int x)" "An anonymous method takes no space."
        }
        test "an argument that breaks before the last one breaks its list" {
            let options = PrinterOptions.Default

            let demanded =
                printSyntax
                    "class C{void M(){Parallel.ForEach(units,new ParallelOptions{MaxDegreeOfParallelism=settings.Jobs,},unit=>Handle(unit));}}"
                    options

            Expect.stringContains
                demanded
                "Parallel.ForEach(\n            units,\n"
                "An initializer before the last argument breaks the list."

            let hug = printSyntax "class C{void M(){Run(items,item=>{Handle(item);});}}" options

            Expect.stringContains hug "Run(items, item =>" "A trailing lambda still hugs."

            let fits =
                printSyntax "class C{void M(){Describe(r with{X=1},s with{X=2});}}" options

            Expect.stringContains
                fits
                "Describe(r with { X = 1 }, s with { X = 2 })"
                "A call that fits is untouched."

            let undecided =
                printSyntax
                    "class C{void M(ParallelQuery<int> query,int count,int seen){Assert.All(query.Select(x=>x>=count/2?(object)x:null).OfType<int>(),x=>Assert.Equal(seen++,x));}}"
                    options

            Expect.stringContains
                undecided
                "Assert.All(query.Select(x => x >= count / 2 ? (object)x : null).OfType<int>(), x =>"
                "An undecided alternative is not a demand."

            for source in
                [
                    "class C{void M(){Parallel.ForEach(units,new ParallelOptions{MaxDegreeOfParallelism=settings.Jobs,},unit=>Handle(unit));}}"
                    "class C{void M(){Run(items,item=>{Handle(item);});}}"
                    "class C{void M(){Describe(r with{X=1},s with{X=2});}}"
                ] do
                let actual = printSyntax source options

                Expect.equal (printSyntax actual options) actual "The chosen layout is idempotent."
        }
        test "an anonymous object in an argument breaks unless a delegate body holds it" {
            let options = PrinterOptions.Default

            for context, expected in
                [
                    "Describe(new { msg = \"x\" }, other);", true
                    "Call(() => Describe(new { msg = \"x\" }, other));", true
                    "if (flag) { Describe(new { msg = \"x\" }, other); }", true
                    "Call(delegate { Describe(new { msg = \"x\" }, other); });", false
                ] do
                let actual = printSyntax ("class C{void M(){" + context + "}}") options

                if expected then
                    Expect.stringContains
                        actual
                        "msg = \"x\","
                        $"The anonymous object breaks in: {context}"
                else
                    Expect.stringContains
                        actual
                        "new { msg = \"x\" }"
                        $"A delegate body keeps it flat: {context}"

                Expect.equal (printSyntax actual options) actual "The layout is idempotent."
        }
        test "a with initializer follows the mode of what contains it" {
            let options = PrinterOptions.Default

            let standalone = printSyntax "class C{void M(){var a=r with{X=1};}}" options
            Expect.stringContains standalone "var a = r with { X = 1 };" "Standalone stays flat."

            let fits =
                printSyntax "class C{void M(){Describe(r with{X=1},s with{X=2});}}" options

            Expect.stringContains
                fits
                "Describe(r with { X = 1 }, s with { X = 2 })"
                "A call that fits stays flat."

            let broken =
                printSyntax
                    "class C{void M(){Describe(receiverName with{PropertyName=ValueName.Something},otherReceiver with{PropertyName=ValueName.SomethingElse});}}"
                    options

            Expect.stringContains
                broken
                "receiverName with\n            {\n                PropertyName = ValueName.Something,\n            },"
                "A broken argument list expands the initializer."

            for source in
                [
                    "class C{void M(){var a=r with{X=1};}}"
                    "class C{void M(){Describe(r with{X=1},s with{X=2});}}"
                    "class C{void M(){Describe(receiverName with{PropertyName=ValueName.Something},otherReceiver with{PropertyName=ValueName.SomethingElse});}}"
                ] do
                let actual = printSyntax source options
                Expect.equal (printSyntax actual options) actual "The layout is idempotent."
        }
        for name, source, expected in
            [
                "namespace close",
                "namespace N {\n#if true\nusing Z;\n#endif\nusing B;\n}",
                "namespace N\n{\n    using B;\n#if true\n    using Z;\n#endif\n}\n"
                "outer conditional",
                "#if true\nnamespace N {\n#if true\nusing Z;\n\n#endif\nusing B;\nclass C {}\n}\n#endif",
                "#if true\nnamespace N\n{\n    using B;\n#if true\n    using Z;\n#endif\n    class C { }\n}\n#endif\n"
                "extern header",
                "extern alias X;\n\nusing Z;\n#if true\nusing M;\n#endif\nusing A;",
                "extern alias X;\nusing A;\nusing Z;\n#if true\nusing M;\n#endif\n"
                "nested namespace close",
                "namespace O { namespace N {\n#if true\nusing Z;\n#endif\nusing B;\n}}",
                "namespace O\n{\n    namespace N\n    {\n        using B;\n#if true\n        using Z;\n#endif\n    }\n}\n"
            ] do
            test ($"using replay is stable on the first pass / {name}") {
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected "Replay uses the reparsed spacing and scope."
                Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable first pass."

                Expect.equal
                    (SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "replay.cs", source, actual))
                    (Ok())
                    "Sorting retains tokens and conditional membership."
            }

        test "ignore markers apply to directly printed binary and block bodies" {
            for source, preserved in
                [
                    "class C { void M() { var x =\n// csff-ignore\n1   +   2; } }", "1   +   2"
                    "class C { int M() =>\n// csff-ignore\n1   +   2; }", "1   +   2"
                    ("class C { void M()\n// csff-ignore\n{   int   x = 1 ;   } }",
                     "{   int   x = 1 ;   }")
                    ("class C { void M() // csff-ignore\n{ /* c */ X( 1 ); } }",
                     "{ /* c */ X( 1 ); }")
                    ("class C { void M() // csff-ignore-start\n{ /* c */ X( 1 ); } }",
                     "{ /* c */ X( 1 ); }")
                    ("class C { void M() { var f = () =>\n// csff-ignore\n1   +   2; } }",
                     "1   +   2")
                    "class C { void M() { var f = () =>\n// csff-ignore\n{   int   x = 1 ;   }; } }",
                    "{   int   x = 1 ;   }"
                    "class C { void M() { try\n// csff-ignore\n{   int   x = 1 ;   } finally {} } }",
                    "{   int   x = 1 ;   }"
                    "class C { int M(bool b) => b ?\n// csff-ignore\n1   +   2 : 3; }", "1   +   2"
                ] do
                let formatted = printSyntax source PrinterOptions.Default

                Expect.stringContains
                    formatted
                    preserved
                    "The selected node keeps its source bytes."

                Expect.equal
                    (printSyntax formatted PrinterOptions.Default)
                    formatted
                    "Ignoring the body is stable."

                Expect.equal
                    (SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "ignore.cs", source, formatted))
                    (Ok())
                    "Ignored expressions and blocks retain their syntax."
        }
        test "ignore ranges ending inside helper bodies retain the remaining syntax" {
            for source in
                [
                    "class C { int M() =>\n// csff-ignore-start\n1 +\n// csff-ignore-end\n2; }"
                    "class C { void M() { var x =\n// csff-ignore-start\n1 +\n// csff-ignore-end\n2; } }"
                    "class C { void M()\n// csff-ignore-start\n{ int   x=1;\n// csff-ignore-end\nX( 1 ); } }"
                ] do
                let formatted = printSyntax source PrinterOptions.Default
                Expect.stringContains formatted "// csff-ignore-end" "The closing marker survives."

                Expect.equal
                    (SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "partial-ignore.cs", source, formatted))
                    (Ok())
                    "A helper retains syntax following a partial ignore range."

                Expect.equal
                    (printSyntax formatted PrinterOptions.Default)
                    formatted
                    "The range boundary is stable."
        }
        test "foreign blocks with preprinted brace comments retain literal bytes" {
            let source =
                "class C {\nvoid M(\n#if !A\n)\n{ var s = @\"\n#endif\n#if B\n)\n{ /* c */ X(); }\n#endif\n#if !A\n\";\n}\n#endif\n}\n"

            let formatted = printSyntax source PrinterOptions.Default

            Expect.equal
                (SyntaxPreservation
                    .Checker()
                    .Check(PrinterOptions.Default, "foreign-block.cs", source, formatted))
                (Ok())
                "A preserved foreign block must not copy its opener twice."

            Expect.equal
                (printSyntax formatted PrinterOptions.Default)
                formatted
                "Foreign literal ownership is stable."
        }
        test "multiline using names sort independently of whitespace" {
            for whitespace in [ "\n    "; "\r\n\t"; "\t"; "\u2028    " ] do
                for container in [ ""; "namespace N {\n" ] do
                    let source =
                        container
                        + "using A.C;\nusing A."
                        + whitespace
                        + "B;\n"
                        + (if container.Length = 0 then "" else "}\n")

                    let formatted = printSyntax source PrinterOptions.Default

                    Expect.isLessThan
                        (formatted.IndexOf("using A.B;", StringComparison.Ordinal))
                        (formatted.IndexOf("using A.C;", StringComparison.Ordinal))
                        "Using order depends on names, not trivia."

                    Expect.equal
                        (printSyntax formatted PrinterOptions.Default)
                        formatted
                        "The first sorted output is already a fixed point."
        }
        test "printNode initializes trivia storage for directives and ignore spans" {
            for source in
                [
                    "#if true\n// c\n#endif\nusing B;\nusing A;\n"
                    "// csff-ignore\nclass C  {int P{get;}}\n"
                    "// csff-ignore-start\nclass C  {int P{get;}}\n// csff-ignore-end\n"
                ] do
                let tree = SyntaxTree()
                Parser.parse source tree
                use document = new DocumentBuffer()
                use printer = new Printer()
                document.AddTag Tag.StartIndent
                SyntaxPrinter.printNode source tree tree.RootIndex document
                document.AddTag Tag.EndIndent
                printer.Print(source, document, PrinterOptions.Default)
                let printed = outputText printer

                Expect.equal
                    (TokenPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "node.cs", source, printed))
                    (Ok())
                    "Printing a node retains tokens and supports the caller's indentation."

                if source.Contains("csff-ignore", StringComparison.Ordinal) then
                    Expect.stringContains
                        printed
                        "class C  {int P{get;}}"
                        "Ignore spans retain their bytes."
                else
                    Expect.stringContains
                        printed
                        "    using B;"
                        "Node printing keeps current indentation."

                    Expect.stringContains printed "// c" "Directive-owned comments survive."
        }
        for name, source in
            [
                "ignored alias after conditional extern",
                "#define C\n#if A\nextern alias X;\n#else\nusing System.Text;\n#endif\n// csff-ignore-start\nusing Alias =  System.String;\n// csff-ignore-end\nusing System;\n\nclass C\n{\n    public Type T => typeof(C);\n}\n"
                "nullable state after conditional extern",
                "#define C\n#if false\nextern alias X;\n#endif\n#nullable enable\nusing System.Text;\n#nullable disable\nusing System;\n\nclass C\n{\n    public string Name = null;\n}\n"
            ] do
            test ($"using directive order preserves compilation / {name}") {
                let errors (text: string) =
                    let compilation =
                        CSharpCompilation.Create(
                            "UsingDirectiveRegression",
                            [ CSharpSyntaxTree.ParseText(text) ],
                            [
                                Microsoft.CodeAnalysis.MetadataReference.CreateFromFile(
                                    typeof<obj>.Assembly.Location
                                )
                            ],
                            CSharpCompilationOptions(
                                Microsoft.CodeAnalysis.OutputKind.DynamicallyLinkedLibrary,
                                generalDiagnosticOption =
                                    Microsoft.CodeAnalysis.ReportDiagnostic.Error
                            )
                        )

                    compilation.GetDiagnostics()
                    |> Seq.filter (fun diagnostic ->
                        diagnostic.Severity = Microsoft.CodeAnalysis.DiagnosticSeverity.Error)
                    |> Seq.map string
                    |> Seq.toList

                Expect.isEmpty (errors source) "The input compiles with warnings treated as errors."
                let actual = printSyntax source PrinterOptions.Default

                Expect.isEmpty
                    (errors actual)
                    "Import membership and final nullable state must survive formatting."

                Expect.equal actual source "Keep source order and the ignored alias text."

                for symbols in [ [||]; [| "A" |] ] do
                    let usings (text: string) =
                        let options =
                            CSharpParseOptions(LanguageVersion.Preview)
                                .WithPreprocessorSymbols(symbols)

                        let root =
                            CSharpSyntaxTree.ParseText(text, options).GetCompilationUnitRoot()

                        Expect.isEmpty (root.GetDiagnostics()) "Both symbol configurations parse."
                        root.Usings |> Seq.map string |> Seq.toList

                    Expect.equal (usings actual) (usings source) "Active using order is unchanged."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Directive and ignore boundaries remain idempotent."
            }

        for directive in
            [
                "#define FEATURE"
                "#undef FEATURE"
                "#nullable enable"
                "#pragma warning disable CS0168"
                "#line 100"
                "#line (10,1)-(10,10) 1 \"mapped.cs\""
                "#error keep this error"
                "#warning keep this warning"
            ] do
            test ($"using run retains source order across directives / {directive.Split('\n')[0]}") {
                let source = "using Zebra;\n" + directive + "\nusing System;\nusing Alpha;\n"

                for configuration, options in OutputConfigurations.all do
                    let actual = printSyntax source options
                    Expect.equal actual source ($"Directive-bearing run at {configuration}.")
                    Expect.equal (printSyntax actual options) actual "Source order is idempotent."
            }

        for name, source, expected in
            [
                "#if group",
                "using Zebra;\n#if FEATURE\nusing Zulu;\n#elif OTHER\nusing Yankee;\n#else\nusing Xray;\n#endif\nusing System;\nusing Alpha;\n",
                "using System;\nusing Alpha;\nusing Zebra;\n#if FEATURE\nusing Zulu;\n#elif OTHER\nusing Yankee;\n#else\nusing Xray;\n#endif\n"
                "#region pair",
                "using Zebra;\n#region R\n#endregion\nusing System;\nusing Alpha;\n",
                "#region R\n#endregion\nusing System;\nusing Alpha;\nusing Zebra;\n"
            ] do
            test ($"using run sorts around relocatable directives / {name}") {
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected "Names sort; the frames keep their source order."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Sorted run is idempotent."
            }

        for header in
            [
                "#define FEATURE\n"
                "#undef FEATURE\n"
                "#nullable enable\n"
                "#pragma warning disable CS0168\n"
                "#region R\n#endregion\n"
                "#line 100\n"
            ] do
            test ($"closed file header permits using sorting / {header.Split('\n')[0]}") {
                let source = header + "using Zebra;\nusing System;\nusing Alpha;\n"
                let expected = header + "using System;\nusing Alpha;\nusing Zebra;\n"
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected "Header directives stay ahead of a directive-free run."
                Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable header."
            }

        test "a commented disabled extern alias still holds the head of the run" {
            let source =
                "#if false\n// using Fake;\nextern alias X;\n#endif\nusing Zebra;\nusing System;\nusing Alpha;\n"

            let expected =
                "#if false\n// using Fake;\nextern alias X;\n#endif\nusing Zebra;\nusing System;\nusing Alpha;\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The head stays; the rest of the run sorts."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable head."
        }

        test "a region spanning two usings keeps the run in source order" {
            let source = "using Z;\n#region R\nusing B;\n#endregion\nusing A;\n"
            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "Split region endpoints pin the run."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable region pair."
        }

        test "a positional directive after the first #if keeps the run in source order" {
            let source = "#if true\n#nullable enable\nusing System;\n#endif\nusing Alpha;\n"
            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "The movable header's directive pins the run."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable context."
        }

        test "a nested #endif does not end a disabled extern alias header" {
            let source =
                "#if A\nextern alias X;\n#else\n#if true\nusing Z;\n#endif\nusing Y;\n#endif\nusing B;\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "Every name stays in its branch."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable nested header."
        }

        test "adjacent directive groups keep their separating blank line" {
            let source = "#if true\nusing Z;\n#endif\nusing B;\n#if true\nusing A;\n#endif\n"

            let expected =
                "using B;\n#if true\nusing Z;\n#endif\n\n#if true\nusing A;\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The frames keep one blank line between them."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable blank."
        }

        for name, source in
            [
                "active", "#if true\nglobal using System.Text;\n#endif\nusing System;\n"
                "disabled", "#if A\nglobal using G;\n#endif\nusing System;\n"
            ] do
            test ($"a conditional global using keeps the run in source order / {name}") {
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual source "The conditional global import pins the run."
                Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable global."
            }

        test "a comment after a replayed #endif takes a hard separator" {
            let source =
                "#if true\nusing Z;\n#endif\n// note\nusing B;\n#if true\nusing A;\n#endif\n"

            let expected =
                "using B;\n#if true\nusing Z;\n#endif\n// note\n#if true\nusing A;\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The comment joins the frames without a blank."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable comment."
        }

        test "a commented disabled extern alias below the first using pins the run" {
            let source =
                "using Z;\n#if !FLAG\nusing W;\n#else\n// keep\nextern alias X;\n#endif\nusing A;\n"

            let expected =
                "using Z;\n\n#if !FLAG\nusing W;\n#else\n// keep\nextern alias X;\n#endif\nusing A;\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "No name may sort ahead of the extern alias."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable alias."
        }

        test "punctuated names sort by the invariant culture's primary order" {
            let source = "using static AB;\nusing static A<X>;\nclass C { }\n"
            let expected = "using static A<X>;\nusing static AB;\n\nclass C { }\n"
            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "A<X> sorts before AB."

            let source2 = "using B;\nusing @A;\nclass C { }\n"
            let expected2 = "using @A;\nusing B;\n\nclass C { }\n"
            let actual2 = printSyntax source2 PrinterOptions.Default
            Expect.equal actual2 expected2 "@A sorts before B."
        }

        test "a constant-condition frame stays glued to its carrying using" {
            let source =
                "#if false\nusing F;\n#endif\nusing System;\n#if true\nusing T;\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "The false frame stays above its using."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable frame."
        }

        for name, source in
            [ "open header", "#if A\nusing Zebra;\nusing System;\nusing Alpha;\n#endif\n" ] do
            test ($"using run retains source order with a leading open conditional / {name}") {
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual source "An open conditional belongs to the using run."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Stable conditional."
            }

        test "disabled leading using prints as a directive group after the sorted names" {
            let source =
                "#if A\n// Conditional using.\nusing Zebra;\n#endif\nusing System;\nusing Alpha;\n"

            let expected =
                "using System;\nusing Alpha;\n#if A\n// Conditional using.\nusing Zebra;\n#endif\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "The frame keeps its text below the sorted names."
            Expect.equal (printSyntax actual PrinterOptions.Default) actual "Stable frame."

            for symbols in [ [||]; [| "A" |] ] do
                let actives (text: string) =
                    let options =
                        CSharpParseOptions(LanguageVersion.Preview).WithPreprocessorSymbols(symbols)

                    CSharpSyntaxTree.ParseText(text, options).GetCompilationUnitRoot().Usings
                    |> Seq.map (fun node -> node.Name.ToString())
                    |> Seq.sort
                    |> Seq.toList

                Expect.equal
                    (actives actual)
                    (actives source)
                    "Zebra stays inside A; System and Alpha stay unconditional."
        }

        for name, source, expected in
            [
                "empty frame after conditional using frame",
                "#if A\nusing Z;\n#endif\n#if B\n#endif\nusing Y;\n",
                "using Y;\n#if A\nusing Z;\n#endif\n#if B\n#endif\n"
                "empty frame before conditional using frame",
                "#if B\n#endif\n#if A\nusing Z;\n#endif\nusing Y;\n",
                "using Y;\n#if B\n#endif\n#if A\nusing Z;\n#endif\n"
                "comment frame after conditional using frame",
                "#if A\nusing Z;\n#endif\n#if B\n// comment\n#endif\nusing Y;\n",
                "using Y;\n#if A\nusing Z;\n#endif\n#if B\n// comment\n#endif\n"
                "two conditional using frames",
                "#if A\nusing Z;\n#endif\n#if B\nusing W;\n#endif\nusing Y;\n",
                "using Y;\n#if A\nusing Z;\n#endif\n#if B\nusing W;\n#endif\n"
                "conditional global using frame preserves source order",
                "#if A\nusing Z;\n#endif\n#if B\nglobal using G;\n#endif\nusing Y;\n",
                "#if A\nusing Z;\n#endif\n#if B\nglobal using G;\n#endif\nusing Y;\n"
                "usings before and after multiple preprocessor frames",
                "using Z0;\n#if A\nusing Z;\n#endif\n#if B\n#endif\nusing Y;\nusing A0;\n",
                "using A0;\nusing Y;\nusing Z0;\n#if A\nusing Z;\n#endif\n#if B\n#endif\n"
                "empty frame on later using after replayed frame",
                "#if A\nusing Z;\n#endif\nusing X;\n#if B\n#endif\nusing D;\n",
                "using D;\nusing X;\n#if A\nusing Z;\n#endif\n\n#if B\n#endif\n"
            ] do
            test ($"using sort across multiple preprocessor frames / {name}") {
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected "Frames stay in directive order after sorted usings."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Stable second pass."

                Expect.equal
                    (SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "using-frames.cs", source, actual))
                    (Ok())
                    "Preprocessor directive order and using membership are preserved."
            }

        test "enum conditional separator avoids a synthetic comma" {
            let options = PrinterOptions.Default
            let checker = TokenPreservation.Checker()

            for memberText in [ "A"; "A // keep"; "A /* keep */" ] do
                let source = $"enum E\n{{\n    {memberText}\n#if DEBUG\n    ,\n    B,\n#endif\n}}\n"

                for prefix in [ ""; "#define DEBUG\n" ] do
                    let input = prefix + source
                    let actual = printSyntax input options

                    for symbols in [ ""; "#define DEBUG\n" ] do
                        for text in [ input; actual ] do
                            GeneratedOutput.checkSyntax (symbols + text)
                            |> function
                                | Ok() -> ()
                                | Error error -> failtest error

                    Expect.equal actual input "The conditional branch supplies the separator."

                    checker.Check(options, "enum-conditional-separator.cs", input, actual)
                    |> function
                        | Ok() -> ()
                        | Error error -> failtest error

                    Expect.equal
                        (printSyntax actual options)
                        actual
                        "Conditional enum separators are idempotent."

        }
        for comment in [ "// keep\n"; "/* keep */" ] do
            test ($"enum missing trailing comma precedes trailing comment / {comment.Trim()}") {
                let options = PrinterOptions.Default
                let source = "enum E{A " + comment + "}"
                let actual = printSyntax source options
                let expected = "enum E\n{\n    A, " + comment.Trim() + "\n}\n"

                Expect.equal actual expected "Insert the comma before the comment trivia."

                for text in [ source; actual ] do
                    GeneratedOutput.checkSyntax text
                    |> function
                        | Ok() -> ()
                        | Error error -> failtest error

                TokenPreservation
                    .Checker()
                    .Check(options, "enum-trailing-comment.cs", source, actual)
                |> function
                    | Ok() -> ()
                    | Error error -> failtest error

                Expect.equal
                    (printSyntax actual options)
                    actual
                    "Trailing enum commas are idempotent."
            }
        test "closed extern header keeps warning pragmas in source order" {
            let header = "#if false\nextern alias X;\n#endif\n"

            let members =
                "\n[System.Obsolete(\"Old\")]\nstatic class Old\n{\n    public static int Value => 1;\n}\n\nclass C\n{\n    public int M() => Value;\n}\n"

            let source =
                header
                + "#pragma warning disable CS0618\nusing static Old;\n#pragma warning restore CS0618\nusing System;\n"
                + members

            let errors (text: string) =
                let compilation =
                    CSharpCompilation.Create(
                        "PragmaRegression",
                        [ CSharpSyntaxTree.ParseText(text) ],
                        [
                            Microsoft.CodeAnalysis.MetadataReference.CreateFromFile(
                                typeof<obj>.Assembly.Location
                            )
                        ],
                        CSharpCompilationOptions(
                            Microsoft.CodeAnalysis.OutputKind.DynamicallyLinkedLibrary,
                            generalDiagnosticOption = Microsoft.CodeAnalysis.ReportDiagnostic.Error
                        )
                    )

                compilation.GetDiagnostics()
                |> Seq.filter (fun diagnostic ->
                    diagnostic.Severity = Microsoft.CodeAnalysis.DiagnosticSeverity.Error)
                |> Seq.map string
                |> Seq.toList

            Expect.isEmpty (errors source) "The input compiles with warnings treated as errors."
            let actual = printSyntax source PrinterOptions.Default

            Expect.isEmpty
                (errors actual)
                "Sorting must not restore CS0618 before the obsolete using."

            Expect.equal actual source "Post-header pragmas retain their scope and final state."

            Expect.equal
                (printSyntax actual PrinterOptions.Default)
                actual
                "The header and attached pragmas remain idempotent."
        }

        test "ordinary extern alias retains its blank line before usings" {
            let source = "extern alias X;\n\nusing System;\n"
            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual source "Preserve the ordinary extern/using separator."

            Expect.equal
                (printSyntax actual PrinterOptions.Default)
                actual
                "The ordinary separator remains idempotent."
        }

        for name, source, expected in
            [
                "all categories",
                "// extern Z\nextern alias Z;\n// extern A\nextern alias A;\nusing Zebra;\n// Alpha\nusing Alpha;\n// assembly\n[assembly: A]\n// module\n[module: B]\n// first\nclass First{}\n// second\nclass Second{}\n",
                "// extern Z\nextern alias Z;\n// extern A\nextern alias A;\n// Alpha\nusing Alpha;\nusing Zebra;\n\n// assembly\n[assembly: A]\n// module\n[module: B]\n\n// first\nclass First { }\n\n// second\nclass Second { }\n"
                "block namespace",
                "namespace N {\n// extern Z\nextern alias Z;\n// extern A\nextern alias A;\nusing Zebra;\n// Alpha\nusing Alpha;\n// first\nclass First{}\n// second\nclass Second{}\n}\n",
                "namespace N\n{\n    // extern Z\n    extern alias Z;\n    // extern A\n    extern alias A;\n    // Alpha\n    using Alpha;\n    using Zebra;\n\n    // first\n    class First { }\n\n    // second\n    class Second { }\n}\n"
                "file-scoped namespace",
                "namespace N;\n// extern Z\nextern alias Z;\n// extern A\nextern alias A;\nusing Zebra;\n// Alpha\nusing Alpha;\n// first\nclass First{}\n// second\nclass Second{}\n",
                "namespace N;\n\n// extern Z\nextern alias Z;\n// extern A\nextern alias A;\n// Alpha\nusing Alpha;\nusing Zebra;\n\n// first\nclass First { }\n\n// second\nclass Second { }\n"
                "empty compilation unit", "", ""
                "only externs",
                "extern alias Z;\nextern alias A;\n",
                "extern alias Z;\nextern alias A;\n"
                "only attributes", "[assembly: A]\n[module: B]\n", "[assembly: A]\n[module: B]\n"
                "only members",
                "class First{}\nclass Second{}\n",
                "class First { }\n\nclass Second { }\n"
                "empty block namespace", "namespace Empty{}\n", "namespace Empty { }\n"
                "empty file-scoped namespace", "namespace File;\n", "namespace File;\n"
            ] do
            test ($"namespace child categories preserve output / {name}") {
                let checker = TokenPreservation.Checker()
                let tree = SyntaxTree()

                for configuration, options in OutputConfigurations.all do
                    let expected =
                        if options.UseTabs then
                            expected.Replace("    ", "\t")
                        else
                            expected

                    let actual = printSyntax source options
                    Expect.equal actual expected ($"Preserve category order at {configuration}.")

                    Expect.equal
                        (printSyntax actual options)
                        actual
                        "Category output is idempotent."

                    for text in [ source; actual ] do
                        NodeOracle.check "namespace-categories.cs" text tree
                        |> function
                            | Ok() -> ()
                            | Error error -> failtest error

                    checker.Check(options, "namespace-categories.cs", source, actual)
                    |> function
                        | Ok() -> ()
                        | Error error -> failtest error
            }

        for name, source, expected in
            [
                "sorting",
                "using Zebra;using System;using Alpha;",
                "using System;\nusing Alpha;\nusing Zebra;\n"
                "leading blank lines",
                "\n\nusing Zebra;\nusing System;\n",
                "using System;\nusing Zebra;\n"
                "leading comment",
                "// header\nusing Zebra;\n// System\nusing System;\n",
                "// header\n// System\nusing System;\nusing Zebra;\n"
                "warning pragmas",
                "#pragma warning disable CS0618\nusing static Old;\n#pragma warning restore CS0618\nusing System;\n",
                "#pragma warning disable CS0618\nusing static Old;\n#pragma warning restore CS0618\nusing System;\n"
                "define",
                "#define A\nusing Zebra;\nusing System;\n",
                "#define A\nusing System;\nusing Zebra;\n"
                "undef",
                "#undef A\nusing Zebra;\nusing System;\n",
                "#undef A\nusing System;\nusing Zebra;\n"
                "extern without separator",
                "extern alias X;\nusing System;\n",
                "extern alias X;\nusing System;\n"
                "extern with separator",
                "extern alias X;\n\nusing System;\n",
                "extern alias X;\n\nusing System;\n"
                "extern and sorted usings",
                "extern alias X;\n\nusing Zebra;\nusing System;\n",
                "extern alias X;\nusing System;\n\nusing Zebra;\n"
                "multiple externs",
                "extern alias Z;\nextern alias X;\n\nusing Zebra;\nusing System;\n",
                "extern alias Z;\nextern alias X;\nusing System;\n\nusing Zebra;\n"
                "extern and using comment",
                "extern alias X;\n\n// Zebra\nusing Zebra;\nusing System;\n",
                "extern alias X;\n// Zebra\nusing System;\n\nusing Zebra;\n"
                "block namespace",
                "namespace N {extern alias X;\n\nusing Zebra;using System;}",
                "namespace N\n{\n    extern alias X;\n    using System;\n\n    using Zebra;\n}\n"
                "file namespace",
                "namespace N;\nextern alias X;\n\nusing Zebra;\nusing System;\n",
                "namespace N;\n\nextern alias X;\nusing System;\n\nusing Zebra;\n"
                "using groups",
                "global using Z;global using System;using static Z;using static System.Math;using A=Z;using X::Y;using Zebra;using System;",
                "global using System;\nglobal using Z;\nusing System;\nusing X::Y;\nusing Zebra;\nusing static System.Math;\nusing static Z;\nusing A = Z;\n"
                "conditional usings",
                "#if A\nusing Zebra;\n#endif\nusing System;\n",
                "using System;\n#if A\nusing Zebra;\n#endif\n"
                "ignored usings",
                "extern alias X;\n\n// csff-ignore-start\nusing Z =  A;\n// csff-ignore-end\nusing System;\n",
                "extern alias X;\nusing System;\n\n// csff-ignore-start\nusing Z =  A;\n// csff-ignore-end\n"
            ] do
            test ($"ordinary using and extern output matches merge base / {name}") {
                for configuration, options in OutputConfigurations.all do
                    let expected =
                        if options.UseTabs then
                            expected.Replace("    ", "\t")
                        else
                            expected

                    Expect.equal
                        (printSyntax source options)
                        expected
                        ($"Ordinary trivia keeps merge-base behavior at {configuration}.")
            }

        for name, source, expected in
            [
                "sorted run with a separated using",
                "extern alias X;\nusing System;\n\nusing Zebra;\n",
                "extern alias X;\nusing System;\n\nusing Zebra;\n"
                "two separated usings",
                "extern alias X;\nusing System;\n\nusing Zebra;\n\nusing Alpha;\n",
                "extern alias X;\nusing System;\n\nusing Alpha;\n\nusing Zebra;\n"
                "separated using sorts first",
                "extern alias X;\nusing B;\n\nusing A;\n",
                "extern alias X;\n\nusing A;\nusing B;\n"
                "global usings",
                "extern alias X;\n\nglobal using B;\nglobal using A;\n",
                "extern alias X;\nglobal using A;\n\nglobal using B;\n"
                "comment with blank line before global using alias",
                "extern alias RemoteServerCore;\n// ApplicationLaunchMonitor.cs can compile without modification.\n\nglobal using IApplicationLaunchMonitor = RemoteServerCore::Uno.UI.RemoteControl.Server.AppLaunch.IApplicationLaunchMonitor;\n",
                "extern alias RemoteServerCore;\n// ApplicationLaunchMonitor.cs can compile without modification.\n\nglobal using IApplicationLaunchMonitor = RemoteServerCore::Uno.UI.RemoteControl.Server.AppLaunch.IApplicationLaunchMonitor;\n"
                "blank line before comment and global using alias",
                "extern alias RemoteServerCore;\n\n// ApplicationLaunchMonitor.cs can compile without modification.\nglobal using IApplicationLaunchMonitor = RemoteServerCore::Uno.UI.RemoteControl.Server.AppLaunch.IApplicationLaunchMonitor;\n",
                "extern alias RemoteServerCore;\n// ApplicationLaunchMonitor.cs can compile without modification.\n\nglobal using IApplicationLaunchMonitor = RemoteServerCore::Uno.UI.RemoteControl.Server.AppLaunch.IApplicationLaunchMonitor;\n"
                "comment with blank line before global using",
                "extern alias X;\n// Header comment.\n\nglobal using System;\n",
                "extern alias X;\n// Header comment.\n\nglobal using System;\n"
                "comment with blank line before using alias",
                "extern alias X;\n// Header comment.\n\nusing A = X::System.String;\n",
                "extern alias X;\n// Header comment.\n\nusing A = X::System.String;\n"
                "comment with blank line before plain using",
                "extern alias X;\n// Header comment.\n\nusing System;\n",
                "extern alias X;\n// Header comment.\n\nusing System;\n"
            ] do
            test ($"extern alias run keeps each using's blank line / {name}") {
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected "Each using carries its own separator."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Stable second pass."
            }

        let conditionalExternAlias =
            "#if DEBUG\nextern alias MonoSecurity;\n#else\nusing Mono.Security.Cryptography;\n#endif\n\nusing System;\n"

        test "conditional extern alias keeps unconditional using after endif" {
            let actual = printSyntax conditionalExternAlias PrinterOptions.Default

            Expect.equal
                actual
                conditionalExternAlias
                "Match EdgeCase7's historical expected output."

            Expect.equal
                (printSyntax actual PrinterOptions.Default)
                actual
                "Reparsing and formatting preserves directive membership."
        }

        for debug in [ false; true ] do
            test ($"conditional extern alias preserves using membership / DEBUG {debug}") {
                let actual = printSyntax conditionalExternAlias PrinterOptions.Default

                let options =
                    CSharpParseOptions(LanguageVersion.Preview)
                        .WithPreprocessorSymbols(if debug then [| "DEBUG" |] else [||])

                let root = CSharpSyntaxTree.ParseText(actual, options).GetCompilationUnitRoot()
                Expect.isEmpty (root.GetDiagnostics()) "Both configurations remain valid syntax."

                let directive kind =
                    root.DescendantTrivia() |> Seq.find (fun trivia -> trivia.RawKind = int kind)

                let elseDirective = directive SyntaxKind.ElseDirectiveTrivia
                let endIf = directive SyntaxKind.EndIfDirectiveTrivia

                let memberships =
                    root.Usings
                    |> Seq.map (fun node ->
                        node.Name.ToString(),
                        if node.SpanStart > endIf.SpanStart then "unconditional"
                        elif node.SpanStart > elseDirective.SpanStart then "!DEBUG"
                        else "DEBUG")
                    |> Seq.toList

                let expected =
                    if debug then
                        [ "System", "unconditional" ]
                    else
                        [ "Mono.Security.Cryptography", "!DEBUG"; "System", "unconditional" ]

                Expect.equal memberships expected "Active usings retain their original branches."
            }

        let activeUsings (source: string) symbols =
            let options =
                CSharpParseOptions(LanguageVersion.Preview)
                    .WithPreprocessorSymbols(symbols: string[])

            let root = CSharpSyntaxTree.ParseText(source, options).GetCompilationUnitRoot()

            Expect.isEmpty
                (root.GetDiagnostics())
                "Every symbol configuration remains valid syntax."

            root.Usings
            |> Seq.map (fun node -> node.Name.ToString())
            |> Seq.sort
            |> Seq.toList

        for directive in [ "#define B"; "#undef B" ] do
            for name, ignored, suffix in
                [
                    "ends inside prefix",
                    "// csff-ignore-start\nusing Y =   Some.Namespace;\nusing X =   Other.Namespace;\n",
                    "// csff-ignore-end\nusing W =   Last.Namespace;\n#endif\nusing System;\n"
                    "crosses endif",
                    "// csff-ignore-start\nusing Y =   Some.Namespace;\n#endif\nusing X =   Other.Namespace;\n",
                    "// csff-ignore-end\nusing W =   Last.Namespace;\n"
                ] do
                test ($"preserved using prefix honors ignore regions / {directive} / {name}") {
                    let source = "#if true\n" + directive + "\nusing Zebra;\n" + ignored + suffix
                    let actual = printSyntax source PrinterOptions.Default

                    Expect.stringContains actual ignored "Every ignored using retains its source."

                    Expect.stringContains
                        actual
                        "using W = Last.Namespace;"
                        "Formatting resumes at the ignore-end marker."

                    Expect.equal
                        (printSyntax actual PrinterOptions.Default)
                        actual
                        "Ignored prefix boundaries remain idempotent."

                    Expect.equal
                        (activeUsings actual [||])
                        (activeUsings source [||])
                        "Ignore handling preserves active usings."
                }

            test ($"preserved using prefix keeps unconditional source order / {directive}") {
                let header = "#if true\n" + directive + "\nusing Conditional;\n#endif\n"
                let source = header + "using Zebra;\nusing System;\nusing Alpha;\n"
                let actual = printSyntax source PrinterOptions.Default

                Expect.equal
                    actual
                    source
                    "The directive-bearing run keeps every using in source order."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "The closing directive is emitted only once."

                Expect.equal
                    (activeUsings actual [||])
                    (activeUsings source [||])
                    "Sorting preserves conditional membership."
            }

        test "conditional extern header does not recount trivia after an ignore region" {
            let source =
                "#if true\nextern alias X;\nusing Zebra;\n// csff-ignore-start\nusing Y =   Some.Namespace;\n// csff-ignore-end\n#endif\nusing System;\n"

            let expected =
                "#if true\nextern alias X;\nusing Zebra;\n// csff-ignore-start\nusing Y =   Some.Namespace;\n// csff-ignore-end\n#endif\nusing System;\n"

            let actual = printSyntax source PrinterOptions.Default
            Expect.equal actual expected "Keep the ignored span and its closing directives intact."
            let mutable previous = actual

            for pass = 1 to 3 do
                let next = printSyntax previous PrinterOptions.Default

                Expect.equal
                    next
                    expected
                    ($"Pass {pass} must not add blank lines between endif and System.")

                previous <- next

            for symbols in [ [||]; [| "DEBUG" |] ] do
                Expect.equal
                    (activeUsings actual symbols)
                    (activeUsings source symbols)
                    "The conditional header and unconditional using remain valid."
        }

        test "closed extern header does not grow blank lines before ignored usings" {
            let ignored = "// csff-ignore-start\nusing Y =   Some.Namespace;\n"

            let source =
                "#define A\n#if A\nextern alias X;\n#endif\nusing System;\n"
                + ignored
                + "// csff-ignore-end\nclass C{}\n"

            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains actual ignored "The ignored using retains its original text."

            Expect.equal
                (printSyntax actual PrinterOptions.Default)
                actual
                "Consumed closing trivia must not add a separator on each pass."
        }

        for name, source, expected in
            [
                "depth across reparses",
                "#define C\n#if A\nextern alias X;\n#endif\n#if C\nusing Zebra;\n#endif\nusing System;\n",
                "#define C\n#if A\nextern alias X;\n#endif\n#if C\nusing Zebra;\n#endif\nusing System;\n"
                "closed header",
                "#if false\nextern alias X;\n#endif\nusing Zebra;\nusing System;\n",
                "#if false\nextern alias X;\n#endif\nusing Zebra;\nusing System;\n"
            ] do
            test ($"conditional extern header preserves valid sorted usings / {name}") {
                let actual = printSyntax source PrinterOptions.Default

                Expect.equal actual expected "Keep directive pairs together and sort outside them."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "The preserved header is idempotent."

                for symbols in [ [||]; [| "A" |]; [| "C" |]; [| "A"; "C" |] ] do
                    Expect.equal
                        (activeUsings actual symbols)
                        (activeUsings source symbols)
                        "Each configuration keeps its original active usings."
            }

        test "conditional extern header preserves ignored leading trivia" {
            let ignored =
                "// csff-ignore-start\n#if false\nextern alias X;\n#else\nusing Zebra =   Some.Namespace;\n#endif\nusing System;\n"

            let source = ignored + "// csff-ignore-end\nclass C{}\n"
            let actual = printSyntax source PrinterOptions.Default

            Expect.stringContains
                actual
                ignored
                "The ignored span retains its directives, marker and unformatted using."

            Expect.equal
                (printSyntax actual PrinterOptions.Default)
                actual
                "Ignored leading trivia survives reparsing."

            for symbols in [ [||]; [| "A" |] ] do
                Expect.equal
                    (activeUsings actual symbols)
                    (activeUsings source symbols)
                    "The ignored conditional remains valid with unchanged active usings."
        }

        for name, suffix, expectedSuffix in
            [
                "pragma",
                "#pragma warning disable CS0168\nusing Alpha;\n",
                "#pragma warning disable CS0168\nusing Alpha;\n"
                "comment",
                "// Keep Alpha's comment.\nusing Alpha;\n",
                "// Keep Alpha's comment.\nusing Alpha;\n"
                "conditional",
                "#if OTHER\nusing Zebra;\n#endif\nusing Alpha;\n",
                "using Alpha;\n#if OTHER\nusing Zebra;\n#endif\n"
                "conditional with else",
                "#if OTHER\nusing Zebra;\n#else\nusing Zulu;\n#endif\nusing Alpha;\n",
                "using Alpha;\n#if OTHER\nusing Zebra;\n#else\nusing Zulu;\n#endif\n"
            ] do
            test ($"conditional extern alias preserves following using trivia / {name}") {
                let source = conditionalExternAlias + suffix
                let actual = printSyntax source PrinterOptions.Default

                Expect.equal
                    actual
                    (conditionalExternAlias + expectedSuffix)
                    "The directive-bearing run retains following trivia in source order."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Preserved directives are idempotent."

                for symbols in [ [||]; [| "DEBUG" |]; [| "OTHER" |]; [| "DEBUG"; "OTHER" |] ] do
                    Expect.equal
                        (activeUsings actual symbols)
                        (activeUsings source symbols)
                        "Active usings retain their membership in both conditional blocks."
            }

        for directive in [ "#define B"; "#undef B" ] do
            test ($"conditional symbol directive preserves using membership / {directive}") {
                for source in
                    [
                        "#if A\n" + directive + "\nusing Zebra;\n#endif\nusing System;\n"
                        "#if A\n#if C\n"
                        + directive
                        + "\n#endif\nusing Zebra;\nusing Yankee;\n#endif\nusing System;\n"
                    ] do
                    let actual = printSyntax source PrinterOptions.Default

                    Expect.equal
                        actual
                        source
                        "The symbol directive stays inside its original conditional."

                    Expect.equal
                        (printSyntax actual PrinterOptions.Default)
                        actual
                        "Conditional symbol directives are idempotent."

                    for symbols in
                        [ [||]; [| "A" |]; [| "B" |]; [| "A"; "B" |]; [| "C" |]; [| "A"; "C" |] ] do
                        Expect.equal
                            (activeUsings actual symbols)
                            (activeUsings source symbols)
                            "System stays unconditional and Zebra stays inside A."
            }

            test ($"file-header symbol directive stays ahead of sorted usings / {directive}") {
                for prefix in [ ""; "#if A\n#define C\n#endif\n" ] do
                    let header = prefix + directive + "\n"

                    let actual =
                        printSyntax
                            (header + "using Zebra;\nusing System;\n")
                            PrinterOptions.Default

                    Expect.equal
                        actual
                        (header + "using System;\nusing Zebra;\n")
                        "Unconditional symbol directives remain in the file header."
            }

        test "deeply nested conditions are solved without enumerating every assignment" {
            let depth = 40

            let source =
                String.concat "" [ for i in 1..depth -> $"#if S{i}\n" ]
                + "class C{}\n"
                + String.replicate depth "#endif\n"

            let watch = Diagnostics.Stopwatch.StartNew()
            let actual = printSyntax source PrinterOptions.Default
            Expect.stringContains actual "class C { }" "The innermost branch is formatted."

            let redefined =
                String.replicate depth "#if A\n#define A\n#endif\n"
                + "#if A\nclass D{}\n#endif\n"

            let actual = printSyntax redefined PrinterOptions.Default
            Expect.stringContains actual "class D { }" "The redefined branch is formatted."

            let wide = String.Join("||", [ for i in 1..24 -> $"S{i}" ])

            let contradicted =
                $"#if A\n#if !A\n#if {wide}\nclass E{{}}\n#endif\n#endif\n#endif\n"
                + $"#if A\n#if !B\n#if {wide}\nclass F{{}}\n#endif\n#endif\n#endif\n"

            let actual = printSyntax contradicted PrinterOptions.Default
            Expect.stringContains actual "class E{}" "No symbol set reaches class E."
            Expect.stringContains actual "class F { }" "The reachable wide branch is formatted."

            let nest = String.concat "" [ for i in 1..20 -> $"#if S{i}||T{i}\n" ]
            let close = String.replicate 20 "#endif\n"

            let unreachable =
                "#if A\n#if !A\n" + nest + "class G{}\n" + close + "#endif\n#endif\n"

            let actual = printSyntax unreachable PrinterOptions.Default
            Expect.stringContains actual "class G{}" "No symbol set reaches class G."

            let undecided =
                "#if A||B\n#if A||!B\n#if !A||B\n"
                + nest
                + "class H{}\n#if !A||!B\nclass I{}\n#endif\n"
                + close
                + "#endif\n#endif\n#endif\n"

            let actual = printSyntax undecided PrinterOptions.Default
            Expect.stringContains actual "class H { }" "The reachable nested branch is formatted."
            Expect.stringContains actual "class I{}" "No symbol set reaches class I."

            let exhausted =
                "#if ((A||C)&&(A||!C)&&(!A||C)&&(!A||!C)"
                + String.concat "" [ for i in 1..10 -> $"&&(X{i}==X{i})" ]
                + ")||B\nclass J{}\n#endif\n"

            let actual = printSyntax exhausted PrinterOptions.Default
            Expect.stringContains actual "class J { }" "A set that reaches class J is found."
            Expect.isLessThan watch.Elapsed.TotalSeconds 10.0 "Solving stays fast."

            let chain =
                "#if S0\nclass K{}\n"
                + String.concat "" [ for i in 1..800 -> $"#elif S{i}\nclass K{{}}\n" ]
                + "#endif\n"

            let tree = SyntaxTree()
            Parser.parse chain tree
            let selection = Diagnostics.Stopwatch.StartNew()
            let sets = Preprocessor.symbolSets chain tree
            Expect.equal sets.Length 801 "Each branch is reached by its own symbol."

            Expect.isLessThan
                selection.Elapsed.TotalSeconds
                8.0
                "An #elif chain is selected quickly."
        }

        test "every reachable nested or later branch is formatted" {
            for source in
                [
                    "#if !A||B&&C\n#if A||C\nclass One{}\n#endif\n#else\nclass Two{}\n#endif\n"
                    "#if A\n#if B\nclass One{}\n#endif\n#else\nclass Two{}\n#endif\n"
                    "#if A\nclass One{}\n#elif B\nclass Two{}\n#endif\n"
                    "#if X\n#if !X||Y\nclass One{}\n#endif\n#elif Z\nclass Two{}\n#endif\n"
                    "#if A\n#undef A\n#if !A&&B\nclass One{}\n#endif\n#else\nclass Two{}\n#endif\n"
                    "#if A\n#define B\n#endif\n#if B\nclass One{}\n#else\nclass Two{}\n#endif\n"
                    "#undef TRUE\n#if TRUE && A\nclass One{}\n#else\nclass Two{}\n#endif\n"
                    "#define FALSE\n#if !FALSE && A\nclass One{}\n#else\nclass Two{}\n#endif\n"
                    "#if A\n/*\n#undef B\n*/\n#endif\n#if A && B\nclass One{}\n#else\nclass Two{}\n#endif\n"
                    "#if A\n/*\n#define B\n*/\n#endif\n#if B\nclass One{}\n#else\nclass Two{}\n#endif\n"
                ] do
                let actual = printSyntax source PrinterOptions.Default

                for name in [ "One"; "Two" ] do
                    Expect.stringContains
                        actual
                        $"class {name} {{ }}"
                        $"Branch with class {name} is formatted."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Nested branches are idempotent."
        }

        test "directives after an unterminated comment in skipped text are found" {
            for source in
                [
                    "#if false\n/*\n#endif\n#define X\n#if B\nclass Target{}\n#endif\n"
                    "#if false\n/*\n#else\n#define X\n#if B\nclass Target{}\n#endif\n#endif\n"
                    "#if false\n/*\n#elif true\n#define X\n#if B\nclass Target{}\n#endif\n#endif\n"
                ] do
                Expect.stringContains
                    (printSyntax source PrinterOptions.Default)
                    "class Target { }"
                    source
        }

        test "a branch behind a comment in skipped text gets its own witness" {
            let body = "#if B\n#if false\n/*\n#endif\n#else\nclass Target{}\n/* */\n#endif\n"

            for source in
                [
                    "#define X\n#if A == !B\n" + body + "#endif\n"
                    "#if A == !B\n" + body + "#endif\n"
                    "#define X\n#if A == !B\n" + body.Replace("#else", "#elif !B") + "#endif\n"
                    "#define X\n#if C\n#if D\n#if A == !B\n" + body + "#endif\n#endif\n#endif\n"
                    "#define X\n#if A == !B\n" + body.Replace("#if false", "#if C") + "#endif\n"
                ] do
                Expect.stringContains
                    (printSyntax source PrinterOptions.Default)
                    "class Target { }"
                    source

            let update =
                "#undef Y\n#if A == !B\n"
                + body.Replace("class Target{}", "#define Y\nclass Target{}")
                + "#endif\n#if Y\nclass Later{}\n#endif\n"

            let actual = printSyntax update PrinterOptions.Default

            for name in [ "Target"; "Later" ] do
                Expect.stringContains actual $"class {name} {{ }}" $"class {name} is formatted."
        }

        test "the all-active classification lexes again only where a configuration reads it" {
            let hiddenDirective =
                "#define B\n#if A\n/** */ #if B\n/*\n#undef C\n*/\n/** */ #endif\n#endif\n"
                + "#if A && C\nclass Target{}\n#endif\n"

            let holeDirective =
                "class C { string S = $\"{\n#define B\n1\n}\"; }\n#if B\nclass Target{}\n#endif\n"

            let dependent =
                [
                    hiddenDirective
                    "#if A\n/*\n#endif\n*/\n#if B\nclass Target{}\n#endif\n"
                    "#if A\nvar s = @\"\n#endif\n\";\n#if B\nclass Target{}\n#endif\n"
                    "#if A\nvar s = \"\"\"\n#endif\n\"\"\";\n#if B\nclass Target{}\n#endif\n"
                    "#if A\nvar s = \"a\\\n#endif\n\";\n#if B\nclass Target{}\n#endif\n"
                    "#if A\nvar s = $\"{\n#endif\n}\";\n#if B\nclass Target{}\n#endif\n"
                ]

            let independent =
                [
                    holeDirective
                    "#if A\nvar s = \"text\";\nvar c = 'x';\n#else\nclass Target{}\n#endif\n"
                    "#if A\n// comment\n/* and\nanother */\n/// <summary>x</summary>\n#else\nclass Target{}\n#endif\n"
                    "#if A\nvar s = @\"over\ntwo lines\";\n#else\nclass Target{}\n#endif\n"
                    "#if A\nvar s = $\"{Hole()}\";\n#else\nclass Target{}\n#endif\n"
                    "#if !A\nclass Target{}\nvar s = \"text\";\n#endif\n"
                ]

            for source in dependent @ independent do
                let tree = SyntaxTree()
                Parser.parse source tree

                Expect.equal
                    (Preprocessor.pathDependent source tree)
                    (List.contains source dependent)
                    source

            let holeTree = SyntaxTree()
            Parser.parse holeDirective holeTree
            Expect.isFalse holeTree.IsComplete "Directive # inside interpolation hole fails parse."

            Expect.equal
                (Preprocessor.symbolSets holeDirective holeTree)
                [| [| "B" |] |]
                "Non-directive #define B inside hole does not satisfy later #if B."

            for source in hiddenDirective :: List.tail independent do
                Expect.stringContains
                    (printSyntax source PrinterOptions.Default)
                    "class Target { }"
                    source

            Expect.stringContains
                (printSyntax
                    "#if A\nclass C { string S = $\"{\n#define B\n1\n}\"; }\n#endif\n#if B\nclass Target{}\n#endif\n"
                    PrinterOptions.Default)
                "class Target { }"
                "Inactive hole #define B leaves valid {B} configuration free to format Target."
        }

        test "directive text inside an active comment or literal changes no branch state" {
            let reported =
                "#define X\n#if A\n/*\n#if false\n*/\n#if B\nclass Target{}\n#endif\n/*\n#endif\n*/\n#endif\n"

            let surrounded opening closing =
                $"#define X\n#if A\n/*\n{opening}\n*/\n#if A&&B\nclass Target{{}}\n#endif\n/*\n{closing}\n*/\n#endif\n"

            for source in
                [
                    reported
                    reported.Replace("#define X\n", "")
                    surrounded "#else\n#if false" "#endif\n#if false"
                    surrounded "#elif false" ""
                    surrounded "#region Hidden" "#endregion"
                    "#define X\n#if C\n#if D\n"
                    + reported.Replace("#define X\n", "")
                    + "#endif\n#endif\n"
                    reported.Replace("/*", "struct Holder { string S = @\"").Replace("*/", "\"; }")
                    reported
                        .Replace("/*", "struct Holder { string S = \"\"\"")
                        .Replace("*/", "\"\"\"; }")
                ] do
                Expect.stringContains
                    (printSyntax source PrinterOptions.Default)
                    "class Target { }"
                    source

                let tree = SyntaxTree()
                Parser.parse source tree
                Expect.isTrue (Preprocessor.pathDependent source tree) source

            let update =
                "#undef Y\n"
                + reported.Replace("class Target{}", "#define Y\nclass Target{}")
                + "#if Y\nclass Later{}\n#endif\n"

            let actual = printSyntax update PrinterOptions.Default

            for name in [ "Target"; "Later" ] do
                Expect.stringContains actual $"class {name} {{ }}" $"class {name} is formatted."
        }

        test "an unsatisfiable left side does not hide an easy right side" {
            let pairs = String.concat "&&" [ for i in 1..8 -> $"(S{i}||T{i})" ]

            let source =
                $"#if (C&&(A||B)&&(!A||B)&&!B&&{pairs})||(!C&&D)\nclass Target{{}}\n#endif\n"

            Expect.stringContains
                (printSyntax source PrinterOptions.Default)
                "class Target { }"
                "{D} reaches class Target."
        }

        test "symbol selection allocation grows linearly with independent branches" {
            let independent count defined =
                let source = Text.StringBuilder()

                if defined then
                    for i in 1..count do
                        source.Append($"#define N{i}\n") |> ignore

                for i in 1..count do
                    let condition = if defined then $"N{i}" else $"N{i}&&M{i}"
                    source.Append($"#if {condition}\nclass C{i}{{}}\n#endif\n") |> ignore

                source.ToString()

            let selected source =
                let tree = SyntaxTree()
                Parser.parse source tree
                let before = GC.GetAllocatedBytesForCurrentThread()
                let sets = Preprocessor.symbolSets source tree
                sets, GC.GetAllocatedBytesForCurrentThread() - before

            for defined in [ true; false ] do
                selected (independent 64 defined) |> ignore
                let smallSets, smallBytes = selected (independent 1000 defined)
                let largeSets, largeBytes = selected (independent 8000 defined)
                let expected count = if defined then 0 else count
                Expect.equal smallSets.Length (expected 1000) $"Sets for 1,000 (defined={defined})."
                Expect.equal largeSets.Length (expected 8000) $"Sets for 8,000 (defined={defined})."

                Expect.isLessThan
                    largeBytes
                    (12L * smallBytes)
                    $"Eight times the branches allocates about eight times as much (defined={defined})."
        }

        for expression in
            [
                "A&&B"
                "A||B"
                "A==B"
                "A!=B"
                "(A&&B)||!C"
                "A&&(B||!C)"
                "!(A||B)"
                "!!A"
                "true&&A"
                "A==!B"
                "Á"
                "Á&&B"
                "A‿B||C"
                "A\\u0042&&B"
                "\\u0041||B"
                "A_1&&B"
                "A‍&&!A||B"
                "A\\u0042&&!AB||C"
                "!A||(B)&&C"
                "!A||B&&C"
                "A&&B||!A&&C"
                "A==B&&C"
                "A||B==C"
            ] do
            test ($"compact directive preserves both branches / {expression}") {
                let source = $"#if {expression}\nclass Yes{{}}\n#else\nclass No{{}}\n#endif\n"
                let expected = $"#if {expression}\nclass Yes {{ }}\n#else\nclass No {{ }}\n#endif\n"
                let actual = printSyntax source PrinterOptions.Default
                Expect.equal actual expected "Format both branches without changing the expression."

                Expect.equal
                    (printSyntax actual PrinterOptions.Default)
                    actual
                    "Directive is idempotent."
            }

        test "arguments after a multiline interpolation hole fit its last line" {
            let options =
                { PrinterOptions.Default with
                    Width = 40
                }

            let literal = "$\"value is {a\n+ bbbbbbbbbbbbbbbb}\""

            for arguments, expected in
                [
                    "two", "        Build(prefix, " + literal + ", two);\n"
                    "twoooooooooooooooooooooo",
                    "        Build(\n            prefix,\n            "
                    + literal
                    + ",\n            twoooooooooooooooooooooo\n        );\n"
                ] do
                let source =
                    "class C { void M() { Build(prefix, " + literal + ", " + arguments + "); } }"

                let actual = printSyntax source options

                Expect.equal
                    actual
                    ("class C\n{\n    void M()\n    {\n" + expected + "    }\n}\n")
                    "Arguments are measured against the width the hole's last line leaves."

                Expect.equal (printSyntax actual options) actual "Layout is idempotent."

                TokenPreservation.Checker().Check(options, "multiline-hole.cs", source, actual)
                |> function
                    | Ok() -> ()
                    | Error error -> failtest error
        }

        test "a group after a comment is measured from the comment's end" {
            let nested =
                "class C { void M() { Call(aaaaaaaaaaaaaaaaaaaaaaaaaaaaa,\n"
                + "/* lead */ Inner(aa, bb), cccc); } }"

            let hole = "class C { void M() { Call($\"{x /* cc */}\" + Other(bbb, ccc), dd); } }"

            for width, source, expected in
                [
                    30,
                    nested,
                    "        Call(\n            aaaaaaaaaaaaaaaaaaaaaaaaaaaaa,\n"
                    + "            /* lead */Inner(\n                aa,\n                bb\n"
                    + "            ),\n            cccc\n        );\n"
                    45,
                    nested,
                    "        Call(\n            aaaaaaaaaaaaaaaaaaaaaaaaaaaaa,\n"
                    + "            /* lead */Inner(aa, bb),\n            cccc\n        );\n"
                    35,
                    hole,
                    "        Call(\n            $\"{x /* cc */}\"\n"
                    + "                + Other(bbb, ccc),\n            dd\n        );\n"
                    60, hole, "        Call($\"{x /* cc */}\" + Other(bbb, ccc), dd);\n"
                ] do
                let options =
                    { PrinterOptions.Default with
                        Width = width
                    }

                let actual = printSyntax source options

                Expect.equal
                    actual
                    ("class C\n{\n    void M()\n    {\n" + expected + "    }\n}\n")
                    "What follows a comment is measured from the column it leaves."

                Expect.equal (printSyntax actual options) actual "Layout is idempotent."

                TokenPreservation.Checker().Check(options, "comment-column.cs", source, actual)
                |> function
                    | Ok() -> ()
                    | Error error -> failtest error
        }

        for name, literal in
            [
                "ordinary", "$\"{\n1\n}\""
                "verbatim", "$@\"{\n1\n}\""
                "raw", "$$\"\"\"\n{{\n1\n}}\n\"\"\""
            ] do
            for comment in [ "/* keep */"; "// keep\n" ] do
                test (
                    $"multiline interpolation preserves exterior comment / {name} / {comment.Trim()}"
                ) {
                    let source = "class C { void M() { var s = " + literal + " " + comment + "; } }"
                    let actual = printSyntax source PrinterOptions.Default
                    Expect.stringContains actual (comment.Trim()) "Exterior comment must survive."

                    Expect.equal
                        (actual.Split([| comment.Trim() |], StringSplitOptions.None).Length)
                        2
                        "Emit exterior trivia exactly once."

                    TokenPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "interpolation-comment.cs", source, actual)
                    |> function
                        | Ok() -> ()
                        | Error error -> failtest error

                    Expect.equal
                        (printSyntax actual PrinterOptions.Default)
                        actual
                        "Comment is idempotent."
                }
    ]

let private corpusRegressions =
    [
        test "corpus patterns keep every token" {
            let checker = TokenPreservation.Checker()

            for source in
                [
                    "class C { void M() { Debug.Assert(_operation != null && _currentSlot is >= 0 and not int.MaxValue && _currentIndex is >= 0 and not int.MaxValue); } }"
                    "class C { bool M(object a) => a is B * 2; bool N(object a) => a is B * c; }"
                    "class C { string M(float v) => v switch { float.NaN => \"NaN\", float.PositiveInfinity => \"inf\", _ => \"\" }; }"
                    "class C { bool M(object o) => o is { Name: nameof(string.Remove) } || o is nameof(A.B) or nameof(C.D); }"
                    "class C { bool M(object a) => a is bool when && when; bool N(long id) => id is corruptedTx + 1 or corruptedTx + 2; }"
                    "class C { bool M(object a) => a is not (string?, string?)[] accessors; }"
                    "class C { bool M(ParseResult r, Option o) => r.GetResult(o) is OptionResult or && !or.Implicit; }"
                    "class C { string M(int n) => $\"Discovered a total of {n::#,#;00} faulted pages.\"; }"
                    "class C { void M() { outer: for (;;) { for (;;) { continue outer; break outer; } } } }"
                    "public closed class C { public static extern safe double Acos(double d); public safe uint S; internal static safe partial int M(); }"
                    "enum E\n{\n    A,\n    // csff-ignore-start\n    B = 2, C = 3,\n    // csff-ignore-end\n    D,\n    E,\n}\n"
                    "#if true\nextern alias E;\nusing B;\n#endif\nusing A;\nclass D{}\n"
                    "#if true\nnamespace N;\nusing B;\n#endif\nusing A;\nclass D{}\n"
                    "#if true\nextern alias E;\nusing Z;\n#endif\nusing A;\nclass D{}\n"
                    "#if DEBUGX\nextern alias E;\nusing Z;\n#endif\nusing A;\nclass D{}\n"
                    "#if A\nextern alias E;\n#if B\nusing Z;\n#endif\nusing Y;\n#endif\nusing A;\nclass D{}\n"
                    "using N./*a b*/T;\nusing N./*a  b*/T;\nusing N./*a   b*/T;\nusing N./*a    b*/T;\nusing N./*a     b*/T;\nusing N./*a      b*/T;\nusing N./*a       b*/T;\nusing N./*a        b*/T;\nusing N./*a         b*/T;\nusing N./*a          b*/T;\nusing N./*a           b*/T;\nusing N./*a            b*/T;\nusing N./*a             b*/T;\nusing N./*a              b*/T;\nusing N./*a               b*/T;\nusing N./*a                b*/T;\nusing N./*a                 b*/T;\nusing N./*a                  b*/T;\nusing N./*a                   b*/T;\nusing N./*a                    b*/T;\nclass C { void M() { } }\n"
                    "using Foo=System.Int32;\nusing foo =System.String;\nclass C { void M() { } }\n"
                    "using foo=System.String;\nusing Foo =System.Int32;\nclass C { void M() { } }\n"
                    "class C\n{\n    // csff-ignore-start\n    const string S = @\"a   \nb\";\n    // csff-ignore-end\n    void M() { }\n}\n"
                ] do
                for _, options in OutputConfigurations.all do
                    let formatted = printSyntax source options

                    Expect.equal
                        (checker.Check(options, "regression.cs", source, formatted))
                        (Ok())
                        $"Every token of {source} survives."

                    Expect.equal
                        (printSyntax formatted options)
                        formatted
                        "The layout is idempotent."
        }
        test "precomputed flat group widths skip subtrees in O(1) during Fits" {
            let source = "alpha beta"
            use printer = new Printer()

            let buildNested count (d: DocumentBuffer) =
                let rec loop remaining =
                    let id = d.StartGroup()
                    text d source "alpha"
                    d.AddLine LineKind.Normal

                    if remaining > 1 then
                        d.AddTag Tag.StartIndent
                        loop (remaining - 1)
                        d.AddTag Tag.EndIndent
                    else
                        text d source "beta"

                    ifBreak d id (fun () -> d.AddToken StaticToken.Comma) ignore
                    d.EndGroup()

                loop count

            use smallDoc = new DocumentBuffer()
            use largeDoc = new DocumentBuffer()
            buildNested 8 smallDoc
            buildNested 128 largeDoc

            let narrow =
                { PrinterOptions.Default with
                    Width = 20
                }

            printer.Print(source, smallDoc, narrow)
            let smallWorkPerCall = float printer.FitWork / float printer.FitCalls

            printer.Print(source, largeDoc, narrow)
            let largeWorkPerCall = float printer.FitWork / float printer.FitCalls

            Expect.isLessThanOrEqual
                largeWorkPerCall
                (smallWorkPerCall + 1.0)
                "Flat-summarizable nested groups are measured in O(1) FitWork per Fits call."

            let actual =
                print
                    source
                    { PrinterOptions.Default with
                        Width = 40
                    }
                    (fun d ->
                        let mutable innerId = -1

                        group d (fun () ->
                            group d (fun () ->
                                innerId <-
                                    group d (fun () ->
                                        text d source "alpha"
                                        d.AddLine LineKind.Normal
                                        text d source "beta"))
                            |> ignore

                            d.AddLine LineKind.Normal

                            ifBreak d innerId (fun () -> text d source "beta") (fun () ->
                                text d source "alpha"))
                        |> ignore)

            Expect.equal actual "alpha beta alpha\n" "External IfBreak sees flat inner group mode."

            use deepExternalDoc = new DocumentBuffer()

            let rec buildExternalChain remaining =
                group deepExternalDoc (fun () ->
                    if remaining > 1 then
                        let childId = buildExternalChain (remaining - 1)

                        ifBreak
                            deepExternalDoc
                            childId
                            (fun () -> text deepExternalDoc source "beta")
                            ignore
                    else
                        text deepExternalDoc source "alpha")

            buildExternalChain 256 |> ignore

            printer.Print(
                source,
                deepExternalDoc,
                { PrinterOptions.Default with
                    Width = 40
                }
            )

            Expect.equal
                printer.OutputText
                "alpha\n"
                "Nested external IfBreak chain preserves child flat modes."
        }
        test "single-pass measureLastLine matches lastLine and multiline detection across lengths" {
            let samples =
                [
                    ""
                    "a"
                    "\t"
                    "\u000e"
                    "\u10ff"
                    "\u1100"
                    "abc\ndef"
                    "abc\rdef"
                    "abc\r\ndef"
                    "abc\n"
                    "\rあ"
                    "あいうえお"
                    "0123456789abcdef"
                    "0123456789abcdefg"
                    "0123456789abcdef\nあいう"
                    "0123456789abcdefg\r\nあいうえお0123456789abcdef"
                    String.replicate 32 "x"
                    String.replicate 10 "あx"
                    String.replicate 20 "line\n" + "tailあ"
                ]

            for sample in samples do
                let struct (width, multiline) = PrintedWidth.measureLastLine (sample.AsSpan())
                let expectedMultiline = sample.AsSpan().IndexOfAny('\r', '\n') >= 0
                let last = sample.AsSpan().LastIndexOfAny('\r', '\n')
                let start = last + 1
                let mutable expectedWidth = uint32 (sample.Length - start)

                for i = start to sample.Length - 1 do
                    if sample[i] >= '\u1100' then
                        expectedWidth <- expectedWidth + PrintedWidth.character sample[i] - 1u

                Expect.equal
                    multiline
                    expectedMultiline
                    $"Multiline flag for {sample.Length}-char sample."

                Expect.equal width expectedWidth $"Last-line width for {sample.Length}-char sample."

                Expect.equal
                    (PrintedWidth.lastLine (sample.AsSpan()))
                    expectedWidth
                    "lastLine matches."
        }
        test "reused printer prepares tag-scoped ends, elses, and breaks without stale state" {
            let source = "alpha beta"
            use printer = new Printer()
            use d = new DocumentBuffer()

            group d (fun () ->
                d.AddTag(Tag.StartIfBreak, -1)
                text d source "alpha"
                d.AddTag Tag.Else
                text d source "beta"
                d.AddTag Tag.EndIfBreak
                d.AddLine LineKind.Hard)
            |> ignore

            printer.Print(source, d, PrinterOptions.Default)

            Expect.equal printer.OutputText "alpha\n" "Broken group selects broken IfBreak branch."

            d.Reset()

            group d (fun () ->
                d.AddTag(Tag.StartIfBreak, -1)
                let sharedStart = d.Count
                text d source "alpha"
                d.AddLine LineKind.Normal
                text d source "beta"
                let sharedLength = d.Count - sharedStart
                d.AddTag Tag.EndIfBreak
                d.AddShared(sharedStart, sharedLength))
            |> ignore

            printer.Print(source, d, PrinterOptions.Default)

            Expect.equal
                printer.OutputText
                "alpha beta\n"
                "No stale Else, break, or end index leaks."
        }
        test "reused SyntaxNodePrinter and SyntaxTree.IsComplete track completeness and lazy state" {
            let tree = SyntaxTree()
            Parser.parse "class C { int[] A = new int[]; Type T = typeof(List<>); }" tree

            Expect.isTrue
                tree.IsComplete
                "Omitted array size and type argument tokens stay complete."

            Expect.isTrue (SyntaxFacts.complete tree) "SyntaxFacts.complete agrees."

            Parser.parse "class C { void M() { int x = " tree
            Expect.isFalse tree.IsComplete "Missing token marks tree incomplete."
            Expect.isFalse (SyntaxFacts.complete tree) "SyntaxFacts.complete agrees."

            Parser.parse "class C { public }" tree
            Expect.isFalse tree.IsComplete "IncompleteMember marks tree incomplete."

            use builder = new SyntaxDocumentBuilder()
            use d = new DocumentBuffer()
            use printer = new Printer()

            let inputs =
                [
                    "#if DEBUG\n// csff-ignore\nclass   A   {   int  x = 1; }\n#else\nclass B{}\n#endif\n"
                    "class Plain{int x=1;int y=2;}\n"
                    "class Ignored{\n// csff-ignore-start\nint   a  =  1;\n// csff-ignore-end\nint b=2;}\n"
                    "class PlainTwo{void M(){var f = (int x) => x + 1;}}\n"
                ]

            for source in inputs do
                Parser.parse source tree
                d.Reset()
                builder.Build(source, tree, d, PrinterOptions.Default)
                printer.Print(source, d, PrinterOptions.Default)
                let reused = printer.OutputText
                let fresh = printSyntax source PrinterOptions.Default
                Expect.equal reused fresh "Reused builder matches fresh printSyntax."
        }
        test
            "conditional files with only closed single-line strings skip literal ownership tracking" {
            let tree = SyntaxTree()
            let scratch = Csff.Lexer.TokenBuffer()

            let singleLineConditional =
                "/// <summary name=\"doc\">\n"
                + "#if FOO\n"
                + "class C { string A = \"alpha\"; ReadOnlySpan<byte> B => \"beta\"u8; string V = @\"gamma\"; }\n"
                + "#else\n"
                + "// comment with \"quote\"\n"
                + "class C { string A = \"delta\"; ReadOnlySpan<byte> B => \"epsilon\"u8; string V = @\"zeta\"; }\n"
                + "#endif\n"

            Parser.parse singleLineConditional tree

            let struct (_, sets, independent, discovery) =
                Preprocessor.symbolSetsWithInitial singleLineConditional tree (ValueSome scratch)

            Expect.isNonEmpty sets "Conditional sets exist."

            Expect.isFalse
                (SyntaxFacts.literalOwnershipNeeded
                    singleLineConditional
                    tree
                    tree.IsComplete
                    false
                    discovery
                    (ValueSome scratch))
                "Single-line strings and line-comment quotes do not need literal ownership."

            Expect.isFalse
                (SyntaxFacts.literalOwnershipNeeded
                    singleLineConditional
                    tree
                    tree.IsComplete
                    independent
                    discovery
                    (ValueSome scratch))
                "Independent regions do not need literal ownership."

            for multilineConditional in
                [
                    "#if FOO\nclass C { string S = \"\"\"\nhello\n\"\"\"; }\n#endif\n"
                    "#if FOO\nclass C { string S = @\"hello\nworld\"; }\n#endif\n"
                    "#if FOO\nclass C { string S = $\"{1}\"; }\n#endif\n"
                    "#if FOO\n/* \" */\nclass C { }\n#endif\n"
                ] do
                Parser.parse multilineConditional tree

                let struct (_, _, _, neededDiscovery) =
                    Preprocessor.symbolSetsWithInitial multilineConditional tree (ValueSome scratch)

                Expect.isTrue
                    (SyntaxFacts.literalOwnershipNeeded
                        multilineConditional
                        tree
                        tree.IsComplete
                        false
                        neededDiscovery
                        (ValueSome scratch))
                    "Multiline, interpolated, or block-comment quotes keep literal ownership."

            let formatted = printSyntax singleLineConditional PrinterOptions.Default

            Expect.equal
                (printSyntax formatted PrinterOptions.Default)
                formatted
                "Formatted single-line conditional remains idempotent."

            let fallbackSource =
                "#if !A\n"
                + "class C { string S = @\"\n"
                + "    #endif\n"
                + "    #if A\n"
                + "class D { }\n"
                + "    #endif\n"
                + "    #if !A\n"
                + "\"; }\n"
                + "#endif\n"

            Parser.parseWith [| "A" |] fallbackSource tree
            use builder = new SyntaxDocumentBuilder()
            use d = new DocumentBuffer()
            use printer = new Printer()
            builder.Build(fallbackSource, tree, d, PrinterOptions.Default)
            printer.Print(fallbackSource, d, PrinterOptions.Default)
            let fallbackFormatted = printer.OutputText

            match
                SyntaxPreservation
                    .Checker()
                    .Check(PrinterOptions.Default, "fallback.cs", fallbackSource, fallbackFormatted)
            with
            | Ok() -> ()
            | Error message -> failtest message
        }
    ]

let private longGreaterThanRuns =
    [
        test "a > run of four or more closes its lists and leaves one operator" {
            let errors (text: string) =
                CSharpSyntaxTree
                    .ParseText(text, CSharpParseOptions(LanguageVersion.Preview))
                    .GetDiagnostics()
                |> Seq.filter (fun d ->
                    d.Severity = Microsoft.CodeAnalysis.DiagnosticSeverity.Error)
                |> Seq.length

            for source, expected in
                [
                    "class C{unsafe void M(){A<int>>>>=1;}}", "A<int> >>>= 1;"
                    "class C{void M(){A<B<C<D<int>>>>();}}", "A<B<C<D<int>>>>();"
                    "class C{void M(){A<int>>>=1;}}", "A<int> >>= 1;"
                    "class C{void M(){A<B<C>>>=1;}}", "A<B<C>> >= 1;"
                    "class C{void M(int a){a>>>=1;}}", "a >>>= 1;"
                    "class C{void M(int a){a>>=1;}}", "a >>= 1;"
                    "class C{void M(){var v = new X{A<int>>>>=1};}}", "{ A<int> >>>= 1 }"
                ] do
                let formatted = printSyntax source PrinterOptions.Default

                Expect.equal (errors source) 0 $"The row must be valid C#: {source}"

                Expect.equal
                    (errors formatted)
                    0
                    $"The output must carry no error the input did not: {source}"

                Expect.stringContains formatted expected source

                Expect.equal
                    (SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "run.cs", source, formatted))
                    (Ok())
                    source
        }
        test "a > run too long for one operator is left as two, as C# leaves it" {
            let errors (text: string) =
                CSharpSyntaxTree
                    .ParseText(text, CSharpParseOptions(LanguageVersion.Preview))
                    .GetDiagnostics()
                |> Seq.filter (fun d ->
                    d.Severity = Microsoft.CodeAnalysis.DiagnosticSeverity.Error)
                |> Seq.length

            for source in
                [
                    "class C{unsafe void M(){A<int>>>>>=1;}}"
                    "class C{unsafe void M(){A<int>>>>>>=1;}}"
                ] do
                let formatted = printSyntax source PrinterOptions.Default

                Expect.isTrue (errors source > 0) $"The row does not compile: {source}"

                Expect.isTrue
                    (errors formatted <= errors source)
                    $"The output must carry no new error: {source}"
        }
    ]

let private repeatedLambdaModifiers =
    [
        test "a repeated lambda modifier is refused rather than written" {
            let errors (text: string) =
                CSharpSyntaxTree
                    .ParseText(text, CSharpParseOptions(LanguageVersion.Preview))
                    .GetDiagnostics()
                |> Seq.filter (fun d ->
                    d.Severity = Microsoft.CodeAnalysis.DiagnosticSeverity.Error)
                |> Seq.length

            for source, accepted in
                [
                    "var v = new X{A=static static int () => 1};", false
                    "var v = new X{A=static async static () => 1};", false
                    "class C{void M(){var v = new X{A=static static int () => 1};}}", false
                    "class C{void M(){var v = new X{A=static async static () => 1};}}", false
                    "var v = new X{A=static int () => 1};", true
                    "var v = new X{A=async static () => 1};", true
                    "class C{void M(){Func<int> f = static int () => 1;}}", true
                    "class C{void M(){Func<int> f = async () => 1;}}", true
                    "class C{void M(){Func<int> f = static static int () => 1;}}", true
                    "class C{void M(){Func<int> f = static async static () => 1;}}", true
                ] do
                let formatted = printSyntax source PrinterOptions.Default

                let verdict =
                    SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "modifier.cs", source, formatted)

                if accepted then
                    Expect.equal verdict (Ok()) source

                    Expect.isTrue
                        (errors formatted <= errors source)
                        $"The output must carry no new error: {source}"
                else
                    Expect.notEqual verdict (Ok()) $"This must be refused, not written: {source}"
        }
    ]

let private characterClassAgreement =
    [
        test "the preprocessor classifies every character as the lexer does" {
            let mismatches = ResizeArray<string>()

            for code = 0 to 0xFFFF do
                let ch = char code

                let check name (copy: char -> bool) (canonical: char -> bool) =
                    if copy ch <> canonical ch then
                        mismatches.Add
                            $"U+{code:X4} {name}: preprocessor {copy ch}, lexer {canonical ch}"

                check "newLine" Preprocessor.Classify.newLine Lexer.Classify.newLine
                check "whitespace" Preprocessor.Classify.whitespace Lexer.Classify.whitespace

                check
                    "identifierStart"
                    Preprocessor.Classify.identifierStart
                    Lexer.Classify.identifierStart

                check
                    "identifierPart"
                    Preprocessor.Classify.identifierPart
                    Lexer.Classify.identifierPart

            Expect.isEmpty
                mismatches
                ("The preprocessor's classification has drifted from the lexer's: "
                 + String.Join("; ", Seq.truncate 10 mismatches)
                 + ".")
        }
    ]

let tests =
    TestList(
        [
            testList
                "printer"
                (fixtures
                 @ properties
                 @ blockExteriorTriviaFixtures
                 @ trailingLambdaFixtures
                 @ commentBoundaryFixtures
                 @ expressionFixtures
                 @ statementFixtures
                 @ controlStatementSpacingFixtures
                 @ retiredMarkerFixtures
                 @ configurationFixtures
                 @ memberListFixtures
                 @ conditionalPassScaling
                 @ conditionalBatchFixtures
                 @ bareSwitchBodyFixtures
                 @ cleanRoomParityRegressions
                 @ conditionalArenaOrder
                 @ conditionalLexingRegressions
                 @ conditionalLexingScaling
                 @ conditionalPassSeams
                 @ conditionalWitnessSelection
                 @ conditionalWitnessBounds
                 @ conditionalWitnessRetry
                 @ conditionalSkippedText
                 @ triviaBlankLines
                 @ leadingCommentFit
                 @ solverReachabilityRegressions
                 @ anonymousMethodFixtures
                 @ preservationRegressions
                 @ lineCommentGuards
                 @ optionGuards
                 @ commentLineGuards
                 @ commentScaling
                 @ commentIndentFixtures
                 @ corpusRegressions
                 @ longGreaterThanRuns
                 @ repeatedLambdaModifiers
                 @ characterClassAgreement)
        ],
        Normal
    )
