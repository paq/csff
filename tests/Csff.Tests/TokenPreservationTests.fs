module Csff.Tests.TokenPreservationTests

open System
open System.IO
open Csff.Conformance
open Csff.Lexer
open Csff.Parser
open Csff.Printer
open Expecto

let private expectOk result =
    match result with
    | Ok() -> ()
    | Error message -> failtest message

let private expectFailure fragments result =
    let message = Expect.wantError result "An undeclared token change must fail."

    for fragment in fragments do
        Expect.stringContains message fragment "Locate and explain the token change."

let private expectRefusedAndDiagnosedOrNot
    (verifier: SyntaxPreservation.Checker)
    (name: string)
    (source: string)
    (formatted: string)
    =
    let refusal =
        Expect.wantError
            (verifier.Check(PrinterOptions.Default, name, source, formatted))
            $"The CLI must refuse this output: {formatted}"

    match verifier.Adjudicate(PrinterOptions.Default, name, source, formatted) with
    | Error message ->
        Expect.stringContains
            message
            "formatting changed a preprocessor directive line"
            $"The only comparison left that names a defect is the directive line: {message}"
    | Ok() ->
        Expect.stringStarts
            refusal
            "unprovable:"
            $"A pair no comparison names is refused as unproven: {refusal}"

let private verdict (verification: SyntaxPreservation.Verification) =
    match verification with
    | SyntaxPreservation.Verification.Proven -> "proven"
    | SyntaxPreservation.Verification.Violation _ -> "violation"
    | SyntaxPreservation.Verification.Unprovable _ -> "unprovable"

let private format options source =
    let tree = SyntaxTree()
    use document = new DocumentBuffer()
    use printer = new Printer()
    Parser.parse source tree
    SyntaxPrinter.build source tree document options
    printer.Print(source, document, options)
    printer.OutputText

let private printWithWitness (options: PrinterOptions) (source: string) =
    let tree = SyntaxTree()
    use builder = new SyntaxDocumentBuilder()
    use document = new DocumentBuffer()
    use printer = new Printer()
    Parser.parse source tree
    builder.Build(source, tree, document, options)
    printer.Print(source, document, options)
    struct (printer.OutputText, builder.Transformations)

let private tokenCount text =
    let tree = SyntaxTree()
    Parser.parse text tree
    tree.TokenCount

let private allocated action =
    for _ = 1 to 100 do
        action ()

    let start = GC.GetAllocatedBytesForCurrentThread()

    for _ = 1 to 100 do
        action ()

    GC.GetAllocatedBytesForCurrentThread() - start

let private comments (text: string) =
    let tree = SyntaxTree()
    Parser.parse text tree
    let buffer = tree.LexerBuffer

    [
        for index in 0 .. buffer.TriviaCount - 1 do
            let item = buffer.Trivia index

            match item.Kind with
            | TriviaKind.SingleLineCommentTrivia
            | TriviaKind.MultiLineCommentTrivia
            | TriviaKind.SingleLineDocumentationCommentTrivia
            | TriviaKind.MultiLineDocumentationCommentTrivia ->
                yield text.Substring(item.Start, item.Length)
            | _ -> ()
    ]

let private replaceOnce (find: string) (replace: string) (text: string) =
    let first = text.IndexOf(find, StringComparison.Ordinal)
    Expect.isTrue (first >= 0) ("The marker must occur: " + find)

    Expect.isTrue
        (text.IndexOf(find, first + 1, StringComparison.Ordinal) < 0)
        ("The marker must occur once: " + find)

    text.Remove(first, find.Length).Insert(first, replace)

let private csharp (text: string) =
    let trimmed = text.Replace("\r\n", "\n").TrimStart('\n')

    if trimmed.EndsWith("\n", StringComparison.Ordinal) then
        trimmed
    else
        trimmed + "\n"

let private commentShapes =
    csharp
        """
// first line
using System;
// between the using and its declaration
class C
{
// one
// two
/// <summary>doc first</summary>
/// <remarks>doc second</remarks>
void M()
{
if (true)
{
/* block
   interior
     deeper */
Use(/* a */ /* b */ 1);
}
}
/** doc block
  * second
  */
int A;
}
// last line
"""

let private commentedUsings =
    csharp
        """
using Zebra; // zebra
// about alpha
using Alpha;

class C { }
"""

let private commentedModifiers =
    csharp
        """
unsafe // area
       // title
public class UC
{
    public int* p;
}
"""

let private lineEndings =
    [ "lf", EndOfLine.Lf; "crlf", EndOfLine.CrLf; "cr", EndOfLine.Cr ]

let private multiLineComments =
    csharp
        """
class C
{
/// <summary>first</summary>
/// <remarks>second</remarks>
/// <returns>third</returns>
int A;
/* block one
   interior
     deeper */
int B;
/** doc block
  * second
  */
int D;
// plain
}
"""

let private configurations = OutputConfigurations.all

let private ignoredRegions (text: string) =
    let marker = "// csff-ignore-end"

    List.unfold
        (fun (from: int) ->
            let start = text.IndexOf("// csff-ignore-start", from, StringComparison.Ordinal)

            if start < 0 then
                None
            else
                let finish = text.IndexOf(marker, start, StringComparison.Ordinal) + marker.Length
                Some(text.Substring(start, finish - start), finish))
        0

let conditionalUsingLayouts =
    [
        "define prefix",
        "#define OTHER\n#if !X\nusing Z;\n#endif\nusing A;\nclass D{}\n",
        "#define OTHER\n#if !X\nusing Z;\n#endif\nusing A;\n\nclass D { }\n"
        "undef prefix",
        "#undef OTHER\n#if !X\nusing Z;\n#endif\nusing A;\nclass D{}\n",
        "#undef OTHER\n#if !X\nusing Z;\n#endif\nusing A;\n\nclass D { }\n"
    ]

let private activeUsingNames (symbols: string array) (source: string) =
    let options =
        Microsoft.CodeAnalysis.CSharp
            .CSharpParseOptions(Microsoft.CodeAnalysis.CSharp.LanguageVersion.Preview)
            .WithPreprocessorSymbols(symbols)

    let parsed =
        Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree.ParseText(source, options)

    Expect.isEmpty
        (parsed.GetDiagnostics()
         |> Seq.filter (fun diagnostic ->
             diagnostic.Severity = Microsoft.CodeAnalysis.DiagnosticSeverity.Error))
        $"Directives stay syntactically valid for symbols {symbols}."

    parsed.GetRoot().DescendantNodes()
    |> Seq.choose (function
        | :? Microsoft.CodeAnalysis.CSharp.Syntax.UsingDirectiveSyntax as node ->
            Some(node.Name.ToString())
        | _ -> None)
    |> Seq.sort
    |> Seq.toList

let private preservation =
    testList
        "token preservation"
        [
            test
                "interpolation directives are refused while surrounding directives keep source order" {
                let illegalHoleDirective =
                    "class C { string M() => $\"{\n#pragma warning disable CS1\n1 + 2}\"; }\n#pragma warning restore CS1\n"

                let movedHoleDirective =
                    "class C { string M() => $\"{1 +\n#pragma warning disable CS1\n2}\"; }\n#pragma warning restore CS1\n"

                let checker = TokenPreservation.Checker()

                checker.Normalize(PrinterOptions.Default, illegalHoleDirective, movedHoleDirective)
                |> ignore

                Expect.isFalse
                    (checker.FastEquivalent(illegalHoleDirective, movedHoleDirective))
                    "Illegal directives inside interpolation holes are never accepted by fast equivalence."

                let sameIllegal = illegalHoleDirective.Replace("1 + 2", "1  +  2")

                checker.Normalize(PrinterOptions.Default, illegalHoleDirective, sameIllegal)
                |> ignore

                Expect.isFalse
                    (checker.FastEquivalent(illegalHoleDirective, sameIllegal))
                    "Directives inside interpolation holes produce BadToken '#' and invalid syntax."

                let source =
                    "#pragma warning disable CS1\nclass C { string M() => $\"{1 + 2}\"; }\n#pragma warning restore CS1\n"

                let reordered =
                    "#pragma warning restore CS1\nclass C { string M() => $\"{1 + 2}\"; }\n#pragma warning disable CS1\n"

                checker.Normalize(PrinterOptions.Default, source, reordered) |> ignore

                Expect.isFalse
                    (checker.FastEquivalent(source, reordered))
                    "Reordering directives around an interpolated string must be rejected."

                let same = source.Replace("1 + 2", "1  +  2")
                checker.Normalize(PrinterOptions.Default, source, same) |> ignore

                Expect.isTrue
                    (checker.FastEquivalent(source, same))
                    "Whitespace inside valid hole is equivalent."
            }
            test "fast equivalence validates block comments and directives without Roslyn" {
                let checker = TokenPreservation.Checker()

                let source =
                    "#define FEATURE\n#nullable enable\n#region Don't touch\n/* block comment */\n/** <summary>doc</summary> */\n#if FEATURE // \"quoted\" comment\nclass C {\n#pragma warning disable CS0168 // don't warn\nint x;\n}\n#endif // !FEATURE's end\n#endregion // \"done\"\n"

                let formatted =
                    "#define FEATURE\n#nullable enable\n#region Don't touch\n/* block comment */\n/** <summary>doc</summary> */\n#if FEATURE // \"quoted\" comment\nclass C\n{\n#pragma warning disable CS0168 // don't warn\n    int x;\n}\n#endif // !FEATURE's end\n#endregion // \"done\"\n"

                checker.Normalize(PrinterOptions.Default, source, formatted) |> ignore

                Expect.isTrue
                    (checker.FastEquivalent(source, formatted))
                    "Clean block comments, doc comments, and commented directives must succeed on the fast path."

                Expect.equal
                    (allocated (fun () -> checker.FastEquivalent(source, formatted) |> ignore))
                    0L
                    "FastEquivalent must not allocate strings when comparing directives."

                let shebangSource = "#!/usr/bin/env dotnet\nclass C {\nint x;\n}\n"
                let shebangFormatted = "#!/usr/bin/env dotnet\nclass C\n{\n    int x;\n}\n"

                checker.Normalize(PrinterOptions.Default, shebangSource, shebangFormatted)
                |> ignore

                Expect.isTrue
                    (checker.FastEquivalent(shebangSource, shebangFormatted))
                    "A leading shebang at offset zero must settle on the fast path."

                for invalid in
                    [
                        "class C { } /* unclosed * /\n"
                        "class C { } /*/"
                        "class C { } /** unclosed * /\n"
                        "class C { } /**"
                        "/** doc */ #if FOO\nclass C { }\n#endif\n"
                        "class C { } #region R\n#endregion\n"
                        "class C { string M() => $\"{1\n#pragma warning disable CS1}\"; }\n"
                        "class C { }\n#define LATE\n"
                        "#if X /* block comment on directive */\nclass C { }\n#endif\n"
                        "#if \"a \nclass C { }\n#endif\n"
                        "\n#!/usr/bin/env dotnet\nclass C { }\n"
                    ] do
                    checker.Normalize(PrinterOptions.Default, invalid, invalid) |> ignore

                    Expect.isFalse
                        (checker.FastEquivalent(invalid, invalid))
                        $"Sensitivity check must fall back to Roslyn for: {invalid}"

                let openLine = "#line 1 \"a \nclass C { }\n"
                checker.Normalize(PrinterOptions.Default, openLine, openLine) |> ignore

                Expect.isTrue
                    (checker.FastEquivalent(openLine, openLine))
                    "An open #line string repeated exactly is the same directive."

                let trimmedLine = "#line 1 \"a\nclass C { }\n"
                checker.Normalize(PrinterOptions.Default, openLine, trimmedLine) |> ignore

                Expect.isFalse
                    (checker.FastEquivalent(openLine, trimmedLine))
                    "Dropping the blank an open #line string ends with changes its file name."
            }
            test "fast equivalence compares payload-carrying directives without Roslyn" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                let source =
                    "#line 42\n#error legacy path\n#warning obsolete member\nclass C {\nint x;\n}\n"

                let formatted =
                    "#line 42\n#error legacy path\n#warning obsolete member\nclass C\n{\n    int x;\n}\n"

                checker.Normalize(PrinterOptions.Default, source, formatted) |> ignore

                Expect.isTrue
                    (checker.FastEquivalent(source, formatted))
                    "A message or line directive the output repeats verbatim must settle without Roslyn."

                verifier.Check(PrinterOptions.Default, "payload.cs", source, formatted)
                |> expectOk

                verifier.Adjudicate(PrinterOptions.Default, "payload.cs", source, formatted)
                |> expectOk

                for changed in
                    [
                        formatted.Replace("#error legacy path", "#error legacy paths")
                        formatted.Replace("#error legacy path", "#warning legacy path")
                        formatted.Replace("#line 42", "#line 43")
                        "#line 42\n#error legacy path\nclass C\n{\n    int x;\n#warning obsolete member\n}\n"
                    ] do
                    checker.Normalize(PrinterOptions.Default, source, changed) |> ignore

                    Expect.isFalse
                        (checker.FastEquivalent(source, changed))
                        $"A changed payload directive must not settle on the fast path: {changed}"

                    verifier.Check(PrinterOptions.Default, "payload.cs", source, changed)
                    |> expectFailure [ "payload.cs" ]

                    verifier.Adjudicate(PrinterOptions.Default, "payload.cs", source, changed)
                    |> expectFailure [ "payload.cs" ]

                for quoted, changed in
                    [
                        "#line 42 \"a.cs\"\nclass C {}\n", "#line 42 \"b.cs\"\nclass C { }\n"
                        "#error don't\nclass C {}\n", "#error dont\nclass C { }\n"
                        "#warning \"x  \nclass C {}\n", "#warning \"x\nclass C { }\n"
                    ] do
                    let same =
                        changed
                            .Replace("b.cs", "a.cs")
                            .Replace("dont", "don't")
                            .Replace("\"x\n", "\"x  \n")

                    checker.Normalize(PrinterOptions.Default, quoted, same) |> ignore

                    Expect.isTrue
                        (checker.FastEquivalent(quoted, same))
                        $"A quoted directive payload repeated verbatim must settle: {quoted}"

                    checker.Normalize(PrinterOptions.Default, quoted, changed) |> ignore

                    Expect.isFalse
                        (checker.FastEquivalent(quoted, changed))
                        $"A changed quoted payload must not settle: {changed}"
            }
            test "fast equivalence settles a using run sorted across a conditional frame" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source in
                    [
                        "#if MONO\nusing A;\n#endif\nusing B;\nclass C { }\n"
                        "using Z;\n#if MONO\nusing A;\n#endif\nusing B;\nclass C { }\n"
                        "#if MONO\nusing A;\n#else\nusing B;\n#endif\nusing C;\nclass D { }\n"
                        "#region R\n#endregion\nusing B;\nusing A;\nclass C { }\n"
                        "#if MONO\n#endif\nusing B;\nusing A;\nclass C { }\n"
                        "#if A\n#endif\n#if B\n#endif\nusing Z;\nusing Y;\nclass C { }\n"
                        "#if MONO\n#endif\nusing Z;\nusing Y;\n"
                        "#if MONO\nusing A;\n#endif\nusing B;\nclass C { string s = $\"{1 + 2}\"; }\n"
                        "#if MONO\nusing A;\n#endif\nusing B;\nclass C { string s = $\"{1}\"; }\n\n#pragma warning disable CS0168\n"
                        "namespace N\n{\n#if MONO\nusing Z;\n#endif\n    using Y;\n\n    class C { }\n}\n"
                        "#define A\nnamespace N;\n#if A\nusing Z;\n#endif\nusing Y;\nclass C { }\n"
                    ] do
                    let formatted = format PrinterOptions.Default source

                    Expect.isFalse
                        (checker.LexicallyPreserved(source, formatted))
                        $"The lexical proof must not be what settles this: {source}"

                    let expected = checker.Normalize(PrinterOptions.Default, source, formatted)

                    Expect.isTrue
                        (checker.FastEquivalent(expected, formatted))
                        $"A sorted using run must settle without Roslyn: {source}"

                    verifier.Check(PrinterOptions.Default, "using-frame.cs", source, formatted)
                    |> expectOk

                    verifier.Adjudicate(PrinterOptions.Default, "using-frame.cs", source, formatted)
                    |> expectOk
            }
            test "a frame out of an interpolation hole leaves the fast path" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "#if MONO\nusing A;\n#endif\nusing B;\nclass C { string s = $\"{1\n#if X\n+ 2\n#endif\n}\"; }\n"
                        "#if MONO\nusing A;\n#endif\nusing B;\nclass C { string s = $\"{1\n#region R\n+ 2\n#endregion\n}\"; }\n"
                    ] do
                    let formatted = format PrinterOptions.Default source
                    let expected = checker.Normalize(PrinterOptions.Default, source, formatted)

                    Expect.isFalse
                        (checker.FastEquivalent(expected, formatted))
                        $"A frame inside an interpolation hole must fall back: {source}"
            }
            test "a using run permutes within one frame, however deep" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source, sorted in
                    [
                        "#define A\n#define B\n#if A\n#if B\nusing Z;\nusing Y;\n#endif\n#endif\nclass C { }\n",
                        "#define A\n#define B\n#if A\n#if B\nusing Y;\nusing Z;\n#endif\n#endif\nclass C { }\n"
                        "#if MONO\n#else\nusing Z;\nusing Y;\n#endif\nclass C { }\n",
                        "#if MONO\n#else\nusing Y;\nusing Z;\n#endif\nclass C { }\n"
                        "namespace N\n{\n#if A\n    using Z;\n    using Y;\n#endif\n\n    class C { }\n}\n",
                        "namespace N\n{\n#if A\n    using Y;\n    using Z;\n#endif\n\n    class C { }\n}\n"
                    ] do
                    let expected = checker.Normalize(PrinterOptions.Default, source, sorted)

                    Expect.isTrue
                        (checker.FastEquivalent(expected, sorted))
                        $"A permutation inside one frame must settle: {sorted}"

                    verifier.Adjudicate(PrinterOptions.Default, "nested-frame.cs", source, sorted)
                    |> expectOk
            }
            test "a using keeps the frame and the context segment it was written in" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source, changed in
                    [
                        "#define MONO\nusing A;\n#if MONO\nclass C { }\n#endif\n",
                        "#define MONO\n#if MONO\nusing A;\nclass C { }\n#endif\n"
                        "#if MONO\n#else\nusing A;\n#endif\nusing B;\nclass C { }\n",
                        "using A;\nusing B;\n#if MONO\n#else\n#endif\nclass C { }\n"
                        "#nullable enable\nusing A;\nclass C { }\n",
                        "using A;\n#nullable enable\nclass C { }\n"
                        "#define LATE\nusing A;\nclass C { }\n",
                        "using A;\n#define LATE\nclass C { }\n"
                        "#define MONO\n#if MONO\nusing A;\n#endif\n#if MONO\nusing B;\n#endif\nclass C { }\n",
                        "#define MONO\n#if MONO\nusing B;\n#endif\n#if MONO\nusing A;\n#endif\nclass C { }\n"
                        "#define A\n#define B\n#if A\n#if B\nusing X;\n#endif\nusing Y;\n#endif\nclass C { }\n",
                        "#define A\n#define B\n#if A\n#if B\nusing Y;\n#endif\nusing X;\n#endif\nclass C { }\n"
                        "#define A\n#if A\nusing X;\n#endif\nnamespace N\n{\n    using Y;\n\n    class C { }\n}\n",
                        "#define A\n#if A\nusing X;\nusing Y;\n#endif\nnamespace N\n{\n    class C { }\n}\n"
                        "#define MONO\n#if MONO\nusing A;\n#endif\nusing B;\nclass C { }\n",
                        "#define MONO\nusing C;\n#if MONO\nusing A;\n#endif\nclass C { }\n"
                        "#define MONO\nusing A;\nclass C { }\n#if MONO\nclass D { }\n#endif\n",
                        "#define MONO\nusing A;\n#if MONO\nclass C { }\nclass D { }\n#endif\n"
                    ] do
                    let expected = checker.Normalize(PrinterOptions.Default, source, changed)

                    Expect.isFalse
                        (checker.FastEquivalent(expected, changed))
                        $"An import that changed its directive context must not settle: {changed}"

                    expectRefusedAndDiagnosedOrNot verifier "using-frame.cs" source changed
            }
            test "a sorted using run hides no other change to the file" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source, changed in
                    [
                        "#nullable enable\nusing A;\nusing A;\nusing B;\nclass C { }\n",
                        "#nullable enable\nusing A;\nusing B;\nclass C { }\n"
                        "#nullable enable\nusing B;\nnamespace N\n{\n    using A;\n\n    class C { }\n}\n",
                        "#nullable enable\nusing A;\nusing B;\nnamespace N\n{\n    class C { }\n}\n"
                        "#nullable enable\nusing B;\nusing A;\nclass C { string s = \"x\"; }\n",
                        "#nullable enable\nusing A;\nusing B;\n\nclass C\n{\n    string s = \"y\";\n}\n"
                    ] do
                    let expected = checker.Normalize(PrinterOptions.Default, source, changed)

                    Expect.isFalse
                        (checker.FastEquivalent(expected, changed))
                        $"A sorted run must not carry another change with it: {changed}"

                    verifier.Check(PrinterOptions.Default, "sorted-run.cs", source, changed)
                    |> expectFailure [ "sorted-run.cs" ]
            }
            test "only a plain import is paired with another" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source, reordered in
                    [
                        "#nullable enable\nusing Z;\nusing int;\nclass C { }\n",
                        "#nullable enable\nusing int;\nusing Z;\nclass C { }\n"
                        "#nullable enable\nusing Z;\nusing ref int;\nclass C { }\n",
                        "#nullable enable\nusing ref int;\nusing Z;\nclass C { }\n"
                        "#nullable enable\nusing Z;\nusing delegate*<int>;\nclass C { }\n",
                        "#nullable enable\nusing delegate*<int>;\nusing Z;\nclass C { }\n"
                    ] do
                    let expected = checker.Normalize(PrinterOptions.Default, source, reordered)

                    Expect.isFalse
                        (checker.FastEquivalent(expected, reordered))
                        $"A run holding a non-import using must fall back to Roslyn: {reordered}"

                    verifier.Check(PrinterOptions.Default, "non-import.cs", source, reordered)
                    |> expectFailure [ "non-import.cs" ]
            }
            test "a directive inside a using directive is unprovable, not permitted" {
                let checker = TokenPreservation.Checker()

                let source = "using A = System\n#if X\n.Text\n#endif\n;\nusing B;\nclass C { }\n"
                let reordered = "using B;\nusing A = System\n#if X\n.Text\n#endif\n;\nclass C { }\n"
                let expected = checker.Normalize(PrinterOptions.Default, source, reordered)

                Expect.isFalse
                    (checker.FastEquivalent(expected, reordered))
                    "A using holding a directive leaves the fast path."

                let verifier = SyntaxPreservation.Checker()

                Expect.equal
                    (verdict (
                        verifier.AdjudicateDecision(
                            PrinterOptions.Default,
                            "inside-using.cs",
                            source,
                            reordered
                        )
                    ))
                    "proven"
                    "The independent comparison allows the reordering."

                Expect.equal
                    (verdict (
                        verifier.Decide(
                            PrinterOptions.Default,
                            "inside-using.cs",
                            source,
                            reordered
                        )
                    ))
                    "unprovable"
                    "What only the comparison allows is unproven, not permitted."
            }
            test "fast equivalence settles a permitted trailing separator" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source in
                    [
                        "enum E\n{\n    A = 1\n    // c\n}\n"
                        "class C { int[] a = new int[] { 1, 2\n// c\n}; }\n"
                        "class C { int[] a = { 1, 2\n// c\n}; }\n"
                        "class C { int M(int x) => x switch { 1 => 2, _ => 3\n// c\n}; }\n"
                        "class C { int[] a = [1, 2\n// c\n]; }\n"
                        "class C { bool M(int[] x) => x is [1, 2\n// c\n]; }\n"
                        "class C { object M() => new { A = 1, B = 2\n// c\n}; }\n"
                        "record R(int A) { R M(R r) => r with { A = 1\n// c\n}; }\n"
                        "class C { object M() => new C { Length = 1\n// c\n}; }\n"
                        "class C { int[][] a = new int[][] { new int[] { 1, 2\n// c\n}, new int[] { 3\n// d\n}\n// e\n}; }\n"
                        "class C { int[] a = { 1\n// c\n}; int[] b = { 2\n// d\n}; }\n"
                        "enum E\n{\n    A\n    // c\n}\n"
                        "enum E\n{\n    A = 1,\n    B = 2\n    // c\n}"
                        "#define A\nclass C\n{\n#if A\n    int[] a = { 1, 2\n    // c\n    };\n#endif\n}\n"
                    ] do
                    let formatted = format PrinterOptions.Default source

                    Expect.notEqual
                        (tokenCount source)
                        (tokenCount formatted)
                        $"This fixture must gain or lose a separator: {source}"

                    let expected = checker.Normalize(PrinterOptions.Default, source, formatted)

                    Expect.isTrue
                        (checker.FastEquivalent(expected, formatted))
                        $"A permitted trailing separator must settle without Roslyn: {source}"

                    verifier.Check(PrinterOptions.Default, "separator.cs", source, formatted)
                    |> expectOk

                    verifier.Adjudicate(PrinterOptions.Default, "separator.cs", source, formatted)
                    |> expectOk
            }
            test "a trailing separator behind a closing brace is settled by the walk alone" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                let source = "enum E\n{\n    A = 1\n    // c\n};\n"
                let formatted = format PrinterOptions.Default source
                let expected = checker.Normalize(PrinterOptions.Default, source, formatted)

                Expect.isTrue
                    (checker.FastEquivalent(expected, formatted))
                    "The walk must settle a separator behind the closing brace."

                verifier.Check(PrinterOptions.Default, "enum-semicolon.cs", source, formatted)
                |> expectOk

                Expect.equal
                    (verdict (
                        verifier.Decide(
                            PrinterOptions.Default,
                            "enum-semicolon.cs",
                            source,
                            formatted
                        )
                    ))
                    "proven"
                    "The separator behind the brace is proven, not merely unrefuted."

                verifier.Adjudicate(PrinterOptions.Default, "enum-semicolon.cs", source, formatted)
                |> expectOk

                let plain = "enum E\n{\n    A = 1\n    // c\n}\n"
                let plainFormatted = format PrinterOptions.Default plain

                verifier.Adjudicate(PrinterOptions.Default, "enum.cs", plain, plainFormatted)
                |> expectOk
            }
            test "a permitted trailing separator may also be the one the output drops" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source, changed in
                    [
                        "class C { int[] a = { 1, 2,\n// c\n}; }\n",
                        "class C { int[] a = { 1, 2\n// c\n}; }\n"
                        "class C { bool M(object o) => o is C { Length: 1,\n// c\n}; }\n",
                        "class C { bool M(object o) => o is C { Length: 1\n// c\n}; }\n"
                        "class C { bool M(object o) => o is C { Length: 1\n// c\n}; }\n",
                        "class C { bool M(object o) => o is C { Length: 1,\n// c\n}; }\n"
                        "[A, B,\n// c\n]\nclass C { }\n", "[A, B\n// c\n]\nclass C { }\n"
                        "[A, B\n// c\n]\nclass C { }\n", "[A, B,\n// c\n]\nclass C { }\n"
                        "[assembly: A,\n// c\n]\n", "[assembly: A\n// c\n]\n"
                        "enum E\n{\n    A = 1,\n    // c\n}\n",
                        "enum E\n{\n    A = 1\n    // c\n}\n"
                    ] do
                    let expected = checker.Normalize(PrinterOptions.Default, source, changed)

                    Expect.isTrue
                        (checker.FastEquivalent(expected, changed))
                        $"A dropped trailing separator must settle: {changed}"

                    verifier.Adjudicate(PrinterOptions.Default, "separator.cs", source, changed)
                    |> expectOk
            }
            test "only a list whose grammar permits a trailing separator forgives one" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source, changed in
                    [
                        "using System.Collections.Generic;\n\nclass C\n{\n    Dictionary<int, int> d = new Dictionary<int, int> { { 1, 2 }\n    // c\n    };\n}\n",
                        "using System.Collections.Generic;\n\nclass C\n{\n    Dictionary<int, int> d = new Dictionary<int, int> { { 1, 2, }\n    // c\n    };\n}\n"
                        "class C { int[] a = new int[] { 1, 2, 3\n// c\n}; }\n",
                        "class C { int[] a = new int[] { 1, 3,\n// c\n}; }\n"
                        "class C { int[] a = new int[] { 1, 2\n// c\n}; }\n",
                        "class C { int[] a = new int[] { 1, 3,\n// c\n}; }\n"
                    ] do
                    let expected = checker.Normalize(PrinterOptions.Default, source, changed)

                    Expect.isFalse
                        (checker.FastEquivalent(expected, changed))
                        $"A comma that is not a permitted trailing separator must not settle: {changed}"

                    expectRefusedAndDiagnosedOrNot verifier "separator.cs" source changed
            }
            test "a lambda head this parser accepts and C# does not is what the table declines" {
                let checker = TokenPreservation.Checker()

                for refused in
                    [
                        "var v = new X{A=static static int () => 1};"
                        "var v = new X{A=static async static () => 1};"
                    ] do
                    let formatted = format PrinterOptions.Default refused

                    Expect.notEqual
                        (tokenCount refused)
                        (tokenCount formatted)
                        $"The output must differ by the comma the table would explain: {refused}"

                    checker.Check(PrinterOptions.Default, "lambda-head.cs", refused, formatted)
                    |> expectFailure [ "undeclared token transformation" ]

                for proven in
                    [
                        "var v = new X\n{\n    A = _ => Array.Empty<string>(),\n    B = q\n};\n"
                        "class C\n{\n    void M()\n    {\n        var h = 1;\n        h >>= 2;\n        var v = new X\n        {\n            A = _ => Array.Empty<string>(),\n            B = q\n        };\n    }\n}\n"
                        "var v = new X\n{\n    A = () =>\n    {\n        var h = A<B>();\n        h >>= 2;\n        return h;\n    },\n    B = q\n};\n"
                        "var v = new X\n{\n    A = static async Task () => { },\n    B = q\n};\n"
                        "var v = new X\n{\n    A = async static () => 1,\n    B = q\n};\n"
                        "var v = new X\n{\n    A = v1 >>= 2,\n    B = q\n};\n"
                    ] do
                    let formatted = format PrinterOptions.Default proven

                    Expect.notEqual
                        (tokenCount proven)
                        (tokenCount formatted)
                        $"The output must differ by a comma for the table to be needed: {proven}"

                    let expected = checker.Normalize(PrinterOptions.Default, proven, formatted)

                    Expect.isTrue
                        (checker.FastEquivalent(expected, formatted))
                        $"The tree must settle this separator on its own: {proven}"

                    checker.Check(PrinterOptions.Default, "lambda-head.cs", proven, formatted)
                    |> expectOk
            }
            test "a pointer argument leaves the > run alone, and nothing is written for it" {
                let verifier = SyntaxPreservation.Checker()

                for source in
                    [
                        "class C { unsafe void M() { A<B*>>>=1; } }"
                        "class C { unsafe void M() { A<B**>>>=1; } }"
                        "class C { unsafe void M() { A<int*>>>=1; } }"
                        "class C { unsafe void M() { A<B*[]>>>=1; } }"
                        "class C { unsafe void M() { A<B*>>=1; } }"
                        "class C { unsafe void M() { A<G<int>*>>>=1; } }"
                        "class C { unsafe void M() { A<G<int>.H<B>*>>>=1; } }"
                        "class C { unsafe void M() { var v = new X { A<B*>>>=1 }; } }"
                    ] do
                    let tree = SyntaxTree()
                    Parser.parse source tree

                    let runs (count: int) (token: int -> Token) =
                        let mutable total = 0

                        for index = 0 to count - 1 do
                            match (token index).Kind with
                            | TokenKind.GreaterThanGreaterThanEqualsToken
                            | TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken ->
                                total <- total + 1
                            | _ -> ()

                        total

                    let lexed = runs tree.LexerBuffer.TokenCount tree.LexerBuffer.Token
                    Expect.isGreaterThan lexed 0 $"The fixture must hold a run: {source}"

                    Expect.equal
                        (runs tree.TokenCount tree.Token)
                        lexed
                        $"No closer comes out of the run: {source}"

                    let formatted = format PrinterOptions.Default source

                    match
                        verifier.Check(PrinterOptions.Default, "pointer.cs", source, formatted)
                    with
                    | Ok() ->
                        verifier.Adjudicate(PrinterOptions.Default, "pointer.cs", source, formatted)
                        |> expectOk
                    | Error _ -> ()

            }
            test "a > run that ends in = leaves a separator position this tree can claim" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for proven in
                    [
                        "var v = new X\n{\n    A = X<Y>>=1,\n    B = q\n};\n"
                        "var v = new X\n{\n    A = X<Y<Z>>>=1,\n    B = q\n};\n"
                        "var v = new X\n{\n    A = X<Y,Z>>=1,\n    B = q\n};\n"
                        "enum E\n{\n    A = X<Y>>=1,\n    B = 2\n}\n"
                        "enum E\n{\n    A = X<Y<Z>>>=1,\n    B = 2\n}\n"
                        "var v = new X{A<B>>>=() => {return 1;}};"
                    ] do
                    let formatted = format PrinterOptions.Default proven

                    Expect.notEqual
                        (tokenCount proven)
                        (tokenCount formatted)
                        $"The output must differ by a comma for the table to be needed: {proven}"

                    let expected = checker.Normalize(PrinterOptions.Default, proven, formatted)

                    Expect.isTrue
                        (checker.FastEquivalent(expected, formatted))
                        $"The tree must settle this separator on its own: {proven}"

                    checker.Check(PrinterOptions.Default, "shift-run.cs", proven, formatted)
                    |> expectOk

                    verifier.Adjudicate(PrinterOptions.Default, "shift-run.cs", proven, formatted)
                    |> expectOk

                for refused in
                    [
                        "var v = new X{X<Y<Z>>=() => {return 1;}};"
                        "var v = new X{A<B>>=() => {return 1;}};"
                        "var v = new X{a<b, c>>=() => {return 1;}};"
                        "[A(new int[]{1})]\nenum E{B=X<Y<Z>>=() => {return 1;}}"
                    ] do
                    let formatted = format PrinterOptions.Default refused

                    verifier.Check(PrinterOptions.Default, "shift-run.cs", refused, formatted)
                    |> expectFailure [ "shift-run.cs" ]
            }
            test "combined symbol scans handle interpolation trivia after outer directives" {
                let source =
                    "class C { string M() => $\"{\n#if INNER\n1\n#else\n2\n#endif\n}\"; }\n"
                    + String.concat
                        ""
                        [ for index in 0..32 -> $"#if S{index}\nclass C{index} {{}}\n#endif\n" ]

                let checker = TokenPreservation.Checker()
                checker.Normalize(PrinterOptions.Default, source, source) |> ignore

                Expect.isNone
                    (checker.CombinedIndependentSymbols(source, source))
                    "Non-independent interpolation regions use the ordinary verification path."

                let verifier = SyntaxPreservation.Checker()

                verifier.Check(
                    PrinterOptions.Default,
                    "many-regions.cs",
                    source,
                    source.Replace("class C {", "class C  {")
                )
                |> expectOk

                let independent =
                    String.concat
                        ""
                        [ for index in 0..32 -> $"#if S{index}\nclass C{index} {{}}\n#endif\n" ]

                checker.Normalize(PrinterOptions.Default, independent, independent) |> ignore

                Expect.equal
                    (checker.CombinedIndependentSymbols(independent, independent))
                    (Some [| for index in 0..32 -> $"S{index}" |])
                    "Independent outer regions retain the combined fast path."
            }
            test "using declaration permits only a permutation bounded by conditional nesting" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "using Z;using System;using A;class C{}"
                        "global using Z;global using System;using static Z;using A=System.String;class C{}"
                        "namespace N{using Z;using A;class C{}}"
                        "namespace N;using Z;using A;class C{}"
                        "using Z;using A;using Z;class C{}"
                    ] do
                    let formatted = format PrinterOptions.Default source
                    checker.Check(PrinterOptions.Default, "using.cs", source, formatted) |> expectOk

                    checker.CheckWith(PrinterOptions.Default, [], "using.cs", source, formatted)
                    |> expectFailure [ "IdentifierToken" ]

                    for mutation in
                        [
                            formatted.Replace("using Z;", "")
                            formatted.Replace("using Z;", "using Z;using Z;")
                            formatted.Replace("using Z;", "using Changed;")
                            formatted.Replace("class C", "class Changed")
                        ] do
                        checker.Check(PrinterOptions.Default, "using-mutation.cs", source, mutation)
                        |> expectFailure [ "undeclared token transformation" ]

                for source, changed in
                    [
                        "using Z;namespace N{using A;}", "using A;namespace N{using Z;}"
                        "using Z;\n#if true\nusing A;\n#endif\nclass C{}",
                        "using A;\n#if true\nusing Z;\n#endif\nclass C{}"
                    ] do
                    checker.Check(PrinterOptions.Default, "using-boundary.cs", source, changed)
                    |> expectFailure [ "IdentifierToken" ]

                for source in
                    [
                        "using B;\n#pragma warning disable CS1\nusing A;\nclass D{}"
                        "using B;\n#nullable enable\nusing A;\nclass D{}"
                        "using B;\n#region R\nusing A;\n#endregion\nclass D{}"
                    ] do
                    let formatted = format PrinterOptions.Default source

                    checker.Check(
                        PrinterOptions.Default,
                        "using-nesting-zero.cs",
                        source,
                        formatted
                    )
                    |> expectOk

                    checker.CheckWith(
                        PrinterOptions.Default,
                        [],
                        "using-nesting-zero.cs",
                        source,
                        formatted
                    )
                    |> expectOk

                for source in
                    [
                        "using B;\n#if X\nusing C;\n#endif\nusing A;\nclass D{}"
                        "using B;\n#region R\n#endregion\nusing A;\nclass D{}"
                        "using B;\n#if X\nusing C;\n#endif\n#if Y\nusing E;\n#endif\nusing A;\nclass D{}"
                        "namespace N{\nusing B;\n#if X\nusing C;\n#endif\nusing A;\nclass D{}}"
                    ] do
                    let formatted = format PrinterOptions.Default source

                    checker.Check(
                        PrinterOptions.Default,
                        "using-nesting-zero.cs",
                        source,
                        formatted
                    )
                    |> expectOk

                    checker.CheckWith(
                        PrinterOptions.Default,
                        [],
                        "using-nesting-zero.cs",
                        source,
                        formatted
                    )
                    |> expectFailure [ "IdentifierToken" ]

                for source, changed in
                    [
                        "using B;\n#if true\nusing A;\n#endif\nclass D{}",
                        "using A;\n#if true\nusing B;\n#endif\nclass D{}"
                        "using B;\n#if X\nusing C;\n#endif\nusing A;\nclass D{}",
                        "using A;\nusing B;\nusing C;\nclass D{}"
                        "using B;\n#pragma warning disable CS1\nusing A;\nclass D{}",
                        "using A;\nclass D{}"
                        "using B;\n#pragma warning disable CS1\nusing A;\nclass D{}",
                        "using A;\nusing B;\nusing B;\nclass D{}"
                        "using B;\n#pragma warning disable CS1\nusing A;\nclass D{}",
                        "using A;\nusing Changed;\nclass D{}"
                    ] do
                    checker.Check(
                        PrinterOptions.Default,
                        "using-nesting-mutation.cs",
                        source,
                        changed
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                for source, changed in
                    [
                        "#if true\nusing B;\n#endif\n#if true\nusing A;\n#endif\nclass D{}",
                        "#if true\nusing A;\n#endif\n#if true\nusing B;\n#endif\nclass D{}"
                        "#if true\nusing B;\n#if true\nusing A;\n#endif\n#endif\nclass D{}",
                        "#if true\nusing A;\n#if true\nusing B;\n#endif\n#endif\nclass D{}"
                        "#if true\nusing B;\n#else\n#endif\nusing A;\nclass D{}",
                        "#if true\nusing A;\n#else\n#endif\nusing B;\nclass D{}"
                        "#if true\nextern alias E;\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if true\nextern alias E;\nusing A;\n#endif\nusing B;\nclass D{}"
                        "#if true\nextern alias E;\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if true\nextern alias E;\n#endif\nusing A;\nusing B;\nclass D{}"
                        "#if true\nnamespace N;\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if true\nnamespace N;\nusing A;\n#endif\nusing B;\nclass D{}"
                        "#if true\nnamespace N;\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if true\nnamespace N;\n#endif\nusing A;\nusing B;\nclass D{}"
                        "using B;\n#pragma warning disable CS1\nusing A;\n#if !X\nusing C;\n#endif\nclass D{}",
                        "#pragma warning disable CS1\n#if !X\nusing A;\nusing B;\n#endif\nusing C;\nclass D{}"
                        "#if !X\nusing B;\nusing A;\n#endif\n#if !Y\nusing C;\n#endif\nclass D{}",
                        "#if !Y\nusing A;\nusing B;\n#endif\n#if !X\nusing C;\n#endif\nclass D{}"
                        "#if true\n#region R\nusing B;\n#endregion\nusing A;\n#else\nclass Hidden{}\n#endif\nclass D{}",
                        "#if true\n#region R\nusing A;\n#endregion\nusing B;\n#else\n#endif\nclass Hidden{}\nclass D{}"
                        "#if !X\nusing B;\n#pragma warning disable CS0168\nusing\n#else\nusing\n#endif\nA;\nclass D{}",
                        "#if !X\nusing A;\n#pragma warning disable CS0168\nusing\n#else\nusing\n#endif\nB;\nclass D{}"
                    ] do
                    checker.Check(
                        PrinterOptions.Default,
                        "using-frames-mutation.cs",
                        source,
                        changed
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                checker.Check(
                    PrinterOptions.Default,
                    "using-context-mutation.cs",
                    "using Z;\nusing A;\n#if true\nusing B;\n#endif\n#nullable enable\n#if true\n#endif\nusing C;\nclass D{}",
                    "using A;\nusing Z;\n#if true\n#endif\n#nullable enable\n#if true\nusing B;\n#endif\nusing C;\nclass D{}"
                )
                |> expectFailure [ "undeclared token transformation" ]

                checker.Check(
                    PrinterOptions.Default,
                    "using-context-mutation.cs",
                    "using Z;\nusing A;\n#if true\nusing B;\n#endif\n#if true\n#nullable enable\n#endif\nusing C;\nclass D{}",
                    "using A;\nusing Z;\n#if true\n#endif\n#if true\n#nullable enable\nusing B;\n#endif\nusing C;\nclass D{}"
                )
                |> expectFailure [ "undeclared token transformation" ]

                for source in
                    [
                        "#if true\nusing B;\n#endif\n#if true\nusing A;\n#endif\nclass D{}"
                        "#if true\nusing B;\n#if true\nusing A;\n#endif\n#endif\nclass D{}"
                        "#if true\nusing B;\nusing A;\n#endif\nclass D{}"
                    ] do
                    let formatted = format PrinterOptions.Default source

                    checker.Check(PrinterOptions.Default, "using-frames.cs", source, formatted)
                    |> expectOk
            }
            test "reordered usings retain original spans and duplicate FIFO order" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "using directive permutation")

                let original =
                    [|
                        "using A;"
                        "using static /*static*/ Z.Tools;"
                        "using Alias /*alias*/ = Z.Name;"
                        "using /*first*/ Dup.Space;"
                        "using/*second*/ Dup . Space;"
                        "global using /*global*/ Z;"
                    |]

                let output =
                    [|
                        "using A;"
                        "using static Z.Tools;"
                        "using Alias=Z.Name;"
                        "using /*output cannot supply content*/ Dup.Space;"
                        "using Dup.Space;"
                        "global using Z;"
                    |]

                let source =
                    String.concat "" [ for i in 0..5 -> $"// slot {i}\n{original[i]}\n" ]
                    + "class C{}"

                for order, occurrences in
                    [
                        [| 5; 4; 3; 2; 1; 0 |], [| 5; 3; 4; 2; 1; 0 |]
                        [| 5; 1; 0; 2; 3; 4 |], [| 5; 1; 0; 2; 3; 4 |]
                    ] do
                    let formatted =
                        String.concat "\n" (Array.map (fun i -> output[i]) order) + "\nclass C{}"

                    let expected =
                        String.concat
                            ""
                            [ for i in 0..5 -> $"// slot {i}\n{original[occurrences[i]]}\n" ]
                        + "class C{}"

                    Expect.equal
                        (rule.RewriteInput PrinterOptions.Default source formatted)
                        expected
                        "Reorder only original directive spans; identical keys take the first occurrence."

                let source =
                    "#if true\nusing /*B*/ B;\nusing /*A*/ A;\n#endif\nusing /*D*/ D;\nusing /*C*/ C;\nnamespace N {\nusing /*F*/ F;\nusing /*E*/ E;\n}\n"

                let formatted =
                    "#if true\nusing A;\nusing B;\n#endif\nusing C;\nusing D;\nnamespace N {\nusing E;\nusing F;\n}\n"

                Expect.equal
                    (rule.RewriteInput PrinterOptions.Default source formatted)
                    "#if true\nusing /*A*/ A;\nusing /*B*/ B;\n#endif\nusing /*C*/ C;\nusing /*D*/ D;\nnamespace N {\nusing /*E*/ E;\nusing /*F*/ F;\n}\n"
                    "Match each conditional frame and namespace independently."
            }
            test "reordered usings reject edited tokens and changed duplicate counts" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "using directive permutation")

                let source =
                    "global using Z;using static Z.Tools;using Alias=Z.Name;using /*first*/ Dup.Space;using/*second*/ Dup . Space;using A;class C{}"

                let formatted =
                    "using A;using Dup.Space;using Dup.Space;using Alias=Z.Name;using static Z.Tools;global using Z;class C{}"

                let checker = TokenPreservation.Checker()

                for mutation in
                    [
                        formatted.Replace("Z.Name", "Z.Changed")
                        formatted.Replace("using static Z.Tools;", "using Z.Tools;")
                        formatted.Replace("Dup.Space", "Dup.@Space")
                        formatted.Replace("using A;", "using Dup.Space;")
                        formatted.Replace("using A;", "")
                        formatted.Replace("using A;", "using A;using Dup.Space;")
                    ] do
                    Expect.equal
                        (rule.RewriteInput PrinterOptions.Default source mutation)
                        source
                        "An invalid multiset must not partially rewrite the group."

                    checker.Check(
                        PrinterOptions.Default,
                        "using-queue-mutation.cs",
                        source,
                        mutation
                    )
                    |> expectFailure [ "undeclared token transformation" ]
            }
            test "reversed using matching allocation grows linearly" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "using directive permutation")

                let allocated count =
                    let directives = Array.init count (fun i -> $"using N{i:D6};\n")
                    let source = String.concat "" directives + "class C{}"
                    let formatted = String.concat "" (Array.rev directives) + "class C{}"

                    for _ = 1 to 3 do
                        rule.RewriteInput PrinterOptions.Default source formatted |> ignore

                    let before = GC.GetAllocatedBytesForCurrentThread()
                    let expected = rule.RewriteInput PrinterOptions.Default source formatted
                    let bytes = GC.GetAllocatedBytesForCurrentThread() - before

                    Expect.equal
                        expected
                        formatted
                        "The measured call must actually reverse the group."

                    bytes

                let small = allocated 128
                let large = allocated 1024
                printfn "reversed using allocation: %d / %d bytes" small large

                Expect.isLessThan
                    (float large / float small)
                    12.0
                    "Eight times as many directives must allocate at most roughly eight times as much."
            }
            test "using frames cost one pass over the directives" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "using directive permutation")

                let checker = TokenPreservation.Checker()

                let allocated count =
                    let source =
                        String.concat "" [ for i in 1..count -> $"#if true\nusing N{i};\n#endif\n" ]
                        + "class D{}"

                    checker.Check(PrinterOptions.Default, "guarded.cs", source, source) |> expectOk
                    rule.RewriteInput PrinterOptions.Default source source |> ignore
                    let before = GC.GetAllocatedBytesForCurrentThread()
                    let expected = rule.RewriteInput PrinterOptions.Default source source
                    let bytes = float (GC.GetAllocatedBytesForCurrentThread() - before)

                    Expect.equal
                        expected
                        source
                        "Every guarded directive must stay where the input put it."

                    bytes

                let small = allocated 500
                let large = allocated 1000

                Expect.isLessThan
                    (large / small)
                    3.0
                    "Doubling the guarded usings at most roughly doubles the allocation."
            }
            test "literal newline declaration follows configured EOL and preserves all other bytes" {
                let checker = TokenPreservation.Checker()

                let withoutNewlines =
                    DeclaredTransformations.rules
                    |> List.filter (fun rule -> rule.Name <> "multiline literal line endings")

                for source in
                    [
                        "class C{string s=\"\"\"\n            alpha\n              beta\n            \"\"\";}"
                        "var s=\"\"\"\nalpha\nbeta\n\"\"\";"
                        "var s=@\"alpha\nbeta\";"
                        "var s=$@\"alpha\n{F(x, 7):X}\nbeta\";"
                        "class C{string s=$$\"\"\"\n            alpha {{F(x, 7):X}}\n              beta\n            \"\"\";}"
                        "var s=$@\"alpha\n{F(@\"nested\nvalue\")}\nbeta\";"
                    ] do
                    for inputEol in [ "\n"; "\r\n" ] do
                        let source = source.Replace("\n", inputEol)

                        for endOfLine in [ EndOfLine.Lf; EndOfLine.CrLf ] do
                            let options =
                                { PrinterOptions.Default with
                                    EndOfLine = endOfLine
                                }

                            let actual = format options source
                            checker.Check(options, "literal-eol.cs", source, actual) |> expectOk
                            let target = if endOfLine = EndOfLine.CrLf then "\r\n" else "\n"
                            let formatted = actual.Replace("\r\n", "\n").Replace("\n", target)
                            checker.Check(options, "literal-eol.cs", source, formatted) |> expectOk

                            if
                                inputEol <> (if endOfLine = EndOfLine.CrLf then "\r\n" else "\n")
                            then
                                checker.CheckWith(
                                    options,
                                    withoutNewlines,
                                    "literal-eol.cs",
                                    source,
                                    formatted
                                )
                                |> expectFailure [ "undeclared token transformation" ]

                            checker.Check(
                                options,
                                "literal-content.cs",
                                source,
                                formatted.Replace("alpha", "omega")
                            )
                            |> expectFailure [ "undeclared token transformation" ]

                            if source.Contains("F(x, 7)") then
                                for oldText, newText in
                                    [ "F(x, 7)", "G(x, 7)"; "7", "8"; ":X", ":Y" ] do
                                    checker.Check(
                                        options,
                                        "literal-hole.cs",
                                        source,
                                        formatted.Replace(oldText, newText)
                                    )
                                    |> expectFailure [ "undeclared token transformation" ]

                            let quotes = if source.Contains("\"\"\"") then "\"\"\"" else "@\""
                            let changedQuotes = if quotes = "\"\"\"" then "\"\"\"\"" else "\""

                            checker.Check(
                                options,
                                "literal-quotes.cs",
                                source,
                                formatted.Replace(quotes, changedQuotes)
                            )
                            |> expectFailure [ "undeclared token transformation" ]

                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "multiline literal line endings")

                let source = "// outside\nvar s=@\"alpha\nbeta\";\n"

                let crlf =
                    { PrinterOptions.Default with
                        EndOfLine = EndOfLine.CrLf
                    }

                let converted = "// outside\nvar s=@\"alpha\r\nbeta\";\n"

                Expect.equal
                    (rule.RewriteInput crlf source converted)
                    converted
                    "Only literal newline bytes are rewritten."

                Expect.equal
                    (rule.RewriteInput PrinterOptions.Default source converted)
                    source
                    "Matching configured/input EOL permits no conversion."

                checker.Check(PrinterOptions.Default, "wrong-eol.cs", source, converted)
                |> expectFailure [ "StringLiteralToken" ]

                checker.Check(crlf, "wrong-eol.cs", converted, source)
                |> expectFailure [ "StringLiteralToken" ]
            }
            test "trailing comma declaration covers actual broken and collapsed layouts" {
                let checker = TokenPreservation.Checker()
                let source = "var values = new[] { alphaArgument, betaArgument, gammaArgument };"

                let narrow =
                    format
                        { PrinterOptions.Default with
                            Width = 40
                        }
                        source

                let wide =
                    format
                        { PrinterOptions.Default with
                            Width = 200
                        }
                        narrow

                checker.Check(PrinterOptions.Default, "broken.cs", source, narrow) |> expectOk
                checker.Check(PrinterOptions.Default, "collapsed.cs", narrow, wide) |> expectOk

                checker.CheckWith(PrinterOptions.Default, [], "broken.cs", source, narrow)
                |> expectFailure [ "CommaToken"; "declared transformations: none" ]

                checker.CheckWith(PrinterOptions.Default, [], "collapsed.cs", narrow, wide)
                |> expectFailure [ "CommaToken"; "declared transformations: none" ]
            }
            test "trailing comma declaration rejects other comma edits with the table enabled" {
                let checker = TokenPreservation.Checker()

                for source, formatted in
                    [
                        "var x = new[] { 1, 2 };", "var x = new[] {\n1 2,\n};"
                        "var x = new[] { 1, 2 };", "var x = new[] {\n1,, 2,\n};"
                        "var x = new[] { 1, 2 };", "var x = new[] {\n1, 2,,\n};"
                        "var x = new[] { 1, 2 };", "var x = new[] { 1, 2, };"
                        "var x = new[] { 1, 2, };", "var x = new[] {\n1, 2\n};"
                        "Call(a, b);", "Call(\na, b,\n);"
                        "class C { void M() { Call(); } }", "class C { void M() { Call();,\n} }"
                        "var x = new int[1, 2];", "var x = new int[\n1, 2,\n];"
                        "var x = new[] { };", "var x = new[] {,\n};"
                        "enum E { A, }", "enum E { A }"
                        "var x = new[] { 1, // keep\n};", "var x = new[] { 1 };"
                        "[A, B] class C { }", "[\nA,\nB,\n] class C { }"
                        "[A, B,] class C { }", "[\nA,\nB\n] class C { }"
                        "[A, // keep\n] class C { }", "[A] class C { }"
                        "[A, /* keep */] class C { }", "[A /* keep */] class C { }"
                        "[A, B,] class C { }", "[A B] class C { }"
                        "[assembly: A, B,]", "[assembly: A B]"
                        "class C<[A,] T> { }", "class C<[A] T,> { }"
                        "var b = o is { P: 1 };", "var b = o is {\nP: 1,\n};"
                        "var b = o is { P: 1, };", "var b = o is {\nP: 1\n};"
                        "var b = o is { P: 1, Q: 2, };", "var b = o is { P: 1 Q: 2 };"
                    ] do
                    checker.Check(PrinterOptions.Default, "comma-mutation.cs", source, formatted)
                    |> expectFailure [ "undeclared token transformation" ]
            }
            test "an attribute list and a property pattern lose a trailing comma by collapsing" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for source in
                    [
                        "[\n    Obsolete,\n]\nclass C { }\n"
                        "[Obsolete, Serializable,]\nclass C { }\n"
                        "[assembly: Obsolete,]\n[module: Obsolete, Serializable,]\n"
                        "class C<[A,] T>\n{\n    [return: A,]\n    int M([In, Out,] int x) => 0;\n}\n"
                        "class C\n{\n    int P { [A,] get; [B,] set; }\n}\n"
                        "enum E\n{\n    [A,]\n    X,\n}\n"
                        "class C\n{\n    bool M(object o) => o is C\n    {\n        Length: 1,\n    } c;\n}\n"
                        "class C\n{\n    bool M(object o) => o is { A: { B: 1, }, } or [{ D: 2, }, ..];\n}\n"
                    ] do
                    let struct (formatted, witness) = printWithWitness PrinterOptions.Default source

                    Expect.isTrue
                        witness.ChangedTrailingCommas
                        $"The printer must say it changed a separator: {source}"

                    Expect.isLessThan
                        (tokenCount formatted)
                        (tokenCount source)
                        $"The fixture must really lose a comma: {formatted}"

                    Expect.isFalse
                        (formatted.Contains ",]" || formatted.Contains ", }")
                        $"No collapsed list keeps its comma: {formatted}"

                    Expect.equal
                        (format PrinterOptions.Default formatted)
                        formatted
                        "The collapsed list is a fixed point."

                    checker.Check(PrinterOptions.Default, "collapsed.cs", source, formatted)
                    |> expectOk

                    checker.CheckWith(PrinterOptions.Default, [], "collapsed.cs", source, formatted)
                    |> expectFailure [ "CommaToken"; "declared transformations: none" ]

                    verifier.Check(PrinterOptions.Default, "collapsed.cs", source, formatted)
                    |> expectOk

                    Expect.equal
                        (verdict (
                            verifier.Decide(
                                PrinterOptions.Default,
                                "collapsed.cs",
                                source,
                                formatted
                            )
                        ))
                        "proven"
                        $"The dropped comma is proven, not merely unrefuted: {source}"

                    verifier.Adjudicate(PrinterOptions.Default, "collapsed.cs", source, formatted)
                    |> expectOk
            }
            test "an attribute list and a property pattern that stay broken keep what they had" {
                let narrow =
                    { PrinterOptions.Default with
                        Width = 30
                    }

                for source, kept in
                    [
                        "[AlphaAttribute, BetaAttribute, GammaAttribute,]\nclass C { }\n", true
                        "[AlphaAttribute, BetaAttribute, GammaAttribute]\nclass C { }\n", false
                        "class C\n{\n    bool M(object o) => o is { Alpha: 1, Beta: 2, Gamma: 3, };\n}\n",
                        true
                        "class C\n{\n    bool M(object o) => o is { Alpha: 1, Beta: 2, Gamma: 3 };\n}\n",
                        false
                    ] do
                    let struct (formatted, _) = printWithWitness narrow source

                    Expect.equal
                        (tokenCount formatted)
                        (tokenCount source)
                        $"A broken list neither gains nor loses a comma: {formatted}"

                    Expect.equal
                        (formatted.Contains "GammaAttribute,\n]" || formatted.Contains "Gamma: 3,\n")
                        kept
                        $"The comma stays exactly where the source had one: {formatted}"

                    SyntaxPreservation.Checker().Check(narrow, "broken.cs", source, formatted)
                    |> expectOk
            }
            test "trailing comma declaration covers nested lists and keeps unrelated edits visible" {
                let checker = TokenPreservation.Checker()
                let source = "var x = new[] { new[] { 1, 2 }, new[] { 3, 4, }, };"
                let changed = "var x = new[] {\nnew[] {\n1, 2,\n}, new[] { 3, 4 },\n};"
                checker.Check(PrinterOptions.Default, "nested.cs", source, changed) |> expectOk

                checker.Check(
                    PrinterOptions.Default,
                    "nested.cs",
                    source,
                    changed.Replace("3, 4", "3, 5")
                )
                |> expectFailure [ "NumericLiteralToken" ]
            }
            test "multiline raw-string declaration covers actual space and tab reindentation" {
                let checker = TokenPreservation.Checker()

                let source =
                    "class C{string s=\"\"\"\n            alpha\n              beta\n\n            \"\"\";}"

                for options in
                    [
                        PrinterOptions.Default
                        { PrinterOptions.Default with
                            UseTabs = true
                        }
                    ] do
                    let formatted = format options source
                    checker.Check(PrinterOptions.Default, "raw.cs", source, formatted) |> expectOk

                    checker.CheckWith(PrinterOptions.Default, [], "raw.cs", source, formatted)
                    |> expectFailure
                        [ "MultiLineRawStringLiteralToken"; "declared transformations: none" ]

                    for mutation in
                        [
                            formatted.Replace("alpha", "omega")
                            formatted.Replace("  beta", "   beta")
                        ] do
                        checker.Check(PrinterOptions.Default, "raw-mutation.cs", source, mutation)
                        |> expectFailure [ "MultiLineRawStringLiteralToken" ]
            }
            test
                "raw-string declaration retains delimiters, relative whitespace, newlines and token kind" {
                let checker = TokenPreservation.Checker()
                let source = "var s=\"\"\"\n    alpha\n      beta\n    \"\"\";"
                let reindented = "var s=\"\"\"\n\talpha\n\t  beta\n\t\"\"\";"
                checker.Check(PrinterOptions.Default, "raw.cs", source, reindented) |> expectOk

                for mutation in
                    [
                        reindented.Replace("  beta", " beta")
                        reindented.Replace("alpha", "alphx")
                        reindented.Replace("\"\"\"", "\"\"\"\"")
                        reindented.Replace("\n", "\r\n")
                        "var s=\"alpha\\n  beta\";"
                    ] do
                    checker.Check(PrinterOptions.Default, "raw-mutation.cs", source, mutation)
                    |> expectFailure [ "MultiLineRawStringLiteralToken" ]

                checker.Check(
                    PrinterOptions.Default,
                    "single-line.cs",
                    "var s=\"\"\" alpha \"\"\";",
                    "var s=\"\"\"  alpha \"\"\";"
                )
                |> expectFailure [ "SingleLineRawStringLiteralToken" ]

            }
            test "interpolated raw-string indentation preserves literal text and hole tokens" {
                let checker = TokenPreservation.Checker()

                let source =
                    "class C{string s=$$\"\"\"\n            alpha {{x}}\n              beta\n            \"\"\";}"

                let formatted =
                    format
                        { PrinterOptions.Default with
                            UseTabs = true
                        }
                        source

                checker.Check(PrinterOptions.Default, "interpolated-raw.cs", source, formatted)
                |> expectOk

                checker.CheckWith(
                    PrinterOptions.Default,
                    [],
                    "interpolated-raw.cs",
                    source,
                    formatted
                )
                |> expectFailure [ "InterpolatedStringTextToken" ]

                for mutation in
                    [
                        formatted.Replace("alpha", "omega"), "InterpolatedStringTextToken"
                        formatted.Replace("  beta", " beta"), "InterpolatedStringTextToken"
                        formatted.Replace("{{x}}", "{{y}}"), "IdentifierToken"
                    ] do
                    let changed, kind = mutation

                    checker.Check(
                        PrinterOptions.Default,
                        "interpolated-mutation.cs",
                        source,
                        changed
                    )
                    |> expectFailure [ kind ]

                checker.Check(
                    PrinterOptions.Default,
                    "interpolated-trivia.cs",
                    formatted,
                    formatted.Replace("{{x}}", "{{ x }}")
                )
                |> expectOk

                checker.Check(
                    PrinterOptions.Default,
                    "single-line.cs",
                    "var s=$\"\"\" alpha {x} \"\"\";",
                    "var s=$\"\"\"  alpha {x} \"\"\";"
                )
                |> expectFailure [ "InterpolatedStringTextToken" ]
            }
            test "interpolated raw-string indentation locates holes with csff's own lexer" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "multiline raw-string indentation")

                let rewrite source formatted =
                    rule.RewriteInput PrinterOptions.Default source formatted

                Expect.equal
                    (rewrite
                        "var s = $\"\"\"\n    alpha {x}\n    \"\"\";\n"
                        "var s = $\"\"\"\n        alpha {x}\n        \"\"\";\n")
                    "var s = $\"\"\"\n        alpha {x}\n        \"\"\";\n"
                    "Reindentation alone is explained."

                Expect.equal
                    (rewrite
                        "var s = $\"\"\"\n    alpha {x,5:F2}\n    \"\"\";\n"
                        "var s = $\"\"\"\n        alpha {x,5:F3}\n        \"\"\";\n")
                    "var s = $\"\"\"\n        alpha {x,5:F2}\n        \"\"\";\n"
                    "A format clause belongs to its hole, not to the literal's text."

                Expect.equal
                    (rewrite
                        "var s = $\"\"\"\n    alpha {$\"inner {y}\"}\n    \"\"\";\n"
                        "var s = $\"\"\"\n        alpha {$\"inside {z}\"}\n        \"\"\";\n")
                    "var s = $\"\"\"\n        alpha {$\"inner {y}\"}\n        \"\"\";\n"
                    "A nested literal travels with the hole that holds it."

                let verbatim = "var s = $@\"\n    a\"\"\"\" {x}\n    \";\n"

                Expect.equal
                    (rewrite verbatim "var s = $@\"\n        a\"\"\"\" {x}\n        \";\n")
                    verbatim
                    "A verbatim interpolated literal is never reindented."

                let single = "var s = $\"\"\"\n    alpha {x}\n    \"\"\";\n"

                Expect.equal
                    (rewrite single "var s = $\"\"\"\n        alpha {x}{w}\n        \"\"\";\n")
                    single
                    "An added hole is not explained."
            }
            test "multiline literal line endings converts interpolated runs, not holes" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "multiline literal line endings")

                let crlf =
                    { PrinterOptions.Default with
                        EndOfLine = EndOfLine.CrLf
                    }

                let rewrite (source: string) =
                    rule.RewriteInput crlf source (source.Replace("\n", "\r\n"))

                Expect.equal
                    (rewrite "var s = $\"\"\"\n    a {x}\n    b\n    \"\"\";\n")
                    "var s = $\"\"\"\r\n    a {x}\r\n    b\r\n    \"\"\";\n"
                    "A raw interpolated literal's delimiters and text all convert."

                Expect.equal
                    (rewrite "var s = $\"\"\"\n    a {x +\n    y}\n    b\n    \"\"\";\n")
                    "var s = $\"\"\"\r\n    a {x +\n    y}\r\n    b\r\n    \"\"\";\n"
                    "A hole's newline is not literal text."

                Expect.equal
                    (rewrite "var s = $\"\"\"\n    a {x:F\n2} b\n    \"\"\";\n")
                    "var s = $\"\"\"\r\n    a {x:F\n2} b\r\n    \"\"\";\n"
                    "A format clause's newline is not literal text."

                Expect.equal
                    (rewrite "var s = $\"\"\"\n    a {$@\"p\nq\"} b\n    \"\"\";\n")
                    "var s = $\"\"\"\r\n    a {$@\"p\r\nq\"} b\r\n    \"\"\";\n"
                    "A nested literal's own text converts."

                Expect.equal
                    (rewrite "var s = $\"\"\"\n    a {F(@\"p\nq\")} b\n    \"\"\";\n")
                    "var s = $\"\"\"\r\n    a {F(@\"p\r\nq\")} b\r\n    \"\"\";\n"
                    "A verbatim string inside a hole converts too."

                let singleLine = "var s = $\"\"\" a {x} b \"\"\";\n"

                Expect.equal
                    (rewrite singleLine)
                    singleLine
                    "A single-line raw literal is left alone."
            }
            test "token preservation: raw interpolation marker allocation grows linearly" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "multiline raw-string indentation")

                let allocated content =
                    let code indent =
                        "var s = $$\"\"\"\n" + indent + content + "\n" + indent + "\"\"\";"

                    let source = code "    "
                    let changed = code "\t"
                    rule.RewriteInput PrinterOptions.Default source changed |> ignore
                    let before = GC.GetAllocatedBytesForCurrentThread()
                    let expected = rule.RewriteInput PrinterOptions.Default source changed
                    let bytes = GC.GetAllocatedBytesForCurrentThread() - before
                    Expect.equal expected changed "Literal marker text still permits reindentation."
                    bytes

                for label, content in
                    [
                        "literal marker", (fun count -> "\u0000hole" + String('_', count) + "{{x}}")
                        "NUL run and holes",
                        (fun count -> String('\u0000', count) + String.replicate count "{{x}}")
                    ] do
                    let small = allocated (content 5000)
                    let large = allocated (content 10000)

                    printfn
                        "raw interpolation marker allocation (%s): %d / %d bytes"
                        label
                        small
                        large

                    Expect.isLessThan
                        (float large / float small)
                        3.0
                        "Doubling literal content and hole count at most roughly doubles the allocation."
            }
            for label, indent in [ "unchanged indentation", "    "; "changed indentation", "\t" ] do
                test ($"token preservation rejects raw interpolation boundary movement / {label}") {
                    let checker = TokenPreservation.Checker()

                    for original, changed in
                        [
                            "{}{{x}}", "{{x}}{}"
                            "{}{{x}}{{x}}", "{{x}}{}{{x}}"
                            "\u0000\u0001{{x}}", "{{x}}\u0000\u0001"
                            "\u0000\u0000\u0001{{x}}", "{{x}}\u0000\u0000\u0001"
                            "\u0000hole0\u0001{{x}}", "{{x}}\u0000hole0\u0001"
                            "\u0000\u0000hole0\u0001{{x}}", "{{x}}\u0000\u0000hole0\u0001"
                            "\u0000hole0\u0001\u0000hole_0\u0001{{x}}",
                            "{{x}}\u0000hole0\u0001\u0000hole_0\u0001"
                        ] do
                        let code indent content =
                            "var x = \"VALUE\";\nvar s = $$\"\"\"\n"
                            + indent
                            + content
                            + "\n"
                            + indent
                            + "\"\"\";"

                        let source = code "    " original

                        checker.Check(
                            PrinterOptions.Default,
                            "raw-boundary.cs",
                            source,
                            code indent changed
                        )
                        |> expectFailure
                            [ "undeclared token transformation"; "InterpolatedStringTextToken" ]

                        for content in [ original; original.Replace("{{x}}", "{{\n    x\n}}") ] do
                            checker.Check(
                                PrinterOptions.Default,
                                "raw-layout.cs",
                                source,
                                code indent content
                            )
                            |> expectOk
                }
            test "parser tokens ignore interpolation-expression layout" {
                let source =
                    "class C{string s=$\"\"\"\n    {Call(alphaArgument,betaArgument)}\n    \"\"\";}"

                let formatted =
                    format
                        { PrinterOptions.Default with
                            Width = 40
                        }
                        source

                TokenPreservation
                    .Checker()
                    .Check(PrinterOptions.Default, "hole-layout.cs", source, formatted)
                |> expectOk

                let plain = "var s=$\"{Call(alphaArgument,betaArgument),10:000}\";"
                let changed = "var s = $\"{ Call( alphaArgument, betaArgument ), 10:000}\";"
                let checker = TokenPreservation.Checker()

                checker.CheckWith(PrinterOptions.Default, [], "hole-trivia.cs", plain, changed)
                |> expectOk

                for mutation, kind in
                    [
                        changed.Replace("betaArgument", "otherArgument"), "IdentifierToken"
                        changed.Replace(", 10:", ", 11:"), "NumericLiteralToken"
                        changed.Replace(":000", ":001"), "InterpolatedStringTextToken"
                    ] do
                    checker.Check(PrinterOptions.Default, "hole-mutation.cs", plain, mutation)
                    |> expectFailure [ kind ]
            }
            test "raw indentation and EOL declarations compose with multiline hole layout" {
                let source =
                    "class C{string s=$\"\"\"\n    {Call(alphaArgument,betaArgument)}\n    \"\"\";}"

                let checker = TokenPreservation.Checker()

                let options =
                    { PrinterOptions.Default with
                        Width = 40
                        EndOfLine = EndOfLine.CrLf
                    }

                let formatted = format options source
                checker.Check(options, "hole-layout-eol.cs", source, formatted) |> expectOk

                for name in [ "multiline raw-string indentation"; "multiline literal line endings" ] do
                    let rules =
                        DeclaredTransformations.rules |> List.filter (fun rule -> rule.Name <> name)

                    checker.CheckWith(options, rules, "hole-layout-eol.cs", source, formatted)
                    |> expectFailure [ "undeclared token transformation" ]

                checker.Check(
                    options,
                    "hole-mutation-eol.cs",
                    source,
                    formatted.Replace("betaArgument", "changedArgument")
                )
                |> expectFailure [ "IdentifierToken" ]
            }
            test "parser tokens split generic closers without declaring a transformation" {
                let checker = TokenPreservation.Checker()
                let source = "class C { A<B<C<int>>> value; }"
                let changed = "class C { A<B<C<int> > > value; }"

                checker.CheckWith(PrinterOptions.Default, [], "closers.cs", source, changed)
                |> expectOk

                checker.CheckWith(
                    PrinterOptions.Default,
                    [],
                    "closers.cs",
                    source,
                    format PrinterOptions.Default changed
                )
                |> expectOk

                checker.Check(
                    PrinterOptions.Default,
                    "closer-mutation.cs",
                    source,
                    changed.Replace("int> > >", "int> >")
                )
                |> expectFailure [ "undeclared token transformation" ]
            }
            test "declarations align across generic layout and inside interpolation holes" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "var xs = new A<B<C<int> > >[] { alphaArgument, betaArgument, gammaArgument };"
                        "class C { A<B<C<int> > > field; string s=\"\"\"\n                    alpha\n                    \"\"\"; }"
                    ] do
                    let formatted =
                        format
                            { PrinterOptions.Default with
                                Width = 40
                            }
                            source

                    checker.Check(
                        PrinterOptions.Default,
                        "parser-declarations.cs",
                        source,
                        formatted
                    )
                    |> expectOk

                    checker.CheckWith(
                        PrinterOptions.Default,
                        [],
                        "parser-declarations.cs",
                        source,
                        formatted
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                let source = "var s=$\"{new[] { alphaArgument, betaArgument, gammaArgument }}\";"

                let changed =
                    "var s=$\"{new[] {\nalphaArgument, betaArgument, gammaArgument,\n}}\";"

                checker.Check(PrinterOptions.Default, "hole-comma.cs", source, changed)
                |> expectOk

                checker.CheckWith(PrinterOptions.Default, [], "hole-comma.cs", source, changed)
                |> expectFailure [ "CommaToken" ]
            }
            test
                "unindented multiline and single-line raw strings are printed without reindentation" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "class C{string s=\"\"\"\nalpha\n\"\"\";}"
                        "class C{string s=\"\"\" alpha \"\"\";}"
                    ] do
                    let formatted =
                        format
                            { PrinterOptions.Default with
                                UseTabs = true
                            }
                            source

                    checker.CheckWith(PrinterOptions.Default, [], "literal.cs", source, formatted)
                    |> expectOk

                checker.Check(
                    PrinterOptions.Default,
                    "unindented.cs",
                    "var s=\"\"\"\nalpha\n\"\"\";",
                    "var s=\"\"\"\n  alpha\n  \"\"\";"
                )
                |> expectFailure [ "MultiLineRawStringLiteralToken" ]
            }
            test "production declarations compose without hiding another token edit" {
                let source =
                    "class C{object[] xs=new[]{\"\"\"\n                    alpha\n                    \"\"\",\"beta\"};}"

                let formatted =
                    format
                        { PrinterOptions.Default with
                            Width = 40
                        }
                        source

                let checker = TokenPreservation.Checker()

                checker.Check(PrinterOptions.Default, "combined.cs", source, formatted)
                |> expectOk

                for rule in DeclaredTransformations.rules do
                    checker.CheckWith(
                        PrinterOptions.Default,
                        [ rule ],
                        "combined.cs",
                        source,
                        formatted
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                checker.Check(
                    PrinterOptions.Default,
                    "combined.cs",
                    source,
                    formatted.Replace("alpha", "omega")
                )
                |> expectFailure [ "MultiLineRawStringLiteralToken" ]
            }
            test "token preservation ignores trivia and offsets, including empty files" {
                let checker = TokenPreservation.Checker()

                for source, formatted in
                    [
                        "", "\r\n// comment\r\n"
                        "class C{}", "// comment\nclass /* name */ C {\r\n}\n"
                        "a>>b; a[1..2];", "a >> b;\r\na[ 1 .. 2 ];\n"
                        "var x = $\"{F()}\";", "var x=$\"{F()}\";\r\n"
                    ] do
                    checker.Check(PrinterOptions.Default, "trivia.cs", source, formatted)
                    |> expectOk
            }
            test "token preservation checks actual printer output" {
                let source = "class C{}"
                let tree = SyntaxTree()
                use document = new DocumentBuffer()
                use printer = new Printer()
                Parser.parse source tree
                SyntaxPrinter.build source tree document PrinterOptions.Default
                printer.Print(source, document, PrinterOptions.Default)

                TokenPreservation
                    .Checker()
                    .Check(PrinterOptions.Default, "printer.cs", source, printer.OutputText)
                |> expectOk
            }
            test "parser-token comparison adds no success-path allocation" {
                let source = "class C{}"
                let before = SyntaxTree()
                let after = SyntaxTree()
                let checker = TokenPreservation.Checker()

                let parsing =
                    allocated (fun () ->
                        Parser.parse source before
                        Parser.parse source after)

                let checking =
                    allocated (fun () ->
                        checker.CheckWith(
                            PrinterOptions.Default,
                            [],
                            "allocation.cs",
                            source,
                            source
                        )
                        |> expectOk)

                Expect.equal
                    checking
                    parsing
                    "The exact comparison allocates nothing beyond parsing."
            }
            test "token preservation names dropped and invented tokens" {
                let checker = TokenPreservation.Checker()

                checker.Check(PrinterOptions.Default, "drop.cs", "Call();", "Call()")
                |> expectFailure
                    [
                        "drop.cs: token 3: undeclared token transformation"
                        "expected count=5, formatted count=5"
                        "declared transformations: using directive permutation, declaration modifier permutation"
                        "expected: SemicolonToken, start=6, length=1, text=\";\""
                        "formatted: SemicolonToken, start=6, length=0"
                    ]

                checker.Check(PrinterOptions.Default, "add.cs", "Call()", "Call();")
                |> expectFailure
                    [
                        "add.cs: token 3"
                        "expected: SemicolonToken, start=6, length=0"
                        "formatted: SemicolonToken"
                    ]

                checker.Check(PrinterOptions.Default, "empty.cs", "Call();", "")
                |> expectFailure [ "empty.cs: token 0"; "IdentifierToken"; "EndOfFileToken" ]

                checker.Check(PrinterOptions.Default, "suffix.cs", "", "Call();")
                |> expectFailure
                    [
                        "suffix.cs: token 0"
                        "expected: EndOfFileToken"
                        "formatted: IdentifierToken"
                    ]
            }
            test "token preservation rejects equal counts with changed kinds, text or order" {
                let checker = TokenPreservation.Checker()

                for source, formatted, kind in
                    [
                        "x+y;", "x-y;", "PlusToken"
                        "int x=1;", "int y=1;", "IdentifierToken"
                        "int x=1;", "int x=2;", "NumericLiteralToken"
                        "A(); B();", "B(); A();", "IdentifierToken"
                        "a>>b;", "a> >b;", "GreaterThanGreaterThanToken"
                        "var x=$\"{F()}\";", "var x=$\"{{F()}}\";", "InterpolatedString"
                    ] do
                    checker.Check(PrinterOptions.Default, "change.cs", source, formatted)
                    |> expectFailure [ "change.cs: token"; "undeclared token transformation"; kind ]
            }
            test "token preservation compares literal interiors beyond diagnostic excerpts" {
                let prefix = String.replicate 100 "a"
                let source = $"var x=\"{prefix}b\";"
                let formatted = $"var x=\"{prefix}c\";"

                TokenPreservation
                    .Checker()
                    .Check(PrinterOptions.Default, "literal.cs", source, formatted)
                |> expectFailure [ "literal.cs: token 3"; "StringLiteralToken"; "..." ]
            }
            test "declared transformations require the exact input rewrite" {
                let checker = TokenPreservation.Checker()

                let rule: DeclaredTransformations.Rule =
                    {
                        Name = "fixture semicolon"
                        Witnessed = fun _ -> true
                        RewriteInput =
                            fun _ source _ -> if source = "Call()" then "Call();" else source
                    }

                checker.CheckWith(
                    PrinterOptions.Default,
                    [ rule ],
                    "declared.cs",
                    "Call()",
                    "Call ( );\n"
                )
                |> expectOk

                checker.CheckWith(PrinterOptions.Default, [], "undeclared.cs", "Call()", "Call();")
                |> expectFailure
                    [ "undeclared token transformation"; "declared transformations: none" ]

                for source, formatted in [ "Call()", "Call();Extra();"; "Other()", "Other();" ] do
                    checker.CheckWith(
                        PrinterOptions.Default,
                        [ rule ],
                        "declared.cs",
                        source,
                        formatted
                    )
                    |> expectFailure
                        [
                            "undeclared token transformation"
                            "declared transformations: fixture semicolon"
                        ]
            }
            test "a rule its witness does not claim is not run, and its output is refused" {
                let checker = TokenPreservation.Checker()

                let rule: DeclaredTransformations.Rule =
                    {
                        Name = "fixture semicolon"
                        Witnessed = fun witness -> witness.SortedModifiers
                        RewriteInput =
                            fun _ source _ -> if source = "Call()" then "Call();" else source
                    }

                checker.CheckWith(
                    PrinterOptions.Default,
                    [ rule ],
                    "claimed.cs",
                    "Call()",
                    "Call ( );\n",
                    witness =
                        { TransformationWitness.None with
                            SortedModifiers = true
                        }
                )
                |> expectOk

                checker.CheckWith(
                    PrinterOptions.Default,
                    [ rule ],
                    "denied.cs",
                    "Call()",
                    "Call ( );\n",
                    witness = TransformationWitness.None
                )
                |> expectFailure
                    [
                        "undeclared token transformation"
                        "declared transformations: fixture semicolon"
                    ]

                checker.CheckWith(
                    PrinterOptions.Default,
                    [ rule ],
                    "unwitnessed.cs",
                    "Call()",
                    "Call ( );\n"
                )
                |> expectOk
            }
            test "the printer witnesses a modifier run only when it reordered one" {
                for source, moved in
                    [
                        "class C { public static void M() { } }\n", false
                        "class C { static public void M() { } }\n", true
                        "class C { void M() { } }\n", false
                        "class C { protected internal override string P => \"x\"; }\n", false
                        "class C { override protected internal string P => \"x\"; }\n", true
                    ] do
                    let struct (_, witness) = printWithWitness PrinterOptions.Default source

                    Expect.equal
                        witness.SortedModifiers
                        moved
                        ("The witness must name exactly the reordering of " + source)
            }
            test "a witness that denies the permutation the printer made loses the proof" {
                let options = PrinterOptions.Default
                let source = "class C { static public void M() { } }\n"
                let struct (formatted, witness) = printWithWitness options source

                Expect.isTrue
                    witness.SortedModifiers
                    "The fixture must exercise the transformation the witness is about."

                Expect.stringContains
                    formatted
                    "public static"
                    "The printer really did move a modifier, so a rule has to explain it."

                let verifier = SyntaxPreservation.Checker()

                Expect.equal
                    (verdict (
                        verifier.Decide(options, "witness.cs", source, formatted, witness = witness)
                    ))
                    "proven"
                    "The rule the witness claims searches, finds the permutation and proves it."

                Expect.equal
                    (verdict (
                        verifier.Decide(
                            options,
                            "witness.cs",
                            source,
                            formatted,
                            witness = { witness with SortedModifiers = false }
                        )
                    ))
                    "unprovable"
                    "A denied rule makes no rewrite, so the unrewritten input does not hold the output's tokens."
            }
            test
                "the printer witnesses using sorts, trailing commas, and raw string reindents only when performed" {
                let options = PrinterOptions.Default
                let checker = TokenPreservation.Checker()

                for source, expectedUsings, expectedCommas, expectedRaw in
                    [
                        "using System;\nusing System.Text;\n\nclass C\n{\n    int A;\n    C M() => new C();\n    string s = \"\"\"\na\n\"\"\";\n}\n",
                        false,
                        false,
                        false
                        "using System.Text;\nusing System;\nclass C { }\n", true, false, false
                        "class C { int A; C M() => new C { A = 1 }; }\n", false, true, false
                        "class C { int A; string M() => $\"{new C { A = 1, }}\"; }\n",
                        false,
                        true,
                        false
                        "class C { int[] a = [1, 2,]; }\n", false, true, false
                        "[Obsolete,]\nclass C { }\n", false, true, false
                        "[Obsolete]\nclass C { }\n", false, false, false
                        "class C { bool M(object o) => o is { P: 1, }; }\n", false, true, false
                        "class C { bool M(object o) => o is { P: 1 }; }\n", false, false, false
                        "class C {\nstring s = \"\"\"\n  a\n  \"\"\";\n}\n", false, false, true
                    ] do
                    let struct (formatted, witness) = printWithWitness options source

                    Expect.equal
                        witness.SortedUsings
                        expectedUsings
                        ("SortedUsings witness mismatch for " + source)

                    Expect.equal
                        witness.ChangedTrailingCommas
                        expectedCommas
                        ("ChangedTrailingCommas witness mismatch for " + source)

                    Expect.equal
                        witness.ReindentedRawStrings
                        expectedRaw
                        ("ReindentedRawStrings witness mismatch for " + source)

                    if expectedUsings || expectedCommas || expectedRaw then
                        checker.CheckWith(
                            options,
                            DeclaredTransformations.rules,
                            "witness-extended.cs",
                            source,
                            formatted,
                            witness = witness
                        )
                        |> expectOk

                        checker.CheckWith(
                            options,
                            DeclaredTransformations.rules,
                            "witness-extended.cs",
                            source,
                            formatted,
                            witness = TransformationWitness.None
                        )
                        |> expectFailure [ "undeclared token transformation" ]
            }
            test "an output that already carries the input's tokens consults no declaration" {
                let rule: DeclaredTransformations.Rule =
                    {
                        Name = "fixture corruption"
                        Witnessed = fun _ -> true
                        RewriteInput = fun _ source _ -> source.Replace("Call", "Other")
                    }

                let checker = TokenPreservation.Checker()

                for source, formatted in [ "Call();", "Call();"; "Call();", "Call ( ) ;\n" ] do
                    checker.CheckWith(
                        PrinterOptions.Default,
                        [ rule ],
                        "unchanged.cs",
                        source,
                        formatted
                    )
                    |> expectOk

                checker.CheckWith(
                    PrinterOptions.Default,
                    [ rule ],
                    "changed.cs",
                    "Call();",
                    "Call();Extra();"
                )
                |> expectFailure
                    [
                        "undeclared token transformation"
                        "declared transformations: fixture corruption"
                    ]
            }
            test "declared transformations compose in table order" {
                let rules: DeclaredTransformations.Rule list =
                    [
                        {
                            Name = "fixture rename"
                            Witnessed = fun _ -> true
                            RewriteInput = fun _ source _ -> source.Replace("A()", "B()")
                        }
                        {
                            Name = "fixture semicolon"
                            Witnessed = fun _ -> true
                            RewriteInput =
                                fun _ source _ -> if source = "B()" then "B();" else source
                        }
                    ]

                let checker = TokenPreservation.Checker()

                checker.CheckWith(PrinterOptions.Default, rules, "ordered.cs", "A()", "B();")
                |> expectOk

                checker.CheckWith(
                    PrinterOptions.Default,
                    List.rev rules,
                    "ordered.cs",
                    "A()",
                    "B();"
                )
                |> expectFailure
                    [ "undeclared token transformation"; "fixture semicolon, fixture rename" ]
            }
            test "disabled text remains outside the token property" {
                let source = "#if NEVER_DEFINED\nF();\n#endif\nActive();\n"
                let formatted = "#if NEVER_DEFINED\nG(); H();\n#endif\nActive();\n"

                TokenPreservation
                    .Checker()
                    .Check(PrinterOptions.Default, "disabled.cs", source, formatted)
                |> expectOk
            }
            test
                "declared transformations fast-path pre-checks allocate nothing when no rule applies" {
                let source =
                    "using System;\nusing System.Collections.Generic;\npublic static class C { public static string S = @\"single\"; }\n"

                let formatted =
                    "using System;\nusing System.Collections.Generic;\n\npublic static class C\n{\n    public static string S = @\"single\";\n}\n"

                let applyAll () =
                    DeclaredTransformations.rules
                    |> List.fold
                        (fun current rule ->
                            rule.RewriteInput PrinterOptions.Default current formatted)
                        source

                Expect.isTrue
                    (Object.ReferenceEquals(source, applyAll ()))
                    "No declared transformation should rewrite already-canonical input."

                let bytes =
                    allocated (fun () ->
                        let rewritten = applyAll ()

                        Expect.isTrue
                            (Object.ReferenceEquals(source, rewritten))
                            "Pre-checks should return the original string instance.")

                Expect.isLessThan
                    bytes
                    256L
                    $"Expected fast-path pre-checks to avoid Roslyn/buffer allocations, but allocated {bytes} bytes."
            }
            test "modifier permutation preserves leading comment content across layout changes" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for comment in
                    [
                        "/// </summary>\n"
                        "/// <summary>\n  /// keeps  words \t\n/// </summary>\n"
                        "/** <summary>\n  * keeps  words \t\n  * </summary> */\n"
                        "// keeps  words \t\n"
                        "/* keeps  words \t*/\n"
                    ] do
                    let source = "class C {\n" + comment + "static public void M() { }\n}\n"

                    for ending in [ EndOfLine.Lf; EndOfLine.CrLf; EndOfLine.Cr ] do
                        let options =
                            { PrinterOptions.Default with
                                EndOfLine = ending
                            }

                        let struct (formatted, witness) = printWithWitness options source
                        Expect.isTrue witness.SortedModifiers "The printer sorts the modifier run."

                        Expect.isFalse
                            (checker.LexicallyPreserved(source, formatted))
                            "The modifier order differs."

                        Expect.isTrue
                            (checker.SeparatorsOnlyPreserved(
                                source,
                                formatted,
                                witness = witness,
                                options = options
                            ))
                            "The run proof preserves the leading comment's content and position."

                        checker.Check(options, "comment-boundary.cs", source, formatted) |> expectOk

                        verifier.Check(options, "comment-boundary.cs", source, formatted)
                        |> expectOk

                let source =
                    "class C {\n/// <summary>\n/// keeps  words\n/// </summary>\nstatic public void M() { }\n}\n"

                let formatted = format PrinterOptions.Default source

                for corrupted in
                    [
                        formatted.Replace("keeps  words", "changes words")
                        formatted.Replace("keeps  words", "keeps words")
                        formatted.Replace("/// keeps  words\n", "")
                        formatted.Replace("/// keeps  words", "/// keeps\n    /// words")
                        formatted.Replace("///", "//")
                        formatted
                            .Replace("    /// <summary>", "    public\n    /// <summary>")
                            .Replace("public static void", "static void")
                    ] do
                    Expect.isFalse
                        (checker.LexicallyPreserved(source, corrupted))
                        "A corrupted pair is not lexically identical."

                    Expect.isFalse
                        (checker.SeparatorsOnlyPreserved(source, corrupted))
                        "A comment change or move into the run cannot prove a permutation."

                    checker.Check(PrinterOptions.Default, "comment-boundary.cs", source, corrupted)
                    |> expectFailure [ "undeclared token transformation" ]

                    Expect.isError
                        (verifier.Check(
                            PrinterOptions.Default,
                            "comment-boundary.cs",
                            source,
                            corrupted
                        ))
                        "The complete verifier refuses the corrupted output."
            }
            test "the declaration modifier permutation proves its own sorts without Roslyn" {
                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                for name, source in
                    [
                        "after-ref.cs", "class C {\n[X]\nextern static ref int M(object a);\n}\n"
                        "partial-method.cs",
                        "partial class C {\nstatic public partial void M();\n}\n"
                        "accessor.cs",
                        "class C {\npublic int P { internal protected get; set; }\n}\n"
                        "doc-boundary.cs",
                        "class C {\n/// <summary>d</summary>\nstatic public void M() { }\n}\n"
                        "block-boundary.cs", "class C {\n/* c */ static public void M() { }\n}\n"
                        "async.cs", "class C {\nasync static public Task M() { return null; }\n}\n"
                    ] do
                    let formatted = format PrinterOptions.Default source

                    Expect.notEqual
                        formatted
                        source
                        $"The fixture {name} must give the printer a run to sort."

                    checker.Check(PrinterOptions.Default, name, source, formatted) |> expectOk

                    Expect.equal
                        (verdict (verifier.Decide(PrinterOptions.Default, name, source, formatted)))
                        "proven"
                        $"The sort in {name} is provable from csff's own two parses."

                for name, source, reordered in
                    [
                        "fixed-moved.cs",
                        "unsafe struct C { public fixed int F[1]; }",
                        "unsafe struct C { fixed public int F[1]; }"
                        "extern-alias.cs",
                        "namespace N { public extern class D {} }",
                        "namespace N { extern public class D {} }"
                        "duplicate-partial.cs",
                        "public static partial partial class D {}",
                        "static public partial partial class D {}"
                        "async-past-partial.cs",
                        "class C { public async partial C(){} }",
                        "class C { async public partial C(){} }"
                        "local-access.cs",
                        "class C {void M() {static public void Local(){}}}",
                        "class C {void M() {public static void Local(){}}}"
                    ] do
                    checker.Check(PrinterOptions.Default, name, source, reordered)
                    |> expectFailure [ "undeclared token transformation" ]

                    expectRefusedAndDiagnosedOrNot verifier name source reordered
            }
            test "multiline literal line endings rule handles @$ interpolated verbatim strings" {
                let checker = TokenPreservation.Checker()
                let source = "var s = @$\"alpha\r\n{1}\r\nbeta\";\r\n"
                let formatted = "var s = @$\"alpha\n{1}\nbeta\";\n"

                checker.Check(PrinterOptions.Default, "at-dollar-eol.cs", source, formatted)
                |> expectOk
            }
            test
                "using directive permutation handles tuple aliases and incomplete using runs linearly" {
                let checker = TokenPreservation.Checker()

                let tupleSource =
                    "using T = (int z, int y);\nusing T = (int a, int b);\nclass C { }\n"

                let tupleFormatted =
                    "using T = (int a, int b);\nusing T = (int z, int y);\nclass C { }\n"

                checker.Check(PrinterOptions.Default, "tuple-alias.cs", tupleSource, tupleFormatted)
                |> expectOk

                let incompleteSource = String.replicate 200 "using " + "Z; static public class C {}"

                let incompleteFormatted =
                    String.replicate 200 "using " + "Z; public static class C {}"

                checker.Check(
                    PrinterOptions.Default,
                    "incomplete-usings.cs",
                    incompleteSource,
                    incompleteFormatted
                )
                |> expectFailure
                    [
                        "incomplete-usings.cs: token 600"
                        "expected: StaticKeyword"
                        "formatted: PublicKeyword"
                    ]

                let verifier = SyntaxPreservation.Checker()

                Expect.equal
                    (verdict (
                        verifier.AdjudicateDecision(
                            PrinterOptions.Default,
                            "incomplete-usings.cs",
                            incompleteSource,
                            incompleteFormatted
                        )
                    ))
                    "proven"
                    "The independent comparison allows the modifier swap."

                Expect.equal
                    (verdict (
                        verifier.Decide(
                            PrinterOptions.Default,
                            "incomplete-usings.cs",
                            incompleteSource,
                            incompleteFormatted
                        )
                    ))
                    "unprovable"
                    "A swap on an incomplete parse is unproven, not permitted."
            }
            test
                "declared transformations rewrite complete syntax trees and refuse a comment moved into a modifier list" {
                let checker = TokenPreservation.Checker()

                let source =
                    "using System.Text;\nusing System;\nnamespace N {\nusing System.Linq;\nusing System.Collections.Generic;\nstatic public class C {\nvoid M() {\nasync static void Local() { }\nvar xs = new[] {\n1,\n2\n};\n}\n}\n}\n"

                let formatted = format PrinterOptions.Default source

                checker.Check(PrinterOptions.Default, "cst-rewrites.cs", source, formatted)
                |> expectOk

                let docModifierSource =
                    "class C {\n/// <summary>doc</summary>\npublic static void M() { }\n}\n"

                let docModifierSwapped =
                    "class C {\nstatic\n/// <summary>doc</summary>\npublic void M() { }\n}\n"

                checker.Check(
                    PrinterOptions.Default,
                    "doc-modifier.cs",
                    docModifierSource,
                    docModifierSwapped
                )
                |> expectFailure [ "undeclared token transformation" ]

                let verifier = SyntaxPreservation.Checker()

                for kept in [ "partial public ref struct D{}"; "partial readonly ref struct D{}" ] do
                    Expect.stringStarts
                        (format PrinterOptions.Default kept)
                        (kept.Substring(0, kept.IndexOf(" struct", StringComparison.Ordinal)))
                        $"A partial ahead of the end keeps its run as written: {kept}"

                for invalidModifierReorder, reordered in
                    [
                        "partial public ref struct D{}", "public partial ref struct D { }\n"
                        "partial readonly ref struct D{}", "readonly partial ref struct D { }\n"
                        "class C {void M() {static public void Local(){}}}",
                        format
                            PrinterOptions.Default
                            "class C {void M() {static public void Local(){}}}"
                    ] do

                    checker.Check(
                        PrinterOptions.Default,
                        "reclassified-modifier.cs",
                        invalidModifierReorder,
                        reordered
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                    expectRefusedAndDiagnosedOrNot
                        verifier
                        "reclassified-modifier.cs"
                        invalidModifierReorder
                        reordered

                let validFixed = "unsafe struct C { public fixed int F[1]; }"
                let movedFixed = "unsafe struct C { fixed public int F[1]; }"

                checker.Check(PrinterOptions.Default, "fixed-modifier.cs", validFixed, movedFixed)
                |> expectFailure [ "undeclared token transformation" ]

                expectRefusedAndDiagnosedOrNot verifier "fixed-modifier.cs" validFixed movedFixed

                for name, source, reordered in
                    [
                        "top-level-local-modifiers.cs",
                        "public partial async Task M(){}",
                        "partial public async Task M(){}"
                        "top-level-local-contextual-modifiers.cs",
                        "partial file Task M(){}",
                        "file partial Task M(){}"
                    ] do
                    checker.Check(PrinterOptions.Default, name, source, reordered)
                    |> expectFailure [ "undeclared token transformation" ]

                    Expect.equal
                        (verdict (
                            verifier.AdjudicateDecision(
                                PrinterOptions.Default,
                                name,
                                source,
                                reordered
                            )
                        ))
                        "proven"
                        "The independent comparison allows this particular reordering."

                    Expect.equal
                        (verdict (verifier.Decide(PrinterOptions.Default, name, source, reordered)))
                        "unprovable"
                        "A moved contextual modifier is unproven, not permitted."

                for malformedCollection in
                    [
                        "var v = [\n{1,2},\n];"
                        "var v = [\n{1000000000000000000,2000000000000000000},{3000000000000000000,4000000000000000000}\n];"
                        "var v = new X{X<Y<Z>>=() => {return 1;}};"
                    ] do
                    let formattedCollection = format PrinterOptions.Default malformedCollection

                    checker.Check(
                        PrinterOptions.Default,
                        "malformed-collection.cs",
                        malformedCollection,
                        formattedCollection
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                for source, mutated in
                    [
                        "var v=new X{1,[2]=3};", "var v=new X{1,[2,\n]=3};"
                        "var v=x switch {_ => (1,out var y)};",
                        "var v=x switch {_ => (1,out var y),\n};"
                        "class C{void M(){[new X()];}}", "class C{void M(){[new X(),\n];}}"
                    ] do
                    checker.Check(
                        PrinterOptions.Default,
                        "malformed-trailing-comma.cs",
                        source,
                        mutated
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                for nonImportUsing in
                    [
                        "using Z;\nusing int;"
                        "using Z;\nusing ref int;"
                        "using static Z;\nusing int;"
                        "using B = (int x, int y);\nusing ref int;"
                        "using Z;\nusing delegate*<int>;\nusing A;"
                    ] do
                    let reorderedUsing = format PrinterOptions.Default nonImportUsing

                    checker.Check(
                        PrinterOptions.Default,
                        "non-import-using.cs",
                        nonImportUsing,
                        reorderedUsing
                    )
                    |> expectFailure [ "undeclared token transformation" ]

                    expectRefusedAndDiagnosedOrNot
                        verifier
                        "non-import-using.cs"
                        nonImportUsing
                        reorderedUsing

                let deepImport = "using Z" + String.replicate 12000 ".A" + ";\n"
                let deepSource = deepImport + "using A;\nclass C { }\n"
                let deepFormatted = "using A;\n" + deepImport + "class C { }\n"
                let mutable deepResult = Error "Did not run"

                let thread =
                    System.Threading.Thread(
                        System.Threading.ThreadStart(fun () ->
                            deepResult <-
                                TokenPreservation
                                    .Checker()
                                    .Check(
                                        PrinterOptions.Default,
                                        "deep-using.cs",
                                        deepSource,
                                        deepFormatted
                                    )),
                        1024 * 1024
                    )

                thread.Start()
                thread.Join()
                expectOk deepResult
            }
            test "a generic alias is import-shaped, so a closed frame beside it stays provable" {
                for source in
                    [
                        "#if NET\nusing System.Text.Json;\n#endif\nusing C = N.G<N.T>;\nclass D{}"
                        "#if NET\nusing System.Text.Json;\n#endif\nusing C = N.G<N.H<N.T>>;\nclass D{}"
                        "#if NET\nusing System.Text.Json;\n#endif\nusing C = N.G<N.A, N.B>;\nclass D{}"
                        "#if NET\nusing System.Text.Json;\n#endif\nusing C = N.G<int>;\nclass D{}"
                        "#if NET\nusing System.Text.Json;\n#endif\nusing C = N.G<string[]?>;\nclass D{}"
                    ] do
                    let actual = format PrinterOptions.Default source

                    SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "generic-alias.cs", source, actual)
                    |> expectOk

                    Expect.notEqual actual source "The file is formatted, not declined."
                    Expect.equal (format PrinterOptions.Default actual) actual "Idempotent."

                for source in
                    [ "#if NET\nusing System.Text.Json;\n#endif\nusing C = (int, int);\nclass D{}" ] do
                    let actual = format PrinterOptions.Default source

                    SyntaxPreservation
                        .Checker()
                        .Check(PrinterOptions.Default, "outside-shape.cs", source, actual)
                    |> function
                        | Ok() -> failtest "A tuple is not import-shaped."
                        | Error _ -> ()
            }
            test "active conditional using sorting preserves every directive" {
                let checker = TokenPreservation.Checker()

                let options =
                    configurations
                    @ [
                        "CRLF",
                        { PrinterOptions.Default with
                            EndOfLine = EndOfLine.CrLf
                        }
                    ]

                for _, options in options do
                    for source in
                        [
                            "using B;\n#if true\nusing C;\n#endif\nusing A;\nclass D{}"
                            "namespace N{\nusing B;\n#if true\nusing C;\n#endif\nusing A;\nclass D{}}"
                            "namespace N;\nusing B;\n#if true\nusing C;\n#endif\nusing A;\nclass D{}"
                            "using B;\n#if true\nusing C;\n#if true\nusing E;\n#endif\n#endif\nusing A;\nclass D{}"
                            "using B;\n#if false\nusing E;\n#else\nusing C;\n#endif\nusing A;\nclass D{}"
                            "using B;\n#if true\nusing C;\n#endif\n#if X\nusing D;\n#endif\nusing A;\nclass D{}"
                            "using B;\n#if true\nusing C;\n#endif\nusing E;\n#if X\nusing D;\n#endif\nusing A;\nclass D{}"
                            "using B;\n#if true\nusing C;\n#endif\nusing E;\n#if X\nusing D;\n#endif\nusing A;\n#if true\nusing F;\n#endif\nclass D{}"
                            "using B;\nusing A;\n#if false\nclass X{}\n#endif\nclass D{}"
                            "using B;\nusing A;\n#if WINDOWS\nusing Win32;\n#else\nusing AppKit;\n#endif\n\nnamespace N;\nclass D{}"
                        ] do
                        let actual = format options source

                        SyntaxPreservation
                            .Checker()
                            .Check(options, "active-using.cs", source, actual)
                        |> expectOk

                        checker.CheckWith(options, [], "active-using.cs", source, actual)
                        |> expectFailure [ "IdentifierToken" ]

                        Expect.equal (format options actual) actual "The permitted order is stable."

                Expect.equal
                    (format
                        PrinterOptions.Default
                        "using B;\nusing A;\n#if false\nclass X{}\n#endif\nclass D{}")
                    "using A;\nusing B;\n#if false\nclass X{}\n#endif\nclass D { }\n"
                    "An unrelated member conditional retains its existing separator."

                Expect.equal
                    (format
                        PrinterOptions.Default
                        "using B;\nusing A;\n#if WINDOWS\nusing Win32;\n#else\nusing AppKit;\n#endif\n\nnamespace N;\nclass D{}")
                    "using A;\nusing B;\n#if WINDOWS\nusing Win32;\n#else\nusing AppKit;\n#endif\n\nnamespace N;\n\nclass D { }\n"
                    "An approved final conditional using retains its one-blank separator."
            }
            test "using membership rejects boundary escapes without a token-order change" {
                let checker = TokenPreservation.Checker()

                for source, changed in
                    [
                        "#if true\nextern alias E;\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if true\nextern alias E;\n#endif\nusing B;\nusing A;\nclass D{}"
                        "#if !X\nnamespace N;\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if !X\nnamespace N;\n#endif\nusing B;\nusing A;\nclass D{}"
                        "using B;\n#if true\nusing A;\n#endif\nclass D{}",
                        "#if true\nusing B;\nusing A;\n#endif\nclass D{}"
                        "#if !X\nusing B;\n#endif\n#if !Y\nusing A;\n#endif\nclass D{}",
                        "#if !Y\nusing B;\n#endif\n#if !X\nusing A;\n#endif\nclass D{}"
                        "#if false\nusing Z;\n#else\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if false\nusing Z;\n#else\nusing B;\nusing A;\n#endif\nclass D{}"
                        "#if false\nusing Z;\n#elif Y\nusing C;\n#else\nusing B;\n#endif\nusing A;\nclass D{}",
                        "#if false\nusing Z;\n#elif X\nusing C;\n#else\nusing B;\n#endif\nusing A;\nclass D{}"
                    ] do
                    checker.CheckWith(PrinterOptions.Default, [], "using-frame.cs", source, changed)
                    |> expectOk

                    expectRefusedAndDiagnosedOrNot
                        (SyntaxPreservation.Checker())
                        "using-frame.cs"
                        source
                        changed
            }
            test "formatter preserves using frames opened before externs or namespaces" {
                let checker = SyntaxPreservation.Checker()

                let activeUsings (symbols: string array) (text: string) =
                    let options =
                        Microsoft.CodeAnalysis.CSharp
                            .CSharpParseOptions(
                                Microsoft.CodeAnalysis.CSharp.LanguageVersion.Preview
                            )
                            .WithPreprocessorSymbols(symbols)

                    let root =
                        Microsoft.CodeAnalysis.CSharp.CSharpSyntaxTree
                            .ParseText(text, options)
                            .GetRoot()

                    root.DescendantNodes()
                    |> Seq.choose (function
                        | :? Microsoft.CodeAnalysis.CSharp.Syntax.UsingDirectiveSyntax as node ->
                            Some(node.Name.ToString())
                        | _ -> None)
                    |> Seq.sort
                    |> Seq.toList

                let options =
                    configurations
                    @ [
                        "CRLF",
                        { PrinterOptions.Default with
                            EndOfLine = EndOfLine.CrLf
                        }
                    ]

                for _, options in options do
                    for source, sorts in
                        [
                            "#if !X\nextern alias E;\nusing Z;\n#endif\nusing B;\nusing A;\nclass D{}",
                            true
                            "#if !X\nnamespace N;\nusing Z;\n#endif\nusing B;\nusing A;\nclass D{}",
                            true
                            "namespace N{\n#if !X\nextern alias E;\nusing Z;\n#endif\nusing B;\nusing A;\nclass D{}}",
                            true
                            "#if !X\nextern alias E;\n#if !Y\nusing Z;\n#endif\nusing C;\n#endif\nusing B;\nusing A;\nclass D{}",
                            true
                            "#if !X\nextern alias E;\nusing Z;\n#if !Y\nusing Y;\n#endif\n#endif\nusing B;\nusing A;\nclass D{}",
                            true
                            "#if !X\nextern alias E;\nusing Z;\n#if Y\n#endif\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing Z;\n#if Y\n#else\n#endif\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing Z;\n#if Y\nusing Y;\n#endif\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing Z;\n#if !Y\nusing Y;\n#endif\n#if Y\n#endif\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if !X\nnamespace N;\nusing Z;\n#if Y\n#endif\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "namespace N{\n#if !X\nextern alias E;\nusing Z;\n#if Y\n#endif\n#endif\nusing B;\nusing A;\nclass D{}}",
                            false
                            "#if !X\nextern alias E;\n#if Y\n#endif\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if true\nextern alias E;\nusing V;\n#endif\n#if X\n#endif\nusing Z;\n#if true\n#endif\nusing A;\nclass D{}",
                            false
                            "#if true\nextern alias E;\n#endif\n#if X\n#endif\nusing Z;\n#if true\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing V;\n#endif\nusing B;\n#if true\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing V;\n#endif\nusing B;\n#if Y\nusing Y;\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing V;\n#endif\nusing B;\n#if !Y\nusing Y;\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !Y\nextern alias E;\nusing Z;\n#endif\n#if Y\nusing C;\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if !Y\nextern alias E;\nusing Z;\n#endif\nusing B;\n#if Y\nusing C;\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !Y\nextern alias E;\nusing Z;\n#endif\nusing B;\nusing A;\n#if Y\nusing C;\n#endif\nclass D{}",
                            false
                            "#if !Y\nextern alias E;\nusing Z;\n#endif\nusing B;\n#if Y\nusing C;\nusing Q;\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !Y\nextern alias E;\nusing Z;\n#endif\nusing B;\nusing A;\n#if Y\nusing C;\nusing Q;\n#endif\nclass D{}",
                            false
                            "#if !Y\nextern alias E;\nusing Z;\n#endif\nusing B;\n#if Y\nusing C;\n#endif\nusing A;\n",
                            false
                            "#if !Y\nextern alias E;\n#endif\nusing B;\n#if Y\nusing C;\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing Z;\n#endif\nusing B;\n#if X && Y\nusing C;\n#endif\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\n// csff-ignore-start\nusing   Z ;\n// csff-ignore-end\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\n// csff-ignore\nusing   Z;\n#endif\nusing B;\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\n// csff-ignore-start\nusing   Z;\n#endif\nusing B;\nusing A;\n// csff-ignore-end\nclass D{}",
                            false
                            "#if !X\nnamespace N;\n// csff-ignore-start\nusing   Z;\n#endif\nusing B;\nusing A;\n// csff-ignore-end\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing Z;\n// csff-ignore-start\nusing   Y;\n#endif\nusing B;\nusing A;\n// csff-ignore-end\nclass D{}",
                            false
                            "#if !X\nextern alias E;\n// csff-ignore-start\nusing   Z;\n#endif\nusing B;\n// csff-ignore-end\nusing A;\nclass D{}",
                            false
                            "#if true\n// csff-ignore-start\nextern alias E;\n// csff-ignore-end\n#endif\n// csff-ignore-start\nusing B;\n// csff-ignore-end\nusing A;\nclass D{}",
                            false
                            "#if true\n// csff-ignore\nextern alias E;\n#endif\n// csff-ignore-start\nusing B;\n// csff-ignore-end\nusing A;\nclass D{}",
                            false
                            "#if !X\nextern alias E;\nusing V;\n#endif\nusing C;\n// csff-ignore-start\nusing   B;\n// csff-ignore-end\nusing A;\nclass D{}",
                            false
                        ] do
                        let actual = format options source
                        checker.Check(options, "inherited-using.cs", source, actual) |> expectOk

                        if sorts then
                            let first = actual.IndexOf("using A;", StringComparison.Ordinal)
                            let second = actual.IndexOf("using B;", StringComparison.Ordinal)
                            Expect.isTrue (first >= 0 && first < second) "The outside run sorts."

                        let verdict = Csff.Gate.Adjudicator.adjudicate source actual 8

                        Expect.isEmpty
                            verdict.Findings
                            "Roslyn independently preserves each conditional import scope."

                        for symbols in [ [||]; [| "X" |]; [| "Y" |]; [| "X"; "Y" |] ] do
                            Expect.equal
                                (activeUsings symbols actual)
                                (activeUsings symbols source)
                                $"Active usings stay in their frames for symbols {symbols}."

                        for region in ignoredRegions source do
                            Expect.stringContains
                                (actual.Replace("\r\n", "\n"))
                                region
                                "Each ignored region keeps its original text."

                        Expect.equal (format options actual) actual "Inherited frames are stable."
            }
            test "formatter prefix preserves frames following define and undef" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "#define OTHER\n#if !X\nusing Z;\n#endif\nusing A;\nclass D{}\n"
                        "#undef OTHER\n#if !X\nusing Z;\n#endif\nusing A;\nclass D{}\n"
                        "#define OTHER\n#if !X\n#if !Y\nusing Z;\n#endif\nusing B;\n#endif\nusing A;\nclass D{}\n"
                        "#define OTHER\n#if OTHER\nusing Z;\n#endif\nusing A;\nclass D{}\n"
                        "#undef OTHER\n#if !OTHER\nusing Z;\n#endif\nusing A;\nclass D{}\n"
                        "#define OTHER\n#if !X\nusing Z;\n#endif\n#if !Y\nusing Y;\n#endif\nusing B;\nusing A;\nclass D{}\n"
                    ] do
                    for eol, endOfLine in [ "\n", EndOfLine.Lf; "\r\n", EndOfLine.CrLf ] do
                        let source = source.Replace("\n", eol)

                        let options =
                            { PrinterOptions.Default with
                                EndOfLine = endOfLine
                            }

                        let actual = format options source

                        checker.Check(options, "emitted-prefix-using.cs", source, actual)
                        |> expectOk

                        for symbols in [ [||]; [| "X" |]; [| "Y" |]; [| "X"; "Y" |] ] do
                            Expect.equal
                                (activeUsingNames symbols actual)
                                (activeUsingNames symbols source)
                                $"An emitted prefix keeps active import membership for {symbols}."

                        Expect.equal
                            (format options actual)
                            actual
                            "The fixed prefix is idempotent."
            }
            test
                "global using moved after ordinary using or using across extern alias is rejected in all layers" {
                let rule =
                    DeclaredTransformations.rules
                    |> List.find (fun rule -> rule.Name = "using directive permutation")

                let checker = TokenPreservation.Checker()
                let verifier = SyntaxPreservation.Checker()

                let sortedUsingsWitness = TransformationWitness.Searched

                for name, source, badOutput in
                    [
                        "global using moved after ordinary",
                        "global using Z;\nusing A;\nclass C{}\n",
                        "using A;\nglobal using Z;\nclass C{}\n"
                        "global using moved after second ordinary",
                        "using B;\nglobal using Z;\nusing A;\nclass C{}\n",
                        "using A;\nusing B;\nglobal using Z;\nclass C{}\n"
                        "using swapped across extern alias",
                        "using B;\nextern alias E;\nusing A;\nclass C{}\n",
                        "using A;\nextern alias E;\nusing B;\nclass C{}\n"
                        "using run moved across extern alias",
                        "using B;\nusing A;\nextern alias E;\nclass C{}\n",
                        "extern alias E;\nusing A;\nusing B;\nclass C{}\n"
                        "extern alias before usings moved after",
                        "extern alias E;\nusing B;\nusing A;\nclass C{}\n",
                        "using A;\nusing B;\nextern alias E;\nclass C{}\n"
                    ] do
                    Expect.equal
                        (rule.RewriteInput PrinterOptions.Default source badOutput)
                        source
                        $"{name}: declared using rule must reject invalid permutation."

                    let directExpected =
                        checker.Normalize(
                            PrinterOptions.Default,
                            source,
                            badOutput,
                            witness = sortedUsingsWitness,
                            allowDirectProof = true
                        )

                    Expect.isFalse
                        (checker.FastEquivalent(directExpected, badOutput))
                        $"{name}: Normalize(allowDirectProof)/tryStepUsingRun must reject invalid permutation."

                    let normSrc = "#nullable enable\n" + source
                    let normOut = "#nullable enable\n" + badOutput
                    let expected = checker.Normalize(PrinterOptions.Default, normSrc, normOut)

                    Expect.isFalse
                        (checker.FastEquivalent(expected, normOut))
                        $"{name}: FastEquivalent/pairUsings must reject invalid permutation."

                    checker.Check(PrinterOptions.Default, "bad-using-order.cs", source, badOutput)
                    |> expectFailure [ "undeclared token transformation" ]

                    Expect.notEqual
                        (verdict (
                            verifier.Decide(
                                PrinterOptions.Default,
                                "bad-using-order.cs",
                                source,
                                badOutput
                            )
                        ))
                        "proven"
                        $"{name}: SyntaxPreservation must not prove invalid output."

                for name, source, badOutput in
                    [
                        "conditional global using moved after ordinary",
                        "#if FOO\nglobal using Z;\nusing A;\n#endif\nclass C{}\n",
                        "#if FOO\nusing A;\nglobal using Z;\n#endif\nclass C{}\n"
                        "using moved across conditional extern alias",
                        "using Z;\n#if !FLAG\nusing W;\n#else\nextern alias X;\n#endif\nusing A;\nclass C{}\n",
                        "using A;\n#if !FLAG\nusing W;\n#else\nextern alias X;\n#endif\nusing Z;\nclass C{}\n"
                    ] do
                    Expect.notEqual
                        (verdict (
                            verifier.Decide(
                                PrinterOptions.Default,
                                "bad-cond-using-order.cs",
                                source,
                                badOutput
                            )
                        ))
                        "proven"
                        $"{name}: SyntaxPreservation must reject across conditional configurations."

                for name, source, badOutput in
                    [
                        "active conditional global using moved after ordinary",
                        "#if !FOO\nglobal using Z;\nusing A;\n#endif\nclass C{}\n",
                        "#if !FOO\nusing A;\nglobal using Z;\n#endif\nclass C{}\n"
                        "defined-flag using moved across conditional extern alias",
                        "#define FLAG\nusing Z;\n#if !FLAG\nusing W;\n#else\nextern alias X;\n#endif\nusing A;\nclass C{}\n",
                        "#define FLAG\nusing A;\n#if !FLAG\nusing W;\n#else\nextern alias X;\n#endif\nusing Z;\nclass C{}\n"
                    ] do
                    let condExpected = checker.Normalize(PrinterOptions.Default, source, badOutput)

                    Expect.isFalse
                        (checker.FastEquivalent(condExpected, badOutput))
                        $"{name}: FastEquivalent/pairUsings must reject invalid conditional permutation."

                    Expect.notEqual
                        (verdict (
                            verifier.Decide(
                                PrinterOptions.Default,
                                "bad-active-cond-using-order.cs",
                                source,
                                badOutput
                            )
                        ))
                        "proven"
                        $"{name}: SyntaxPreservation must reject invalid active conditional permutation."

                let validHoistSrc = "using A;\nglobal using Z;\nclass C{}\n"
                let validHoistOut = "global using Z;\nusing A;\nclass C{}\n"

                let validExpected =
                    checker.Normalize(
                        PrinterOptions.Default,
                        validHoistSrc,
                        validHoistOut,
                        witness = sortedUsingsWitness,
                        allowDirectProof = true
                    )

                Expect.isTrue
                    (Object.ReferenceEquals(validExpected, validHoistSrc))
                    "Normalize(allowDirectProof)/tryStepUsingRun must accept hoisting global using without fallback rewrite."

                Expect.isTrue
                    (checker.FastEquivalent(validExpected, validHoistOut))
                    "FastEquivalent after tryStepUsingRun must accept hoisting global using before ordinary."

                for name, source, goodOutput in
                    [
                        "global using hoisted before ordinary", validHoistSrc, validHoistOut
                        "usings sorted within extern alias segments",
                        "using C;\nusing B;\nextern alias E;\nusing Z;\nusing A;\nclass C{}\n",
                        "using B;\nusing C;\nextern alias E;\nusing A;\nusing Z;\nclass C{}\n"
                        "mutually exclusive branch global using sorted",
                        "#if DEBUG\nusing System.Diagnostics;\n#endif\n#if !DEBUG\nglobal using Z;\nglobal using A;\n#endif\nclass C{}\n",
                        "#if DEBUG\nusing System.Diagnostics;\n#endif\n#if !DEBUG\nglobal using A;\nglobal using Z;\n#endif\nclass C{}\n"
                    ] do
                    Expect.notEqual
                        (rule.RewriteInput PrinterOptions.Default source goodOutput)
                        source
                        $"{name}: declared using rule must accept valid permutation."

                    checker.Check(PrinterOptions.Default, "good-using-order.cs", source, goodOutput)
                    |> expectOk

                    Expect.equal
                        (verdict (
                            verifier.Decide(
                                PrinterOptions.Default,
                                "good-using-order.cs",
                                source,
                                goodOutput
                            )
                        ))
                        "proven"
                        $"{name}: SyntaxPreservation must prove valid output."
            }
            test "formatter prefix separates formatted and ignored usings" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "#if !X\nnamespace N;\nusing A;\n#if true\n// csff-ignore-start\nusing   Z ;\n// csff-ignore-end\n#endif\nclass D{}\n#endif\n"
                        "#if !X\nnamespace N;\nusing A;\n// csff-ignore-start\nusing   Z ;\nusing   Y ;\n// csff-ignore-end\nclass D{}\n#endif\n"
                        "#if !X\nextern alias E;\nusing A;\n#if true\n// csff-ignore-start\nusing   Z ;\nusing   Y ;\n// csff-ignore-end\n#endif\n#endif\nclass D{}\n"
                        "#if !X\nextern alias E;\nusing A;\n// csff-ignore-start\nusing   Z ;\nusing   Y ;\n// csff-ignore-end\n#endif\nclass D{}\n"
                        "#if !X\nnamespace N{\nusing A;\n// csff-ignore-start\nusing   Z ;\nusing   Y ;\n// csff-ignore-end\nclass D{}\n}\n#endif\n"
                    ] do
                    for eol, endOfLine in [ "\n", EndOfLine.Lf; "\r\n", EndOfLine.CrLf ] do
                        let source = source.Replace("\n", eol)

                        let options =
                            { PrinterOptions.Default with
                                EndOfLine = endOfLine
                            }

                        let actual = format options source

                        checker.Check(options, "inherited-ignored-using.cs", source, actual)
                        |> expectOk

                        for symbols in [ [||]; [| "X" |] ] do
                            Expect.equal
                                (activeUsingNames symbols actual)
                                (activeUsingNames symbols source)
                                "Ignored imports retain their conditional membership."

                        Expect.equal
                            (format options actual)
                            actual
                            "Neither directives nor ignore markers attach to a preceding using."
            }

            test "formatter prefix exact layouts stay stable" {
                for name, source, expected in conditionalUsingLayouts do
                    for eol, endOfLine in [ "\n", EndOfLine.Lf; "\r\n", EndOfLine.CrLf ] do
                        let options =
                            { PrinterOptions.Default with
                                EndOfLine = endOfLine
                            }

                        let actual = format options (source.Replace("\n", eol))
                        Expect.equal actual (expected.Replace("\n", eol)) $"{name}: exact bytes."
                        Expect.equal (format options actual) actual $"{name}: exact idempotence."
            }
            test "formatter prefix keeps the protected region byte for byte" {
                for source in
                    [
                        "#if !X\nnamespace N;\nusing A;\n#if true\n// csff-ignore-start\nusing   Z ;\n// csff-ignore-end\n#endif\nclass D{}\n#endif\n"
                        "#if !X\nnamespace N;\nusing A;\n// csff-ignore-start\nusing   Z ;\nusing   Y ;\n// csff-ignore-end\nclass D{}\n#endif\n"
                        "namespace N;\nusing A;\n// csff-ignore-start\nusing   Z ;\nusing   Y ;\n// csff-ignore-end\nclass D{}\n"
                        "namespace N;\nusing A;\n// csff-ignore-start\nusing   Z ;\n// csff-ignore-end\nclass D{}\n"
                        "using A;\n// csff-ignore-start\nusing   Z ;\nusing   Y ;\n// csff-ignore-end\nclass D{}\n"
                        "using A;\n// csff-ignore-start\nusing   Z ;\n\nusing   Y ;\n\n// csff-ignore-end\nclass D{}\n"
                        "// csff-ignore-start\nusing Z;\n\n// csff-ignore-end\n"
                        "// csff-ignore-start\nusing Z;\n// csff-ignore-end\n"
                        "// csff-ignore-start\nusing Z;\n\n// csff-ignore-end\nusing A;\n"
                        "#if !X\nextern alias E;\n// csff-ignore-start\nusing   Z;\n#endif\nusing B;\nusing A;\n// csff-ignore-end\nclass D{}\n"
                        "#if !X\nnamespace N;\n// csff-ignore-start\nusing   Z;\n#endif\nusing B;\nusing A;\n// csff-ignore-end\nclass D{}\n"
                        "namespace N{\n#if !X\nextern alias E;\n// csff-ignore-start\nusing   Z;\n#endif\nusing B;\nusing A;\n    // csff-ignore-end\nclass D{}}\n"
                        "#if !X\nextern alias E;\nusing Z;\n// csff-ignore-start\nusing   Y;\n#endif\nusing B;\nusing A;\n// csff-ignore-end\nclass D{}\n"
                        "#if true\n// csff-ignore-start\nextern alias E;\n// csff-ignore-end\n#endif\n// csff-ignore-start\nusing B;\n// csff-ignore-end\nusing A;\nclass D{}\n"
                        "#if !X\nextern alias E;\nusing V;\n#endif\nusing C;\n// csff-ignore-start\nusing   B;\n// csff-ignore-end\nusing A;\nclass D{}\n"
                    ] do
                    for eol, endOfLine in [ "\n", EndOfLine.Lf; "\r\n", EndOfLine.CrLf ] do
                        let source = source.Replace("\n", eol)

                        let options =
                            { PrinterOptions.Default with
                                EndOfLine = endOfLine
                            }

                        let actual = format options source

                        for region in ignoredRegions source do
                            Expect.stringContains
                                actual
                                region
                                "The complete protected region keeps its exact bytes."

                        Expect.equal
                            (format options actual)
                            actual
                            "A region that kept its bytes keeps them on the next pass too."
            }
            test "ignored usings leave a stable namespace closing indent" {
                let region = "    // csff-ignore-start\n    using   Q ;\n    // csff-ignore-end"

                for before, after in
                    [
                        "", "\n    using A;"
                        "    using B;\n", "\n    using A;"
                        "    using B;\n", ""
                    ] do
                    for memberText in [ ""; "    class C {}\n" ] do
                        for eol, endOfLine in [ "\n", EndOfLine.Lf; "\r\n", EndOfLine.CrLf ] do
                            let options =
                                { PrinterOptions.Default with
                                    EndOfLine = endOfLine
                                }

                            let source =
                                $"namespace N\n{{\n{before}{region}{after}\n{memberText}}}\n"
                                    .Replace("\n", eol)

                            let actual = format options source

                            Expect.stringContains
                                actual
                                (region.Replace("\n", eol))
                                "The ignored span retains its bytes."

                            Expect.isTrue
                                (actual.EndsWith(eol + "}" + eol, StringComparison.Ordinal))
                                "The namespace closer resumes the outer indentation on pass one."

                            Expect.equal
                                (format options actual)
                                actual
                                "Sorting around the ignored span reaches a fixed point on pass one."
            }
            test "formatter sorts usings that follow a frame holding an extern or namespace" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "#if !X\nextern alias E;\nusing Z;\n#endif\nusing B;\nusing A;\nclass D{}"
                        "#if !X\nnamespace N;\nusing Z;\n#endif\nusing B;\nusing A;\nclass D{}"
                        "namespace N{\n#if !X\nextern alias E;\nusing Z;\n#endif\nusing B;\nusing A;\nclass D{}}"
                    ] do
                    let actual = format PrinterOptions.Default source

                    checker.CheckWith(
                        PrinterOptions.Default,
                        [],
                        "inherited-using.cs",
                        source,
                        actual
                    )
                    |> expectFailure [ "IdentifierToken" ]
            }
            test "an inactive arm whose tokens changed is not preserved" {
                let checker = TokenPreservation.Checker()

                let changed =
                    [
                        "an identifier inside the arm",
                        "#if A && !A\nclass D { int x; }\n#endif\nclass C { }\n",
                        "#if A && !A\nclass D { int y; }\n#endif\nclass C { }\n"

                        "a token dropped from the arm",
                        "#if A && !A\nclass D { int x; }\n#endif\nclass C { }\n",
                        "#if A && !A\nclass D { int; }\n#endif\nclass C { }\n"

                        "a token added to the arm",
                        "#if A && !A\nclass D { }\n#endif\nclass C { }\n",
                        "#if A && !A\nclass D { int x; }\n#endif\nclass C { }\n"

                        "a nested arm, two frames deep",
                        "#if A && !A\n#if B\nclass D { int x; }\n#endif\n#endif\nclass C { }\n",
                        "#if A && !A\n#if B\nclass D { int y; }\n#endif\n#endif\nclass C { }\n"

                        "an arm at end of file with no trailing newline",
                        "class C { }\n#if A && !A\nclass D { int x; }\n#endif",
                        "class C { }\n#if A && !A\nclass D { int y; }\n#endif"

                        "a string literal's contents inside the arm",
                        "#if A && !A\nclass D { string s = \"p\"; }\n#endif\nclass C { }\n",
                        "#if A && !A\nclass D { string s = \"q\"; }\n#endif\nclass C { }\n"
                    ]

                for label, source, formatted in changed do
                    Expect.isFalse
                        (checker.LexicallyPreserved(source, formatted))
                        $"%s{label}: the arm's text differs, so the lexical proof declines."

                    let expected = checker.Normalize(PrinterOptions.Default, source, formatted)

                    Expect.isFalse
                        (checker.FastEquivalent(expected, formatted))
                        $"%s{label}: a change inside an arm no configuration activates must not be proven equivalent."
            }
            test "an inactive arm's non-ASCII characters are held" {
                let checker = TokenPreservation.Checker()

                let source = "class C {\n#if NEVER\nclass D { int \u00e9 = 1; }\n#endif\n}\n"

                let reindented =
                    "class C {\n#if NEVER\n    class D { int \u00e9 = 1; }\n#endif\n}\n"

                Expect.isFalse
                    (checker.LexicallyPreserved(source, reindented))
                    "The arm's text differs, so the lexical proof declines and the walk decides."

                Expect.isTrue
                    (checker.FastEquivalent(
                        checker.Normalize(PrinterOptions.Default, source, reindented),
                        reindented
                    ))
                    "The same characters, moved, must be proven."

                let changed = "class C {\n#if NEVER\nclass D { int \u00e8 = 1; }\n#endif\n}\n"

                Expect.isFalse
                    (checker.LexicallyPreserved(source, changed))
                    "The arm's text differs, so the lexical proof declines and the walk decides."

                Expect.isFalse
                    (checker.FastEquivalent(
                        checker.Normalize(PrinterOptions.Default, source, changed),
                        changed
                    ))
                    "A character above 127 changed inside an arm must not be proven equivalent."
            }
            test "reindenting an inactive arm is preserved" {
                let checker = SyntaxPreservation.Checker()

                let source = "class C {\n#if NEVER\nclass D { int x; }\n#endif\n}\n"

                let formatted = "class C {\n#if NEVER\n    class D { int x; }\n#endif\n}\n"

                checker.Check(PrinterOptions.Default, "reindented.cs", source, formatted)
                |> expectOk

                let sortedSource = "namespace N\n{\n#if NEVER\nusing Z;\nusing Y;\n#endif\n}\n"

                let sortedFormatted = "namespace N\n{\n#if NEVER\nusing Y;\nusing Z;\n#endif\n}\n"

                checker.Check(
                    PrinterOptions.Default,
                    "sorted-arm.cs",
                    sortedSource,
                    sortedFormatted
                )
                |> expectOk
            }
            test "the comment comparison accepts every comment kind the print reindents" {
                let verifier = SyntaxPreservation.Checker()
                let printed = format PrinterOptions.Default commentShapes

                Expect.notEqual
                    printed
                    commentShapes
                    "The fixture must be one the printer rewrites."

                Expect.notEqual
                    (comments printed)
                    (comments commentShapes)
                    "The print must change the comments' own text, or nothing is compared."

                verifier.Check(PrinterOptions.Default, "shapes.cs", commentShapes, printed)
                |> expectOk

                verifier.Adjudicate(PrinterOptions.Default, "shapes.cs", commentShapes, printed)
                |> expectOk
            }

            test "the comment comparison accepts a comment at either end of a file" {
                let verifier = SyntaxPreservation.Checker()
                let leading = csharp "// only a comment\nclass C{}\n"
                let trailing = csharp "class C{}\n// after the last member\n"

                let unterminated = trailing.TrimEnd('\n')

                Expect.isFalse
                    (unterminated.EndsWith("\n", StringComparison.Ordinal))
                    "The fixture must end without a newline."

                let docRun =
                    csharp "/// <summary>s</summary>\n/// <remarks>r</remarks>\nclass C{}\n"

                for name, source, word in
                    [
                        "leading.cs", leading, "only"
                        "trailing.cs", trailing, "last"
                        "unterminated.cs", unterminated, "last"
                        "doc-run.cs", docRun, "<remarks>"
                    ] do
                    let printed = format PrinterOptions.Default source
                    Expect.notEqual printed source (name + ": the printer must rewrite it.")

                    verifier.Check(PrinterOptions.Default, name, source, printed) |> expectOk

                    verifier.Adjudicate(PrinterOptions.Default, name, source, printed) |> expectOk

                    let mutated = replaceOnce word (word + "X") printed

                    match verifier.Check(PrinterOptions.Default, name, source, mutated) with
                    | Ok() -> failtest (name + ": a changed comment here was accepted.")
                    | Error message ->
                        Expect.stringContains
                            message
                            "changed a comment"
                            (name + ": the comment comparison must be what names it.")
            }

            test "the comment comparison accepts the comments a sorted using run moves" {
                let verifier = SyntaxPreservation.Checker()
                let printed = format PrinterOptions.Default commentedUsings

                Expect.notEqual
                    (comments printed)
                    (comments commentedUsings)
                    "Sorting the usings must move the comments past each other."

                Expect.equal
                    (List.sort (comments printed))
                    (List.sort (comments commentedUsings))
                    "Sorting the usings must not change which comments the file holds."

                verifier.Check(PrinterOptions.Default, "usings.cs", commentedUsings, printed)
                |> expectOk

                verifier.Adjudicate(PrinterOptions.Default, "usings.cs", commentedUsings, printed)
                |> expectOk

                for name, source in
                    [
                        "sorted-doc-usings.cs",
                        "/// about zebra\nusing Zebra;\n/// about alpha\nusing Alpha;\n"
                        "sorted-doc-usings-with-line-comment.cs",
                        "/// header\nusing Zebra;\n// about beta\nusing Beta;\n/// about alpha\nusing Alpha;\n"
                        "blank-between-doc-comments.cs",
                        "using System;\n/// a\n\n/// b\nusing System.IO;\n"
                        "region-doc-comments.cs",
                        "using System;\n#region\n/// a\n\n/// b\n#endregion\nclass P { }\n"
                        "if-usings-doc-comments.cs",
                        "using Z;\n/// a\n#if FOO\nusing Bar;\n#endif\n/// b\nusing A;\n"
                        "overlapping-merged-doc-usings.cs",
                        "using Z;\n// first\nusing Y;\n/// a\n/// b\n\n/// x\nusing X;\n/// a\n\n/// b\nusing A;\nclass C {}\n"
                        "overlapping-merged-doc-usings-no-line-comment.cs",
                        "using Z;\n/// a\n/// b\n\n/// x\nusing X;\n/// a\n\n/// b\nusing A;\nclass C {}\n"
                        "cross-token-jump-not-preferred-over-own-group.cs",
                        "using Z;\n// first\nusing Y;\n/// c\n\n/// b\nusing D;\n/// b\n/// b\nusing C;\n/// c\n\n/// b\n/// b\n/// b\nusing A;\nclass K {}\n"
                        "unchanged-multiset-with-preserved-blank-line-doc-comments.cs",
                        "using Z;\n// z\nusing Y;\n// a\nusing A;\n/// a\n\n/// b\nclass C {}\n/// a\n/// b\n\n/// x\nnamespace N {\nusing Z;\n// z2\nusing Y;\n// a2\nusing A;\n}\n"
                        "two-regions-on-one-token-after-sorted-usings.cs",
                        "using Z;\n// z\nusing A;\n#region R1\n/// a\n\n/// b\n#endregion\n#region R2\n/// c\n\n/// d\n#endregion\nclass C {}\n"
                        "repeated-header-and-later-using-doc-comment.cs",
                        "/// h\nusing Z;\n/// s\nusing A;\n// tail\nusing Y;\n/// h\nusing B;\n"
                        "duplicate-multiline-header-and-later-using.cs",
                        "/// a\n/// b\nusing Z;\n/// a\nusing A;\n// c\nusing C;\n/// a\n/// b\nusing B;\n"
                        "multipart-header-last-part-merged-with-duplicate-suffix.cs",
                        "/// h\n\n/// a\nusing Z;\n// normal\n/// c\nusing Y;\n/// c\nusing D;\n"
                        "duplicate-header-and-sorted-across-namespaces.cs",
                        "namespace N1 {\n/// h\nusing Z;\n/// s\nusing A;\n}\nnamespace N2 {\n/// h\nusing Z;\n/// s\nusing A;\n}\n"
                        "duplicate-sorted-group.cs",
                        "/// h\nusing Z;\n// normal\n/// s\n/// s\nusing Y;\n/// s\n/// s\nusing A;\n"
                        "overlap-combined-sorted-group.cs",
                        "/// h\nusing Z;\n// normal\n/// a\n\n/// b\nusing Y;\n/// a\n/// b\nusing A;\n"
                        "two-headers-across-namespaces.cs",
                        "using Z;\n// z\nusing Y;\n// a\nusing A;\nnamespace N1 {\n/// a\n/// b\nusing A;\n/// s1\nusing Z;\n}\nnamespace N2 {\n/// a\n/// b\nusing Z;\n/// s2\nusing A;\n}\n"
                        "partial-sorted-group.cs",
                        "extern alias X;\n/// h\nusing Z;\n/// c\nusing B;\n/// a\n\n/// b\nusing A;\nclass C {}\n"
                        "greedy-duplicate.cs",
                        "/// a\n/// b\nusing A;\n/// x\nusing B;\nnamespace N {\n/// a\n\n/// a\nusing Z;\n/// b\nusing B;\n/// a\n\n/// b\nusing A;\n}\n"
                        "global-using-doc-comments.cs",
                        "/// h\nglobal using Z;\n/// s\nglobal using A;\n"
                        "retained-conditional-doc-comments.cs",
                        "/// h\nusing Z;\n/// a\n\n/// b\n#if false\nusing Disabled;\n#endif\n/// c\n\n/// d\nusing A;\n"
                        "unchanged-multipart-partkey.cs",
                        "/// a\n/// b\n\n/// a\nusing A;\n/// a\nusing C;\n/// b\n\n/// a\nusing B;\n"
                        "overlapping-doc-groups-supply.cs",
                        "/// a\nusing Z;\n/// b\n\n/// a\nusing Y;\n/// a\n/// b\n\n/// a\nusing W;\n/// b\nusing U;\nclass C {}\n"
                        "bridged-vs-unbridged-candidate-priority.cs",
                        "/// a\n#if false\n#endif\n/// b\nusing Z;\n/// a\n\n/// a\nusing X;\n/// a\n\n/// b\nusing U;\n/// a\nusing T;\nclass C {}\n"
                        "overlapping-region-and-sorted-doc-groups.cs",
                        "/// a\nusing Z;\n/// a\n/// b\n\n/// a\nusing Y;\n/// b\n\n/// a\nusing W;\n#region R\n/// a\n\n/// b\n#endregion\nusing U;\nclass C {}\n"
                        "repeated-single-region-before-merged-region.cs",
                        "using Z;\n// b\nusing B;\n// a\nusing A;\n"
                        + String.replicate 32 "#region R\n/// a\n#endregion\n"
                        + "#region R\n/// b\n#endregion\n#region R\n"
                        + String.replicate 33 "/// a\n\n"
                        + "#endregion\nclass C {}\n"
                        "repeated-merged-doc-usings.cs",
                        "using Z;\n// first\nusing Y;\n"
                        + String.replicate 24 "/// a\n"
                        + "\n/// x\nusing X;\n"
                        + String.replicate 24 "/// a\n\n"
                        + "using A;\nclass C {}\n"
                        "multi-namespace-header-merges-and-unmerged.cs",
                        "/// b\nusing B;\n/// a\nusing A;\nnamespace N1 {\n/// b\nusing B;\n/// a\nusing A;\n}\nnamespace N2 {\n/// b\n/// a\nusing A;\nusing B;\n}\n"
                        "unmerged-multiline-before-sorted-using-and-merged-namespace.cs",
                        "/// b\n/// a\n#if true\n#endif\nusing B;\n/// b\nusing A;\nnamespace N {\n/// b\nusing B;\n/// a\nusing A;\nclass C {}\n}\n"
                        "repeated-nested-doc-groups-in-regions.cs",
                        "using Z;\n// z\nusing Y;\n// a\nusing A;\n"
                        + String.replicate
                            64
                            "#region R\n/// a\n/// b\n\n/// c\n#endregion\n#region R\n/// a\n\n/// b\n#endregion\n"
                        + "class C {}\n"
                    ] do
                    let printed = format PrinterOptions.Default source
                    verifier.Check(PrinterOptions.Default, name, source, printed) |> expectOk
                    verifier.Adjudicate(PrinterOptions.Default, name, source, printed) |> expectOk
            }

            test "the comment comparison accepts the comments a sorted modifier run moves" {
                let verifier = SyntaxPreservation.Checker()

                let kept = format PrinterOptions.Default commentedModifiers

                Expect.isLessThan
                    (kept.IndexOf("unsafe", StringComparison.Ordinal))
                    (kept.IndexOf("public class", StringComparison.Ordinal))
                    $"A comment in front of a later word keeps the run in source order: {kept}"

                let printed =
                    "// title\npublic unsafe // area\nclass UC\n{\n    public int* p;\n}\n"

                Expect.notEqual
                    (comments printed)
                    (comments commentedModifiers)
                    "Sorting the modifiers must move the comments past each other."

                Expect.equal
                    (List.sort (comments printed))
                    (List.sort (comments commentedModifiers))
                    "Sorting the modifiers must not change which comments the file holds."

                let verdict =
                    verifier.Check(
                        PrinterOptions.Default,
                        "modifiers.cs",
                        commentedModifiers,
                        printed
                    )

                let message = Expect.wantError verdict "The walk cannot prove this fixture."

                Expect.isTrue
                    (message.StartsWith("unprovable:", StringComparison.Ordinal))
                    $"The refusal must be the absent proof, not the comment comparison: %s{message}"

                Expect.isFalse
                    (message.Contains "changed a comment")
                    $"The comments a sorted modifier run moves must be accepted: %s{message}"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "modifiers.cs",
                    commentedModifiers,
                    printed
                )
                |> expectOk
            }

            test "the comment comparison accepts the print under every line ending" {
                let verifier = SyntaxPreservation.Checker()

                for name, ending in lineEndings do
                    let options =
                        { PrinterOptions.Default with
                            EndOfLine = ending
                        }

                    let printed = format options multiLineComments

                    Expect.notEqual
                        (comments printed)
                        (comments multiLineComments)
                        (name + ": the print must change the comments' own text.")

                    verifier.Check(options, name + ".cs", multiLineComments, printed) |> expectOk

                    verifier.Adjudicate(options, name + ".cs", multiLineComments, printed)
                    |> expectOk

                    for find, replace in
                        [
                            "<summary>first", "<summary>firstX"
                            "interior", "inferior"
                            "* second", "* secondX"
                        ] do
                        let mutated = replaceOnce find replace printed

                        match verifier.Check(options, name + ".cs", multiLineComments, mutated) with
                        | Ok() ->
                            failtest (name + ": a changed comment was accepted (" + find + ").")
                        | Error message ->
                            Expect.stringContains
                                message
                                "changed a comment"
                                (name + ": the comment comparison must name it.")
            }

            test "a comment the output rewrites, retypes, drops or repeats is refused" {
                let verifier = SyntaxPreservation.Checker()
                let printed = format PrinterOptions.Default commentShapes

                let expectRefused name (result: Result<unit, string>) =
                    match result with
                    | Ok() -> failtest (name + ": verification accepted the output.")
                    | Error message ->
                        Expect.stringContains
                            message
                            "changed a comment"
                            (name + ": the comment comparison must be what names it.")

                let defects =
                    [
                        "the text of a line comment changed", "// one", "// uno"
                        "a line comment deleted", "    // two\n", ""
                        "the body of a doc comment changed", "doc first", "doc changed"
                        "a line comment rewritten as a block comment", "// one", "/* one */"
                        "two block comments rewritten as one line comment",
                        "/* a */ /* b */",
                        "// a b"
                        "a doc block rewritten as a plain block", "/** doc block", "/* doc block"
                        "a line comment repeated", "    // one\n", "    // one\n    // one\n"
                        "an interior line of a block comment changed", "interior", "inferior"
                        "a line dropped from a doc run",
                        "    /// <remarks>doc second</remarks>\n",
                        ""
                        "two lines of a doc run swapped",
                        "    /// <summary>doc first</summary>\n    /// <remarks>doc second</remarks>\n",
                        "    /// <remarks>doc second</remarks>\n    /// <summary>doc first</summary>\n"
                    ]

                for name, find, replace in defects do
                    let mutated = replaceOnce find replace printed

                    verifier.Check(PrinterOptions.Default, "shapes.cs", commentShapes, mutated)
                    |> expectRefused name

                    verifier.Adjudicate(PrinterOptions.Default, "shapes.cs", commentShapes, mutated)
                    |> expectRefused name

                let twoDocRuns = "/// first\n\n/// second\nclass C { }\n"
                let swappedDocRuns = "/// second\n/// first\nclass C { }\n"

                verifier.Check(
                    PrinterOptions.Default,
                    "swapped-runs.cs",
                    twoDocRuns,
                    swappedDocRuns
                )
                |> expectRefused "two merged doc runs swapped"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "swapped-runs.cs",
                    twoDocRuns,
                    swappedDocRuns
                )
                |> expectRefused "two merged doc runs swapped"

                let twoMethodsDoc =
                    "class C {\n/// <summary>A</summary>\nvoid A(){}\n/// <summary>B</summary>\nvoid B(){}\n}\n"

                let mergedMethodsDoc =
                    "class C {\nvoid A(){}\n/// <summary>A</summary>\n/// <summary>B</summary>\nvoid B(){}\n}\n"

                verifier.Check(
                    PrinterOptions.Default,
                    "merged-methods.cs",
                    twoMethodsDoc,
                    mergedMethodsDoc
                )
                |> expectRefused "doc comments merged across separate methods"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "merged-methods.cs",
                    twoMethodsDoc,
                    mergedMethodsDoc
                )
                |> expectRefused "doc comments merged across separate methods"

                let twoUsingVarsDoc =
                    "using Z;\n// c\nusing A;\nclass C {\nvoid M1() {\n/// h\nusing var x = d1;\n}\nvoid M2() {\n/// s\nusing var y = d2;\n}\n}\n"

                let mergedUsingVarsDoc =
                    "using A;\n// c\nusing Z;\nclass C {\nvoid M1() {\nusing var x = d1;\n}\nvoid M2() {\n/// h\n/// s\nusing var y = d2;\n}\n}\n"

                verifier.Check(
                    PrinterOptions.Default,
                    "merged-using-vars.cs",
                    twoUsingVarsDoc,
                    mergedUsingVarsDoc
                )
                |> expectRefused "doc comments merged across local using declarations"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "merged-using-vars.cs",
                    twoUsingVarsDoc,
                    mergedUsingVarsDoc
                )
                |> expectRefused "doc comments merged across local using declarations"

                let crossNamespaceUsingsDoc =
                    "namespace N1 {\nusing Z;\n// c\nusing A;\n/// h\nusing B;\n}\nnamespace N2 {\n/// s\nusing D;\n}\n"

                let mergedCrossNamespaceUsingsDoc =
                    "namespace N1 {\n// c\nusing A;\nusing B;\nusing Z;\n}\nnamespace N2 {\n/// h\n/// s\nusing D;\n}\n"

                verifier.Check(
                    PrinterOptions.Default,
                    "merged-across-namespaces.cs",
                    crossNamespaceUsingsDoc,
                    mergedCrossNamespaceUsingsDoc
                )
                |> expectRefused "doc comments merged across separate namespace using runs"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "merged-across-namespaces.cs",
                    crossNamespaceUsingsDoc,
                    mergedCrossNamespaceUsingsDoc
                )
                |> expectRefused "doc comments merged across separate namespace using runs"

                let borrowedMethodDocsForUsingHeader =
                    "using B;\n/// b\n/// a\nusing A;\nclass C {\n    /// a\n    void M1() {}\n    /// b\n    void M2() {}\n}\n"

                let mutatedBorrowedMethodDocs =
                    "/// b\n/// a\nusing A;\nusing B;\nclass C {\n    /// b\n    /// a\n    void M1() {}\n    void M2() {}\n}\n"

                verifier.Check(
                    PrinterOptions.Default,
                    "borrowed-method-docs.cs",
                    borrowedMethodDocsForUsingHeader,
                    mutatedBorrowedMethodDocs
                )
                |> expectRefused "method doc comments merged by borrowing using header candidate"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "borrowed-method-docs.cs",
                    borrowedMethodDocsForUsingHeader,
                    mutatedBorrowedMethodDocs
                )
                |> expectRefused "method doc comments merged by borrowing using header candidate"

                let crossNamespaceHeaderMerge =
                    "using B;\n/// a\nusing A;\nnamespace N {\n    using D;\n    /// b\n    using C;\n}\n"

                let mutatedCrossNamespaceHeaderMerge =
                    "/// b\n/// a\nusing A;\nusing B;\nnamespace N {\n    using C;\n    using D;\n}\n"

                verifier.Check(
                    PrinterOptions.Default,
                    "cross-namespace-header-merge.cs",
                    crossNamespaceHeaderMerge,
                    mutatedCrossNamespaceHeaderMerge
                )
                |> expectRefused "doc comments merged across top-level and namespace using runs"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "cross-namespace-header-merge.cs",
                    crossNamespaceHeaderMerge,
                    mutatedCrossNamespaceHeaderMerge
                )
                |> expectRefused "doc comments merged across top-level and namespace using runs"

                let threeConditionalDocGroups =
                    "/// a\n#if false\n#endif\n/// b\n#if false\n#endif\n/// c\nusing A;\n"

                let skippedMiddleConditionalDocGroup =
                    "/// a\n/// c\n#if false\n#endif\n/// b\n#if false\n#endif\nusing A;\n"

                verifier.Check(
                    PrinterOptions.Default,
                    "skipped-middle-doc-group.cs",
                    threeConditionalDocGroups,
                    skippedMiddleConditionalDocGroup
                )
                |> expectRefused "nonconsecutive doc comment groups merged across intervening group"

                verifier.Adjudicate(
                    PrinterOptions.Default,
                    "skipped-middle-doc-group.cs",
                    threeConditionalDocGroups,
                    skippedMiddleConditionalDocGroup
                )
                |> expectRefused "nonconsecutive doc comment groups merged across intervening group"
            }

            test "the comment layout the printer owns is admitted on purpose" {
                let verifier = SyntaxPreservation.Checker()
                let printed = format PrinterOptions.Default commentShapes

                let admitted =
                    [
                        "trailing whitespace inside a comment", "// one", "// one   "
                        "an interior line of a block comment reindented", "   interior", "interior"
                    ]

                for name, find, replace in admitted do
                    let mutated = replaceOnce find replace printed
                    Expect.notEqual mutated printed (name + ": the edit must change the output.")

                    verifier.Check(PrinterOptions.Default, "admitted.cs", commentShapes, mutated)
                    |> expectOk

                    verifier.Adjudicate(
                        PrinterOptions.Default,
                        "admitted.cs",
                        commentShapes,
                        mutated
                    )
                    |> expectOk
            }
            test "an arm pairs with an arm that holds code, not with whitespace" {
                let checker = TokenPreservation.Checker()

                let source =
                    "class C {\n#if NEVER\n\n#endif\n#if ALSO\nclass D { int x; }\n#endif\n}\n"

                let formatted =
                    "class C {\n#if NEVER\n#endif\n#if ALSO\n    class D { int x; }\n#endif\n}\n"

                Expect.isTrue
                    (checker.LexicallyPreserved(source, formatted) |> not)
                    "The arms' text differs, so the lexical proof declines."

                let expected = checker.Normalize(PrinterOptions.Default, source, formatted)

                Expect.isTrue
                    (checker.FastEquivalent(expected, formatted))
                    "An empty arm must not consume the pairing slot of one holding code."
            }
        ]
    |> testSequenced

let private tokensBefore (text: string) (marker: string) =
    let at = text.IndexOf(marker, StringComparison.Ordinal)
    Expect.isGreaterThan at -1 ("the fixture must contain " + marker)
    let tree = SyntaxTree()
    Parser.lexOnly text tree
    let buffer = tree.LexerBuffer
    let mutable count = 0

    for index = 0 to buffer.TokenCount - 1 do
        let token = buffer.Token index

        if token.Start + token.Length <= at then
            count <- count + 1

    count

let private directiveLines =
    testList
        "directive lines"
        [
            test "a corrupted directive line is named, not merely left unproven" {
                let checker = SyntaxPreservation.Checker()

                let cases =
                    [
                        "code-swallowed-onto-a-false-if-line",
                        "class C\n{\n    void M()\n    {\n#if false\n        Dead();\n#endif\n    }\n}\n",
                        "class C\n{\n    void M()\n    {\n#if false Dead();\n#endif\n    }\n}\n"

                        "code-swallowed-onto-the-else-of-a-constant-condition",
                        "class C\n{\n    void M()\n    {\n#if true\n        Live();\n#else\n        Dead();\n#endif\n    }\n}\n",
                        "class C\n{\n    void M()\n    {\n#if true\n        Live();\n#else Dead();\n#endif\n    }\n}\n"

                        "error-directive-message-changed",
                        "#error the old message\n\nclass C { }\n",
                        "#error a different message\n\nclass C { }\n"
                    ]

                for label, source, formatted in cases do
                    let message =
                        Expect.wantError
                            (checker.Check(PrinterOptions.Default, label + ".cs", source, formatted))
                            $"%s{label}: the output must be refused."

                    Expect.stringContains
                        message
                        "changed a preprocessor directive line"
                        $"%s{label}: the refusal must name a rule."

                    Expect.equal
                        (verdict (
                            checker.Decide(PrinterOptions.Default, label + ".cs", source, formatted)
                        ))
                        "violation"
                        $"%s{label}: a named rule is a violation, not an unproven file."
            }

            test "indentation and the line terminator are the only liberties over a line" {
                let allowed =
                    [
                        "the directive is indented",
                        "class C\n{\n#if A\n    int x;\n#endif\n}\n",
                        "class C\n{\n    #if A\n    int x;\n#endif\n}\n"

                        "the directive's indentation is removed",
                        "class C\n{\n\t#if A\n    int x;\n#endif\n}\n",
                        "class C\n{\n#if A\n    int x;\n#endif\n}\n"

                        "the line terminator becomes CRLF",
                        "#if A\nclass C { }\n#endif\n",
                        "#if A\r\nclass C { }\r\n#endif\r\n"

                        "trailing blanks after the payload are dropped",
                        "#if A   \nclass C { }\n#endif\n",
                        "#if A\nclass C { }\n#endif\n"
                    ]

                for label, source, formatted in allowed do
                    Expect.isNull
                        (TriviaPreservation.difference source formatted)
                        $"%s{label}: the formatter owns the indentation and the terminator."
            }

            test "whitespace inside a directive's payload is not normalised" {
                Expect.isNotNull
                    (TriviaPreservation.difference
                        "class C { }\n#line 7 \"a  b.cs\"\nclass D { }\n"
                        "class C { }\n#line 7 \"a b.cs\"\nclass D { }\n")
                    "#line 7 \"a  b.cs\" and #line 7 \"a b.cs\" name two different files."

                Expect.isNotNull
                    (TriviaPreservation.difference
                        "#pragma checksum \"a  b.cs\" \"{ff1816ec-aa5e-4d10-87f7-6f4963833460}\" \"ab\"\nclass C { }\n"
                        "#pragma checksum \"a b.cs\" \"{ff1816ec-aa5e-4d10-87f7-6f4963833460}\" \"ab\"\nclass C { }\n")
                    "A checksum names its file in the same quoted way."
            }

            test "an unchanged directive line that moved is a change to where it applies" {
                let source = "class C\n{\n#nullable enable\n    string? A;\n    string B;\n}\n"
                let moved = "class C\n{\n    string? A;\n#nullable enable\n    string B;\n}\n"

                Expect.isNotNull
                    (TriviaPreservation.difference source moved)
                    "#nullable enable applies from where it sits, so moving it changes the file."

                Expect.isNotNull
                    (TriviaPreservation.difference
                        "class C\n{\n#pragma warning disable CS0168\n    void M() { int a; }\n    void N() { int b; }\n}\n"
                        "class C\n{\n    void M() { int a; }\n#pragma warning disable CS0168\n    void N() { int b; }\n}\n")
                    "#pragma warning disable applies from where it sits."

                Expect.isNull
                    (TriviaPreservation.difference
                        source
                        "class C\n{\n#nullable enable\n    string? A;\n\n    string B;\n}\n")
                    "Blank lines and indentation move no token across the directive."
            }

            test "a directive glued after code stops being a directive, and is named" {
                let detail =
                    TriviaPreservation.difference
                        "class C { }\n#pragma warning disable CS0168\nclass D { }\n"
                        "class C { }#pragma warning disable CS0168\nclass D { }\n"

                Expect.isNotNull
                    detail
                    "A '#' that is no longer first on its line is not the same line."

                Expect.isNotNull
                    (TriviaPreservation.difference
                        "class C\n{\n#nullable enable\n    string? A;\n}\n"
                        "class C\n{\n    string? A;\n}\n")
                    "A deleted directive is a line the output does not hold."
            }

            test "directive-looking text inside a raw string stays ordinary data" {
                let checker = SyntaxPreservation.Checker()
                let fence = "\"\"\""

                let raw (message: string) =
                    "class C\n{\n    string S =\n        "
                    + fence
                    + "\n        #error "
                    + message
                    + "\n        "
                    + fence
                    + ";\n}\n"

                Expect.isNull
                    (TriviaPreservation.difference (raw "held") (raw "held"))
                    "A '#' line inside a raw string is not a directive line at all."

                Expect.isNull
                    (TriviaPreservation.difference (raw "held") (raw "changed"))
                    "Changing that line changes a string literal, not a directive."

                let message =
                    Expect.wantError
                        (checker.Check(PrinterOptions.Default, "raw.cs", raw "held", raw "changed"))
                        "A literal's contents must be preserved."

                Expect.isFalse
                    (message.Contains "changed a preprocessor directive line")
                    "The literal is refused as a literal, not as a directive."

                Expect.isNotNull
                    (TriviaPreservation.difference
                        "#error held\n\nclass C { }\n"
                        "#error changed\n\nclass C { }\n")
                    "The same text outside a literal is a directive line, and is compared."
            }

            test "a using the printer moved past a closed frame is not a moved directive" {
                let rewritten =
                    "using A;\n#if PCL\nusing M;\n#endif\nusing B;\nusing D;\n\nclass C { }\n"

                let formatted =
                    "using A;\nusing B;\nusing D;\n#if PCL\nusing M;\n#endif\n\nclass C { }\n"

                Expect.notEqual
                    (tokensBefore formatted "#if PCL")
                    (tokensBefore rewritten "#if PCL")
                    "The fixture must move the frame past tokens, or it bounds nothing."

                Expect.isNull
                    (TriviaPreservation.difference rewritten formatted)
                    "A using run the printer is declared to be able to sort moves no directive."

                Expect.isNotNull
                    (TriviaPreservation.difference
                        "class C\n{\n#if PCL\n    int A;\n#endif\n    int B;\n}\n"
                        "class C\n{\n    int B;\n#if PCL\n    int A;\n#endif\n}\n")
                    "A field the output moved across the frame still moves the frame."
            }

            test "a shebang the output moved off line one is named" {
                let source = "#!/usr/bin/env dotnet\nclass C {}\n"
                let moved = "\n" + source

                Expect.isNotNull
                    (TriviaPreservation.difference source moved)
                    "A shebang is a shebang only as the first thing in the file."

                Expect.isNull
                    (TriviaPreservation.difference source "#!/usr/bin/env dotnet\nclass C { }\n")
                    "A shebang that stayed on line one changed nothing."
            }

            test "a conflict marker is the residual this comparison does not name" {
                let checker = SyntaxPreservation.Checker()
                let source = "class C { }\n<<<<<<< ours\nclass D { }\n"
                let formatted = "class C { }\n<<<<<<< theirs\nclass D { }\n"

                Expect.isNull
                    (TriviaPreservation.difference source formatted)
                    "A conflict marker is not a '#' line, so this comparison cannot see it."

                Expect.isError
                    (checker.Check(PrinterOptions.Default, "conflict.cs", source, formatted))
                    "The output is refused all the same, which is what keeps the residual off the disk."
            }
        ]
    |> testSequenced

let private lexicalScreen =
    testList
        "the configuration loop's lexical screen"
        [
            test "the pair proof answers what the one-sided proof answers" {
                let checker = TokenPreservation.Checker()

                for source in
                    [
                        "class C { }\n"
                        "#if DEBUG\nclass C { }\n#endif\n"
                        "#define A\n#if A\nclass C { int x; }\n#else\nclass C { long x; }\n#endif\n"
                        "class C {\n#if NEVER\n\n#endif\n#if ALSO\nclass D { int x; }\n#endif\n}\n"
                        "using Z;\nusing A;\nclass C { }\n"
                        "class C { string s = \"a\"; }\n"
                    ] do
                    let formatted = format PrinterOptions.Default source

                    let oneSided = TokenPreservation.Checker().LexicallyPreserved(source, formatted)
                    let pair = checker.LexicallyPreservedPair(source, formatted)

                    Expect.equal pair oneSided $"The two entry points read one comparison: {source}"
            }

            test "a text is only ever parsed from its own lex" {
                let first =
                    "#if DEBUG\nclass C { int x; }\n#endif\nusing Z;\nusing A;\nclass C { }\n"

                let second = "namespace N;\nusing Z;\nusing A;\nclass D { long y; }\n"
                let firstFormatted = format PrinterOptions.Default first
                let secondFormatted = format PrinterOptions.Default second

                let reference =
                    TokenPreservation
                        .Checker()
                        .Normalize(PrinterOptions.Default, second, secondFormatted)

                let checker = TokenPreservation.Checker()

                Expect.isFalse
                    (checker.LexicallyPreservedPair(first, firstFormatted))
                    "The sorted using run makes the first pair decline, which is what leaves its lexes behind."

                let reused = checker.Normalize(PrinterOptions.Default, second, secondFormatted)

                Expect.equal
                    reused
                    reference
                    "Normalize must lex the text it was given, not finish another text's lex."

                Expect.isTrue
                    (checker.FastEquivalent(reused, secondFormatted))
                    "And the parses it leaves must be of that text too."
            }

            test "the screen cannot prove a pair the loop refuses" {
                let verifier = SyntaxPreservation.Checker()
                let checker = TokenPreservation.Checker()

                for struct (name, source, formatted) in
                    [
                        struct ("arm-identifier.cs",
                                "class C {\n#if DEBUG\n    int x;\n#endif\n}\n",
                                "class C {\n#if DEBUG\n    int y;\n#endif\n}\n")
                        struct ("arm-token.cs",
                                "class C {\n#if DEBUG\n    int x = 1;\n#endif\n}\n",
                                "class C {\n#if DEBUG\n    int x;\n#endif\n}\n")
                        struct ("arm-directive.cs",
                                "class C {\n#if DEBUG\n    int x;\n#endif\n}\n",
                                "class C {\n#if RELEASE\n    int x;\n#endif\n}\n")
                    ] do
                    let prefix = "#define DEBUG\n"

                    Expect.isFalse
                        (checker.LexicallyPreservedPair(prefix + source, prefix + formatted))
                        $"The screen must decline a changed arm: {name}"

                    Expect.isError
                        (verifier.Check(PrinterOptions.Default, name, source, formatted))
                        $"And the output stays refused: {name}"
            }

            test "the screen is what settles a configuration it can settle" {
                let verifier = SyntaxPreservation.Checker()
                let checker = TokenPreservation.Checker()

                let work (name: string) (source: string) =
                    let formatted = format PrinterOptions.Default source

                    verifier.Decide(PrinterOptions.Default, name, source, formatted) |> ignore
                    verifier.ResetParseWork()

                    let verdict = verifier.Decide(PrinterOptions.Default, name, source, formatted)

                    Expect.equal
                        verdict
                        SyntaxPreservation.Verification.Proven
                        $"The fixture must be proven, or it bounds a loop that stopped: {name}"

                    verifier.ParseWork

                let settled = "class C {\n#if DEBUG\nint x;\n#endif\n}\n"
                let settledFormatted = format PrinterOptions.Default settled

                Expect.isFalse
                    (checker.LexicallyPreserved(settled, settledFormatted))
                    "The file must reach the loop at all: the arm is disabled text whose text changed."

                Expect.isTrue
                    (checker.LexicallyPreservedPair(
                        "#define DEBUG\n" + settled,
                        "#define DEBUG\n" + settledFormatted
                    ))
                    "And the configuration's own two texts must be lexically equal, or the screen settles nothing."

                let struct (settledLexes, settledBuilds) = work "settled.cs" settled

                Expect.equal
                    struct (settledLexes, settledBuilds)
                    struct (5, 3)
                    "A configuration the screen settles costs two lexes and no tree build."

                let declined = "class C {\n#if A\nint x;\n#else\nint y;\n#endif\n}\n"
                let struct (declinedLexes, declinedBuilds) = work "declined.cs" declined

                Expect.equal
                    struct (declinedLexes, declinedBuilds)
                    struct (5, 5)
                    "A configuration the screen declines costs its two tree builds and no second lex."

                let twice = "class C {\n#if A\nint x;\n#endif\n#if B\nint y;\n#endif\n}\n"
                let struct (twiceLexes, twiceBuilds) = work "twice.cs" twice

                Expect.equal
                    struct (twiceLexes, twiceBuilds)
                    struct (7, 7)
                    "Each declined configuration adds one lex and one build per text."

                for spanCase in
                    [
                        "using B;\nusing A;\n// c\nclass C {\n    int[] xs = new[] {\n        1,\n        2\n    };\n}\n"
                        "/// <summary>a</summary>\n/// <remarks>b</remarks>\nstatic public class C {\n    int[] xs = new[] {\n        1,\n        2\n    };\n}\n"
                        "using System;\nclass C {\n    int a = 1;\n#if FOO\n    int[] xs = new[] {\n        1,\n        2\n    };\n#else\n    int y = 2;\n#endif\n    int z = 3;\n}\n"
                    ] do
                    let fmt = format PrinterOptions.Default spanCase
                    let srcTree = Csff.Parser.SyntaxTree()
                    Csff.Parser.Parser.parse spanCase srcTree

                    let expectedVerdict =
                        verifier.DecideDirect(
                            PrinterOptions.Default,
                            "span.cs",
                            spanCase,
                            fmt,
                            srcTree,
                            TransformationWitness.Searched
                        )

                    let actualVerdict =
                        verifier.DecideDirectSpan(
                            PrinterOptions.Default,
                            "span.cs",
                            spanCase,
                            fmt.AsSpan(),
                            srcTree,
                            TransformationWitness.Searched
                        )

                    Expect.equal
                        actualVerdict
                        expectedVerdict
                        "DecideDirectSpan matches DecideDirect."
            }
        ]
    |> testSequenced

let tests = TestList([ preservation; directiveLines; lexicalScreen ], Normal)
