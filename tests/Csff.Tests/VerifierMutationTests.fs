module Csff.Tests.VerifierMutationTests

open System
open System.Collections.Generic
open System.IO
open System.Text
open Csff.Cli
open Csff.Conformance
open Csff.Lexer
open Csff.Parser
open Csff.Printer
open Expecto

[<NoComparison; NoEquality>]
type Edit =
    | Swap of find: string * replace: string
    | Rewrite of (string -> string)

type Expectation =
    | Refused
    | Unproven
    | Survives

[<NoComparison; NoEquality>]
type Mutation =
    {
        Name: string
        Family: string
        Source: string
        Edit: Edit
        Expectation: Expectation
    }

type Defect =
    {
        Name: string
        Family: string
        Source: string
        Output: string
    }

type Verdict =
    {
        Mutation: string
        Family: string
        Lexical: bool
        Walk: bool
        Diagnosis: string
        Pipeline: string
        Outcome: string
        Refused: bool
        Configurations: (string * string) list
        OnlyDirectiveLine: bool
    }

let private csharp (text: string) =
    let trimmed = text.Replace("\r\n", "\n").TrimStart('\n')

    if trimmed.EndsWith("\n", StringComparison.Ordinal) then
        trimmed
    else
        trimmed + "\n"

let private lines items = csharp (String.concat "\n" items)

let private fence = "\"\"\""

let private options = PrinterOptions.Default

let private format (source: string) =
    let tree = SyntaxTree()
    use document = new DocumentBuffer()
    use printer = new Printer()
    Parser.parse source tree
    SyntaxPrinter.build source tree document options
    printer.Print(source, document, options)
    printer.OutputText

let applyEdit (output: string) edit =
    match edit with
    | Swap(find, replace) ->
        if find = replace then
            Error "the marker and its replacement are the same text."
        else
            let first = output.IndexOf(find, StringComparison.Ordinal)

            if first < 0 then
                Error(String.Format("the marker is absent: {0}", find))
            elif output.IndexOf(find, first + 1, StringComparison.Ordinal) >= 0 then
                Error(String.Format("the marker occurs more than once: {0}", find))
            else
                Ok(output.Remove(first, find.Length).Insert(first, replace))
    | Rewrite rewrite ->
        let changed = rewrite output

        if String.Equals(changed, output, StringComparison.Ordinal) then
            Error "the rewrite left the output unchanged."
        else
            Ok changed

let private rule (result: Result<unit, string>) =
    match result with
    | Ok() -> "ok"
    | Error message ->
        if message.StartsWith("unprovable:", StringComparison.Ordinal) then
            "unprovable"
        elif message.Contains "changed a comment" then
            "comments"
        elif message.Contains "changed a preprocessor directive line" then
            "directive-line"
        elif message.Contains "left a block comment unterminated" then
            "open-comment"
        elif message.StartsWith("throw:", StringComparison.Ordinal) then
            "throw"
        else
            "other"

let private attempt action =
    try
        action ()
    with error ->
        Error("throw: " + error.Message)

let private configurationRules (name: string) (source: string) (mutated: string) =
    try
        let tokens = TokenPreservation.Checker()
        let expected = tokens.Normalize(options, source, mutated)
        let selected = tokens.SymbolSets expected

        [
            for symbols in Array.append [| [||] |] selected do
                let prefix =
                    symbols |> Array.map (fun symbol -> "#define " + symbol + "\n") |> String.concat ""

                let verdict =
                    attempt (fun () ->
                        SyntaxPreservation.Checker()
                            .Adjudicate(options, name, prefix + source, prefix + mutated))

                let label =
                    if symbols.Length = 0 then
                        "default"
                    else
                        String.Join("+", symbols)

                yield label, rule verdict
        ]
    with error ->
        [ "default", "throw: " + error.Message ]

let measureEditWith (configurations: bool) (name: string) (source: string) (mutated: string) =
    let lexical =
        try
            TokenPreservation.Checker().LexicallyPreserved(source, mutated)
        with _ ->
            false

    let walk =
        try
            let tokens = TokenPreservation.Checker()
            let expected = tokens.Normalize(options, source, mutated)
            tokens.FastEquivalent(expected, mutated)
        with _ ->
            false

    let roslyn =
        attempt (fun () -> SyntaxPreservation.Checker().Adjudicate(options, name, source, mutated))

    let pipeline =
        attempt (fun () -> SyntaxPreservation.Checker().Check(options, name, source, mutated))

    let configurations =
        if configurations then
            configurationRules name source mutated
        else
            []

    let refusals = configurations |> List.filter (fun (_, verdict) -> verdict <> "ok")

    let refuser (verdict: Result<unit, string>) =
        if rule verdict = "comments" then
            "the comment comparison"
        else
            "the directive-line comparison"

    let outcome =
        match pipeline with
        | Error _ when rule pipeline = "unprovable" ->
            "REFUSED as unprovable: nothing proves it, the comparison allows it"
        | Error _ -> "REFUSED by " + refuser pipeline + " (" + rule pipeline + ")"
        | Ok() ->
            match roslyn with
            | Error _ ->
                let settled = " accepted what " + refuser roslyn + " refuses ("

                if lexical then
                    "SURVIVED: layer 1" + settled + rule roslyn + ")"
                else
                    "SURVIVED: layer 2" + settled + rule roslyn + ")"
            | Ok() -> "SURVIVED: no layer refuses it"

    {
        Mutation = name
        Family = ""
        Lexical = lexical
        Walk = walk
        Diagnosis = rule roslyn
        Pipeline = rule pipeline
        Outcome = outcome
        Refused =
            match pipeline with
            | Error _ -> true
            | Ok() -> false
        Configurations = configurations
        OnlyDirectiveLine =
            not (List.isEmpty refusals)
            && refusals |> List.forall (fun (_, verdict) -> verdict = "directive-line")
    }

let measureEdit name source mutated = measureEditWith true name source mutated

let measureMutation (mutation: Mutation) =
    let output = format mutation.Source

    match applyEdit output mutation.Edit with
    | Error reason ->
        Error(String.Format("{0}: {1}\noutput was:\n{2}", mutation.Name, reason, output))
    | Ok mutated ->
        if String.Equals(mutated, mutation.Source, StringComparison.Ordinal) then
            Error(mutation.Name + ": the mutated output equals its own input, so nothing is verified.")
        else
            let verdict = measureEdit (mutation.Name + ".cs") mutation.Source mutated

            Ok
                { verdict with
                    Family = mutation.Family
                }

let private conditionalStatement =
    csharp
        """
class C
{
    void M()
    {
        int x = 1;
#if DEBUG
        x = 2;
#endif
    }
}
"""

let private conditionalInitializer =
    csharp
        """
class C
{
    public const Level F =
#if DEBUG
        Level.Info;
#else
        Level.Warn;
#endif
}
"""

let private conditionalReturn =
    csharp
        """
class C
{
    static X509KeyStorageFlags Flags()
    {
        return
#if NETFRAMEWORK
            X509KeyStorageFlags.DefaultKeySet;
#else
            X509KeyStorageFlags.EphemeralKeySet;
#endif
    }
}
"""

let private falseBranch =
    csharp
        """
class C
{
    void M()
    {
#if false
        Dead();
#endif
    }
}
"""

let private constantCondition =
    csharp
        """
class C
{
    void M()
    {
#if true
        Live();
#else
        Dead();
#endif
    }
}
"""

let private blockCommentedArgument =
    csharp
        """
class C
{
    int M(int a) => M(/* k */ a);
}
"""

let private trailingBlockComment =
    csharp
        """
class C
{
    int M() => /* k */ 1;
}
"""

let private errorDirective =
    csharp
        """
#error the old message

class C { }
"""

let private commentedStatement =
    csharp
        """
class C
{
    void M()
    {
        // note
        Use();
    }
}
"""

let private nullableFields =
    csharp
        """
class C
{
#nullable enable
    string? A;
#nullable disable
    string B;
}
"""

let private pragmaStatement =
    csharp
        """
class C
{
    void M()
    {
#pragma warning disable CS0168
        int unused;
#pragma warning restore CS0168
    }
}
"""

let private conditionalMembers =
    csharp
        """
class C
{
#if DEBUG
    int A;
    int B;
#endif
}
"""

let private conditionalUsings =
    csharp
        """
#if FOO
using System.Text;
#endif
using System;

class C { }
"""

let private twinFrames =
    csharp
        """
#if FOO
using System.Text;
#endif
#if FOO
using System.IO;
#endif

class C { }
"""

let private duplicateUsings =
    csharp
        """
using System;
using System;

class C { }
"""

let private deadBranch =
    csharp
        """
class C
{
#if false
    int Dead;
#endif
}
"""

let private namedDeadBranch =
    csharp
        """
class C
{
#if NEVER
    int Dead;
#endif
}
"""

let private nestedDeadBranch =
    csharp
        """
class C
{
#if false
#if BAR
    int Dead;
#endif
#endif
}
"""

let private regionMember =
    csharp
        """
class C
{
#region Alpha
    int A;
#endregion
}
"""

let private lineDirective =
    csharp
        """
class C
{
#line 42
    int A;
#line default
}
"""

let private warningDirective =
    csharp
        """
#warning the old message

class C { }
"""

let private shebangScript =
    csharp
        """
#!/usr/bin/env dotnet

Console.WriteLine(1);
"""

let private literals =
    csharp
        """
class C
{
    const string S = "a b";
}
"""

let private interpolation =
    csharp
        """
class C
{
    string M(int value) => $"{value:n2}";
}
"""

let private alignedInterpolation =
    csharp
        """
class C
{
    string M(int value) => $"{value,5:n2}";
}
"""

let private verbatimLiteral =
    csharp
        """
class C
{
    const string S = @"first
second";
}
"""

let private rawLiteral =
    lines
        [
            "class C"
            "{"
            "    const string S = " + fence
            "        line"
            "        " + fence + ";"
            "}"
        ]

let private initializer =
    csharp
        """
class C
{
    int[] A = new[] { 1, 2 };
}
"""

let private threeInitializer =
    csharp
        """
class C
{
    int[] A = new[] { 1, 2, 3 };
}
"""

let private callSite =
    csharp
        """
class C
{
    void M(int a, int b) => M(1, 2);
}
"""

let private arithmetic =
    csharp
        """
class C
{
    int M(int a, int b) => a + +b;
}
"""

let private subtraction =
    csharp
        """
class C
{
    int M(int a, int b) => a - -b;
}
"""

let private shift =
    csharp
        """
class C
{
    int M(int a, int b) => a >> b;
}
"""

let private pointerDivision =
    csharp
        """
unsafe class C
{
    static int M(int a, int* b) => a / *b;
}
"""

let private increment =
    csharp
        """
class C
{
    void M(ref int i)
    {
        i++;
    }
}
"""

let private modifiers =
    csharp
        """
class C
{
    static  public int A;
}
"""

let private commentAfterTrailingComment =
    csharp
        """
class C
{
    static int[] A =>
    [
        1, // trailing
        // own line
        2,
    ];
}
"""

let private interpolationComment =
    csharp
        """
class C
{
    string S = $"{ /* k */ 1 }";
}
"""

let private docComment =
    csharp
        """
class C
{
    /// <summary>first</summary>
    int A;
}
"""

let private docCommentRun =
    csharp
        """
class C
{
    /// <summary>first</summary>
    /// <remarks>second</remarks>
    int A;

    /** block first
      * block second
      */
    int B;
}
"""

let private sortableUsings =
    csharp
        """
using System;
using System.Text;
using System.IO;

class C { }
"""

let private aliasUsing =
    csharp
        """
using A = System.Text.Encoding;

class C { }
"""

let catalogue =
    [
        {
            Name = "newline-before-directive-deleted"
            Family = "directive boundary"
            Source = conditionalStatement
            Edit = Swap("1;\n#if DEBUG", "1;#if DEBUG")
            Expectation = Refused
        }
        {
            Name = "newline-after-directive-deleted"
            Family = "directive boundary"
            Source = conditionalStatement
            Edit = Swap("#if DEBUG\n        x = 2;", "#if DEBUG x = 2;")
            Expectation = Refused
        }
        {
            Name = "newline-after-endif-deleted"
            Family = "directive boundary"
            Source = conditionalStatement
            Edit = Swap("#endif\n", "#endif ")
            Expectation = Refused
        }
        {
            Name = "conditional-return-glued-after-directive"
            Family = "directive boundary"
            Source = conditionalReturn
            Edit =
                Swap(
                    "#if NETFRAMEWORK\n        X509KeyStorageFlags.DefaultKeySet;",
                    "#if NETFRAMEWORK X509KeyStorageFlags.DefaultKeySet;"
                )
            Expectation = Refused
        }
        {
            Name = "code-swallowed-onto-a-false-if-line"
            Family = "directive boundary"
            Source = falseBranch
            Edit = Swap("#if false\n        Dead();", "#if false Dead();")
            Expectation = Refused
        }
        {
            Name = "code-swallowed-onto-the-else-of-a-constant-condition"
            Family = "directive boundary"
            Source = constantCondition
            Edit = Swap("#else\n        Dead();", "#else Dead();")
            Expectation = Refused
        }
        {
            Name = "code-swallowed-onto-a-region-line"
            Family = "directive boundary"
            Source = regionMember
            Edit = Swap("#region Alpha\n    int A;", "#region Alpha int A;")
            Expectation = Refused
        }
        {
            Name = "code-swallowed-onto-a-pragma-line"
            Family = "directive boundary"
            Source = pragmaStatement
            Edit =
                Swap(
                    "#pragma warning disable CS0168\n        int unused;",
                    "#pragma warning disable CS0168 int unused;"
                )
            Expectation = Refused
        }
        {
            Name = "code-swallowed-onto-a-line-directive"
            Family = "directive boundary"
            Source = lineDirective
            Edit = Swap("#line 42\n    int A;", "#line 42 int A;")
            Expectation = Refused
        }
        {
            Name = "directive-turned-into-comment"
            Family = "directive boundary"
            Source = conditionalStatement
            Edit = Swap("#if DEBUG", "//if DEBUG")
            Expectation = Refused
        }

        {
            Name = "line-comment-swallows-the-next-statement"
            Family = "comment"
            Source = commentedStatement
            Edit = Swap("// note\n", "// note ")
            Expectation = Refused
        }
        {
            Name = "line-comment-rewritten-as-a-block-comment"
            Family = "comment"
            Source = commentedStatement
            Edit = Swap("// note\n        Use();", "/* note */ Use();")
            Expectation = Refused
        }
        {
            Name = "block-comment-turned-into-a-line-comment-that-swallows-its-argument"
            Family = "comment"
            Source = blockCommentedArgument
            Edit = Swap("M( /* k */\n            a", "M( // k a")
            Expectation = Refused
        }
        {
            Name = "trailing-block-comment-rewritten-as-a-line-comment"
            Family = "comment"
            Source = trailingBlockComment
            Edit = Swap("/* k */", "// k")
            Expectation = Refused
        }
        {
            Name = "line-comment-text-changed"
            Family = "comment"
            Source = commentedStatement
            Edit = Swap("// note", "// changed")
            Expectation = Refused
        }
        {
            Name = "line-comment-deleted"
            Family = "comment"
            Source = commentedStatement
            Edit = Swap("        // note\n", "")
            Expectation = Refused
        }
        {
            Name = "doc-comment-text-changed"
            Family = "comment"
            Source = docComment
            Edit = Swap("<summary>first</summary>", "<summary>second</summary>")
            Expectation = Refused
        }
        {
            Name = "a-line-of-a-doc-run-deleted"
            Family = "comment"
            Source = docCommentRun
            Edit = Swap("    /// <remarks>second</remarks>\n", "")
            Expectation = Refused
        }
        {
            Name = "an-interior-line-of-a-block-comment-changed"
            Family = "comment"
            Source = docCommentRun
            Edit = Swap("block second", "block third")
            Expectation = Refused
        }
        {
            Name = "doc-block-comment-rewritten-as-a-plain-block"
            Family = "comment"
            Source = docCommentRun
            Edit = Swap("/** block first", "/* block first")
            Expectation = Refused
        }
        {
            Name = "line-comment-repeated"
            Family = "comment"
            Source = commentedStatement
            Edit = Swap("        // note\n", "        // note\n        // note\n")
            Expectation = Refused
        }
        {
            Name = "own-line-comment-glued-onto-a-trailing-comment"
            Family = "comment"
            Source = commentAfterTrailingComment
            Edit = Swap("// trailing\n", "// trailing ")
            Expectation = Refused
        }
        {
            Name = "comment-in-an-interpolation-hole-changed"
            Family = "comment"
            Source = interpolationComment
            Edit = Swap("/* k */", "/* j */")
            Expectation = Refused
        }

        {
            Name = "nullable-directive-moved-past-its-field"
            Family = "directive position"
            Source = nullableFields
            Edit = Swap("#nullable enable\n    string? A;", "    string? A;\n#nullable enable")
            Expectation = Refused
        }
        {
            Name = "pragma-disable-moved-past-its-statement"
            Family = "directive position"
            Source = pragmaStatement
            Edit =
                Swap(
                    "#pragma warning disable CS0168\n        int unused;",
                    "        int unused;\n#pragma warning disable CS0168"
                )
            Expectation = Refused
        }
        {
            Name = "pragma-restore-moved-before-its-statement"
            Family = "directive position"
            Source = pragmaStatement
            Edit =
                Swap(
                    "        int unused;\n#pragma warning restore CS0168",
                    "#pragma warning restore CS0168\n        int unused;"
                )
            Expectation = Refused
        }
        {
            Name = "nullable-directive-deleted"
            Family = "directive position"
            Source = nullableFields
            Edit = Swap("#nullable enable\n", "")
            Expectation = Refused
        }
        {
            Name = "endif-moved-above-the-member-it-governs"
            Family = "directive position"
            Source = conditionalMembers
            Edit = Swap("    int B;\n#endif", "#endif\n    int B;")
            Expectation = Refused
        }

        {
            Name = "if-condition-symbol-changed"
            Family = "directive text"
            Source = conditionalStatement
            Edit = Swap("#if DEBUG", "#if TRACE")
            Expectation = Refused
        }
        {
            Name = "pragma-warning-code-changed"
            Family = "directive text"
            Source = pragmaStatement
            Edit = Swap("disable CS0168", "disable CS0169")
            Expectation = Refused
        }
        {
            Name = "nullable-setting-changed"
            Family = "directive text"
            Source = nullableFields
            Edit = Swap("#nullable enable", "#nullable restore")
            Expectation = Refused
        }
        {
            Name = "line-directive-number-changed"
            Family = "directive text"
            Source = lineDirective
            Edit = Swap("#line 42", "#line 43")
            Expectation = Refused
        }
        {
            Name = "region-name-changed"
            Family = "directive text"
            Source = regionMember
            Edit = Swap("#region Alpha", "#region Beta")
            Expectation = Refused
        }
        {
            Name = "error-directive-message-changed"
            Family = "directive text"
            Source = errorDirective
            Edit = Swap("#error the old message", "#error a different message")
            Expectation = Refused
        }
        {
            Name = "warning-directive-message-changed"
            Family = "directive text"
            Source = warningDirective
            Edit = Swap("#warning the old message", "#warning a different message")
            Expectation = Refused
        }
        {
            Name = "shebang-interpreter-changed"
            Family = "directive text"
            Source = shebangScript
            Edit = Swap("#!/usr/bin/env dotnet", "#!/usr/bin/env other")
            Expectation = Refused
        }

        {
            Name = "space-added-inside-a-string-literal"
            Family = "literal data"
            Source = literals
            Edit = Swap("\"a b\"", "\"a  b\"")
            Expectation = Unproven
        }
        {
            Name = "space-added-inside-an-interpolation-format-clause"
            Family = "literal data"
            Source = interpolation
            Edit = Swap("{value:n2}", "{value: n2}")
            Expectation = Unproven
        }
        {
            Name = "interpolation-format-clause-text-changed"
            Family = "literal data"
            Source = interpolation
            Edit = Swap("{value:n2}", "{value:n3}")
            Expectation = Unproven
        }
        {
            Name = "interpolation-alignment-value-changed"
            Family = "literal data"
            Source = alignedInterpolation
            Edit = Swap("{value, 5:n2}", "{value, 6:n2}")
            Expectation = Unproven
        }
        {
            Name = "lf-turned-into-crlf-inside-a-verbatim-literal"
            Family = "literal data"
            Source = verbatimLiteral
            Edit = Swap("first\nsecond", "first\r\nsecond")
            Expectation = Unproven
        }
        {
            Name = "raw-literal-content-line-reindented"
            Family = "literal data"
            Source = rawLiteral
            Edit = Swap("\n        line", "\n            line")
            Expectation = Unproven
        }
        {
            Name = "raw-literal-closing-fence-reindented"
            Family = "literal data"
            Source = rawLiteral
            Edit = Swap("\n        " + fence, "\n    " + fence)
            Expectation = Unproven
        }

        {
            Name = "using-moved-out-of-its-conditional-frame"
            Family = "using placement"
            Source = conditionalUsings
            Edit = Swap("#if FOO\nusing System.Text;\n#endif\n", "using System.Text;\n")
            Expectation = Refused
        }
        {
            Name = "using-moved-between-two-identically-spelled-frames"
            Family = "using placement"
            Source = twinFrames
            Edit = Swap("using System.Text;", "using System.IO;")
            Expectation = Unproven
        }
        {
            Name = "duplicate-using-dropped"
            Family = "using placement"
            Source = duplicateUsings
            Edit = Swap("using System;\nusing System;\n", "using System;\n")
            Expectation = Unproven
        }
        {
            Name = "duplicate-using-added"
            Family = "using placement"
            Source = duplicateUsings
            Edit = Swap("using System;\nusing System;\n", "using System;\nusing System;\nusing System;\n")
            Expectation = Unproven
        }
        {
            Name = "using-alias-target-changed"
            Family = "using placement"
            Source = aliasUsing
            Edit = Swap("System.Text.Encoding", "System.IO.Stream")
            Expectation = Unproven
        }

        {
            Name = "interior-comma-moved-to-the-trailing-position"
            Family = "separator"
            Source = initializer
            Edit = Swap("{ 1, 2 }", "{ 1 2, }")
            Expectation = Unproven
        }
        {
            Name = "interior-comma-removed"
            Family = "separator"
            Source = threeInitializer
            Edit = Swap("{ 1, 2, 3 }", "{ 1, 2 3 }")
            Expectation = Unproven
        }
        {
            Name = "trailing-comma-added-to-an-argument-list"
            Family = "separator"
            Source = callSite
            Edit = Swap("M(1, 2)", "M(1, 2,)")
            Expectation = Unproven
        }
        {
            Name = "trailing-comma-added-to-a-parameter-list"
            Family = "separator"
            Source = callSite
            Edit = Swap("M(int a, int b)", "M(int a, int b,)")
            Expectation = Unproven
        }

        {
            Name = "plus-plus-glued-into-an-increment"
            Family = "token boundary"
            Source = arithmetic
            Edit = Swap("a + +b", "a++b")
            Expectation = Unproven
        }
        {
            Name = "minus-minus-glued-into-a-decrement"
            Family = "token boundary"
            Source = subtraction
            Edit = Swap("a - -b", "a--b")
            Expectation = Unproven
        }
        {
            Name = "shift-split-into-two-comparisons"
            Family = "token boundary"
            Source = shift
            Edit = Swap("a >> b", "a > > b")
            Expectation = Unproven
        }
        {
            Name = "increment-split-into-two-additions"
            Family = "token boundary"
            Source = increment
            Edit = Swap("i++;", "i+ +;")
            Expectation = Unproven
        }
        {
            Name = "division-glued-into-a-block-comment"
            Family = "token boundary"
            Source = pointerDivision
            Edit = Swap("a / *b", "a /*b")
            Expectation = Refused
        }
        {
            Name = "two-keywords-glued-into-one-identifier"
            Family = "token boundary"
            Source = modifiers
            Edit = Swap("public static", "publicstatic")
            Expectation = Unproven
        }

        {
            Name = "disabled-text-reindented"
            Family = "disabled text"
            Source = deadBranch
            Edit = Swap("\n    int Dead;", "\n            int Dead;")
            Expectation = Survives
        }
        {
            Name = "disabled-text-identifier-changed"
            Family = "disabled text"
            Source = deadBranch
            Edit = Swap("int Dead;", "int Alive;")
            Expectation = Unproven
        }
        {
            Name = "disabled-text-deleted"
            Family = "disabled text"
            Source = deadBranch
            Edit = Swap("    int Dead;\n", "")
            Expectation = Unproven
        }
        {
            Name = "disabled-text-under-a-named-symbol-changed"
            Family = "disabled text"
            Source = namedDeadBranch
            Edit = Swap("int Dead;", "int Alive;")
            Expectation = Unproven
        }
        {
            Name = "nested-directive-inside-disabled-text-changed"
            Family = "disabled text"
            Source = nestedDeadBranch
            Edit = Swap("#if BAR", "#if BAZ")
            Expectation = Refused
        }

        {
            Name = "control-modifiers-unsorted"
            Family = "declared transformation"
            Source = modifiers
            Edit = Swap("public static", "static public")
            Expectation = Survives
        }
        {
            Name = "control-trailing-comma-added-to-an-initializer"
            Family = "declared transformation"
            Source = initializer
            Edit = Swap("{ 1, 2 }", "{ 1, 2, }")
            Expectation = Survives
        }
        {
            Name = "control-usings-put-in-an-unsorted-order"
            Family = "declared transformation"
            Source = sortableUsings
            Edit =
                Swap(
                    "using System;\nusing System.IO;\nusing System.Text;",
                    "using System.Text;\nusing System;\nusing System.IO;"
                )
            Expectation = Survives
        }
        {
            Name = "control-final-newline-removed"
            Family = "declared transformation"
            Source = commentedStatement
            Edit = Rewrite(fun output -> output.TrimEnd('\n'))
            Expectation = Survives
        }
        {
            Name = "control-statement-reindented"
            Family = "declared transformation"
            Source = commentedStatement
            Edit = Swap("        Use();", "            Use();")
            Expectation = Survives
        }
        {
            Name = "control-blank-line-added"
            Family = "declared transformation"
            Source = commentedStatement
            Edit = Swap("        Use();", "\n        Use();")
            Expectation = Survives
        }
        {
            Name = "control-comment-trailing-whitespace-added"
            Family = "declared transformation"
            Source = commentedStatement
            Edit = Swap("// note", "// note   ")
            Expectation = Survives
        }
        {
            Name = "control-block-comment-interior-reindented"
            Family = "declared transformation"
            Source = docCommentRun
            Edit = Swap("      * block second", "          * block second")
            Expectation = Survives
        }
    ]

let historicalDefects =
    [
        {
            Name = "conditional-const-initializer-glued-to-its-directive"
            Family = "directive boundary"
            Source = conditionalInitializer
            Output =
                lines
                    [
                        "class C"
                        "{"
                        "    public const Level F =#if DEBUG        Level.Info;"
                        "#else Level.Warn;"
                        "#endif"
                        "}"
                    ]
        }
        {
            Name = "conditional-return-glued-after-its-directive"
            Family = "directive boundary"
            Source = conditionalReturn
            Output =
                lines
                    [
                        "class C"
                        "{"
                        "    static X509KeyStorageFlags Flags()"
                        "    {"
                        "        return"
                        "#if NETFRAMEWORK X509KeyStorageFlags.DefaultKeySet;"
                        "#else"
                        "        X509KeyStorageFlags.EphemeralKeySet;"
                        "#endif"
                        "    }"
                        "}"
                    ]
        }
    ]

let measureDefect (defect: Defect) =
    let verdict = measureEdit (defect.Name + ".cs") defect.Source defect.Output

    { verdict with
        Family = defect.Family
    }

let private pad (width: int) (text: string) =
    if text.Length >= width then
        text
    else
        text + String(' ', width - text.Length)

let private report (verdicts: Verdict list) =
    let widest selector =
        verdicts |> List.fold (fun best item -> max best (String.length (selector item))) 8

    let nameWidth = widest (fun item -> item.Mutation)
    let familyWidth = widest (fun item -> item.Family)

    Console.Out.WriteLine(
        String.Format(
            "{0}  {1}  {2}  {3}  {4}  {5}",
            pad nameWidth "mutation",
            pad familyWidth "family",
            pad 7 "layer1",
            pad 7 "layer2",
            pad 17 "diagnosis",
            "outcome"
        )
    )

    for verdict in verdicts do
        Console.Out.WriteLine(
            String.Format(
                "{0}  {1}  {2}  {3}  {4}  {5}",
                pad nameWidth verdict.Mutation,
                pad familyWidth verdict.Family,
                pad 7 (if verdict.Lexical then "accept" else "decline"),
                pad 7 (if verdict.Walk then "accept" else "decline"),
                pad 17 verdict.Diagnosis,
                verdict.Outcome
                + (if List.isEmpty verdict.Configurations then
                       ""
                   else
                       "  ["
                       + String.Join(
                           " ",
                           verdict.Configurations
                           |> List.map (fun (name, result) -> name + "=" + result)
                       )
                       + (if verdict.OnlyDirectiveLine then
                              "; ONLY THE DIRECTIVE-LINE COMPARISON REFUSES IT]"
                          else
                              "]"))
            )
        )

let commentDump (argv: string array) =
    let file = argv[0]

    let eol =
        if argv.Length > 1 then
            match argv[1] with
            | "cr" -> EndOfLine.Cr
            | "crlf" -> EndOfLine.CrLf
            | _ -> EndOfLine.Lf
        else
            EndOfLine.Lf

    let settings =
        { PrinterOptions.Default with
            EndOfLine = eol
        }

    let source = SourceEncoding.read file
    let tree = SyntaxTree()
    use document = new DocumentBuffer()
    use printer = new Printer()
    Parser.parse source tree
    SyntaxPrinter.build source tree document settings
    printer.Print(source, document, settings)
    let printed = printer.OutputText

    let dump (label: string) (text: string) =
        let tree = SyntaxTree()
        Parser.parse text tree
        let buffer = tree.LexerBuffer
        let items = ResizeArray<string>()

        for index = 0 to buffer.TriviaCount - 1 do
            let item = buffer.Trivia index

            match item.Kind with
            | TriviaKind.SingleLineCommentTrivia
            | TriviaKind.MultiLineCommentTrivia
            | TriviaKind.SingleLineDocumentationCommentTrivia
            | TriviaKind.MultiLineDocumentationCommentTrivia ->
                items.Add(
                    String.Format(
                        "{0}\t{1}\t{2}\t{3}\t{4}",
                        label,
                        item.Kind,
                        item.Start,
                        item.Length,
                        text
                            .Substring(item.Start, item.Length)
                            .Replace("\r", "<CR>")
                            .Replace("\n", "<LF>")
                            .Replace("\t", "<TAB>")
                    )
                )
            | _ -> ()

        items

    let before = dump "IN" source
    let after = dump "OUT" printed
    Console.Out.WriteLine(String.Format("in={0} out={1}", before.Count, after.Count))

    for line in before do
        Console.Out.WriteLine line

    for line in after do
        Console.Out.WriteLine line

    0

let run (argv: string array) =
    for name in argv do
        match catalogue |> List.tryFind (fun mutation -> mutation.Name = name) with
        | None -> Console.Error.WriteLine("no such mutation: " + name)
        | Some mutation ->
            let output = format mutation.Source
            Console.Out.WriteLine("--- source\n" + mutation.Source)
            Console.Out.WriteLine("--- printed\n" + output)

            match applyEdit output mutation.Edit with
            | Error reason -> Console.Out.WriteLine("--- did not apply: " + reason)
            | Ok mutated -> Console.Out.WriteLine("--- mutated\n" + mutated)

    let mutable failures = 0
    let verdicts = ResizeArray<Verdict>()

    for mutation in catalogue do
        match measureMutation mutation with
        | Ok verdict -> verdicts.Add verdict
        | Error reason ->
            failures <- failures + 1
            Console.Error.WriteLine reason

    for defect in historicalDefects do
        verdicts.Add(measureDefect defect)

    report (List.ofSeq verdicts)

    let refused = verdicts |> Seq.filter (fun item -> item.Refused) |> Seq.length
    let masked =
        verdicts
        |> Seq.filter (fun item -> not item.Refused && item.Diagnosis <> "ok")
        |> Seq.length

    Console.Out.WriteLine()

    Console.Out.WriteLine(
        String.Format(
            "{0} mutations, {1} refused ({5} of them only because nothing proves them), {2} survived ({3} of those masked a named refusal), {4} did not apply",
            verdicts.Count,
            refused,
            verdicts.Count - refused,
            masked,
            failures,
            verdicts |> Seq.filter (fun item -> item.Pipeline = "unprovable") |> Seq.length
        )
    )

    Console.Out.WriteLine(
        String.Format(
            "{0} of the refusals come only from the directive-line comparison",
            verdicts
            |> Seq.filter (fun item -> item.Refused && item.OnlyDirectiveLine)
            |> Seq.length
        )
    )

    for defect in historicalDefects do
        Console.Out.WriteLine(
            String.Format(
                "printer writes {0} today: {1}",
                defect.Name,
                String.Equals(format defect.Source, defect.Output, StringComparison.Ordinal)
            )
        )

    if failures > 0 then 2 else 0

let writeBytes
    (input: byte array)
    (encoding: Encoding)
    (preamble: int)
    (printedText: string)
    (printedBytes: byte array)
    =
    let size =
        if SourceEncoding.isUtf8 encoding then
            printedBytes.Length + preamble
        else
            encoding.GetByteCount printedText + preamble

    let output = Array.zeroCreate<byte> size
    Array.blit input 0 output 0 preamble

    if SourceEncoding.isUtf8 encoding then
        Array.blit printedBytes 0 output preamble printedBytes.Length
    else
        encoding.GetBytes(printedText, output.AsSpan(preamble)) |> ignore

    output

let roundTrip (input: byte array) =
    let struct (encoding, preamble, source) = SourceEncoding.decode input input.Length
    let tree = SyntaxTree()
    use document = new DocumentBuffer()
    use printer = new Printer()
    Parser.parse source tree
    SyntaxPrinter.build source tree document options
    printer.Print(source, document, options)
    let printedText = printer.OutputText
    let printedBytes = printer.OutputBytes.ToArray()
    let written = writeBytes input encoding preamble printedText printedBytes
    let struct (again, againPreamble, reread) = SourceEncoding.decode written written.Length
    struct (encoding, preamble, source, printedText, printedBytes, written, again, againPreamble, reread)

let byteRoundTrip (argv: string array) =
    if argv.Length < 1 then
        Console.Error.WriteLine "usage: --byte-roundtrip <corpus-root>"
        2
    else

    let root = argv[0]
    let strict = UTF8Encoding(false, true)

    let files =
        Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories)
        |> Seq.sort
        |> Seq.toArray

    let mutable examined = 0
    let mutable changed = 0
    let mutable errors = 0
    let mutable textMismatch = 0
    let mutable byteMismatch = 0
    let mutable preambleLoss = 0
    let mutable encodingChange = 0
    let mutable invalidUtf8 = 0
    let paths = Dictionary<string, int>()
    let reported = ResizeArray<string>()

    let bump (table: Dictionary<string, int>) key =
        let mutable count = 0
        table.TryGetValue(key, &count) |> ignore
        table[key] <- count + 1

    let note (message: string) =
        if reported.Count < 40 then
            reported.Add message

    for file in files do
        try
            let input = File.ReadAllBytes file
            let struct (encoding, preamble, source) = SourceEncoding.decode input input.Length

            if source.Length <= 8 * 1024 * 1024 then
                examined <- examined + 1
                let tree = SyntaxTree()
                use document = new DocumentBuffer()
                use printer = new Printer()
                Parser.parse source tree
                SyntaxPrinter.build source tree document options
                printer.Print(source, document, options)

                let printedText = printer.OutputText
                let printedBytes = printer.OutputBytes.ToArray()

                let roundTripsStrictly =
                    try
                        strict.GetBytes(printedText) = printedBytes
                    with _ ->
                        false

                if not roundTripsStrictly then
                    invalidUtf8 <- invalidUtf8 + 1
                    note (file + ": OutputText is not the strict UTF-8 decoding of OutputBytes.")

                if SourceEncoding.isUtf8 encoding then
                    bump paths (if preamble = 0 then "utf-8" else "utf-8 with a BOM")
                else
                    bump paths (encoding.GetType().Name + " preamble=" + string preamble)

                if not (String.Equals(source, printedText, StringComparison.Ordinal)) then
                    changed <- changed + 1
                    let output = writeBytes input encoding preamble printedText printedBytes

                    let struct (again, againPreamble, reread) =
                        SourceEncoding.decode output output.Length

                    if not (String.Equals(reread, printedText, StringComparison.Ordinal)) then
                        textMismatch <- textMismatch + 1
                        note (file + ": the written bytes do not decode to the verified text.")

                    if againPreamble <> preamble then
                        preambleLoss <- preambleLoss + 1
                        note (file + ": the preamble length changed across the write.")

                    if not (obj.ReferenceEquals(again, encoding)) then
                        encodingChange <- encodingChange + 1
                        note (file + ": the written bytes detect as a different encoding.")

                    let secondTree = SyntaxTree()
                    use secondDocument = new DocumentBuffer()
                    use secondPrinter = new Printer()
                    Parser.parse reread secondTree
                    SyntaxPrinter.build reread secondTree secondDocument options
                    secondPrinter.Print(reread, secondDocument, options)

                    if not (secondPrinter.OutputBytes.SequenceEqual(ReadOnlySpan<byte>(printedBytes))) then
                        byteMismatch <- byteMismatch + 1
                        note (file + ": printing the written file again gives different bytes.")
        with error ->
            errors <- errors + 1
            note (file + ": " + error.Message)

    for message in reported do
        Console.Error.WriteLine message

    Console.Out.WriteLine(
        String.Format(
            "{0} files, {1} examined, {2} changed, {3} errored",
            files.Length,
            examined,
            changed,
            errors
        )
    )

    Console.Out.WriteLine(
        String.Format(
            "text mismatches {0}, re-print byte mismatches {1}, preamble losses {2}, encoding changes {3}, non-UTF-8 output text {4}",
            textMismatch,
            byteMismatch,
            preambleLoss,
            encodingChange,
            invalidUtf8
        )
    )

    for pair in Seq.sortBy (fun (pair: KeyValuePair<string, int>) -> pair.Key) paths do
        Console.Out.WriteLine(String.Format("encoding path {0}: {1} files", pair.Key, pair.Value))

    if textMismatch + byteMismatch + preambleLoss + encodingChange + invalidUtf8 > 0 then
        1
    else
        0

let tests =
    testList
        "verifier mutations"
        [
            test "every catalogue mutation applies to the output it mutates" {
                for mutation in catalogue do
                    match measureMutation mutation with
                    | Ok _ -> ()
                    | Error reason -> failtest reason
            }

            test "every historical printer defect stays refused" {
                for defect in historicalDefects do
                    let verdict = measureDefect defect

                    if not verdict.Refused then
                        failtest (
                            defect.Name
                            + ": verification accepts an output the printer is on record for writing. "
                            + verdict.Outcome
                        )
            }

            test "the refused printer defects stay refused, and stay diagnosed" {
                let weakened =
                    [
                        for mutation in catalogue do
                            if mutation.Expectation = Refused then
                                match measureMutation mutation with
                                | Ok verdict when not verdict.Refused || verdict.Pipeline = "unprovable" ->
                                    yield mutation.Name + ": " + verdict.Outcome
                                | _ -> ()
                    ]

                if not (List.isEmpty weakened) then
                    failtest (
                        "Verification stopped naming a rule for these printer defects:\n"
                        + String.concat "\n" weakened
                    )
            }

            test "the mutations only the unproven verdict stops are exactly the recorded ones" {
                let moved =
                    [
                        for mutation in catalogue do
                            if mutation.Expectation = Unproven then
                                match measureMutation mutation with
                                | Ok verdict when verdict.Pipeline <> "unprovable" ->
                                    yield mutation.Name + ": " + verdict.Outcome
                                | _ -> ()
                    ]

                if not (List.isEmpty moved) then
                    failtest (
                        "These mutations are no longer settled by the unproven verdict:\n"
                        + String.concat "\n" moved
                        + "\nRecord each one where it now lands: Refused if a rule names it,\n"
                        + "Survives if nothing stops it."
                    )
            }

            test "the write path's bytes decode to the verified text in every encoding" {
                let body = "class C\n{\n    // caf\u00e9 \u2013 \u00fc \u65e5\u672c\n    int A = 1;\n}\n"

                let cases =
                    [
                        "utf-8", Array.empty<byte>, UTF8Encoding(false) :> Encoding
                        "utf-8 with a BOM", [| 0xefuy; 0xbbuy; 0xbfuy |], UTF8Encoding(false)
                        "utf-16le", [| 0xffuy; 0xfeuy |], UnicodeEncoding(false, false)
                        "utf-16be", [| 0xfeuy; 0xffuy |], UnicodeEncoding(true, false)
                        "utf-32le", [| 0xffuy; 0xfeuy; 0uy; 0uy |], UTF32Encoding(false, false)
                        "utf-32be", [| 0uy; 0uy; 0xfeuy; 0xffuy |], UTF32Encoding(true, false)
                    ]

                for name, preamble, encoding in cases do
                    let input = Array.append preamble (encoding.GetBytes body)

                    let struct (detected, detectedPreamble, source, printed, _, _, again, againPreamble, reread) =
                        roundTrip input

                    Expect.equal detectedPreamble preamble.Length (name + ": the preamble is read.")
                    Expect.stringContains source "caf\u00e9" (name + ": the body decodes.")
                    Expect.equal reread printed (name + ": the written bytes decode to the verified text.")
                    Expect.equal againPreamble detectedPreamble (name + ": the preamble survives the write.")

                    Expect.isTrue
                        (obj.ReferenceEquals(again, detected))
                        (name + ": the written bytes detect as the same encoding.")
            }

            test "every Windows-1252 byte survives the write path" {
                for value in 0x80..0xff do
                    let input =
                        Array.concat
                            [
                                Encoding.ASCII.GetBytes "class C { string S = \""
                                [| byte value |]
                                Encoding.ASCII.GetBytes "\"; }\n"
                            ]

                    let struct (detected, preamble, source, printed, _, written, again, againPreamble, reread) =
                        roundTrip input

                    let label = String.Format("byte 0x{0:x2}", value)

                    Expect.isFalse
                        (SourceEncoding.isUtf8 detected)
                        (label + ": a lone high byte is not UTF-8, so the fallback decodes it.")

                    Expect.equal preamble 0 (label + ": the fallback reads no preamble.")
                    Expect.equal source.Length input.Length (label + ": one byte is one character.")
                    Expect.equal reread printed (label + ": the written bytes decode to the verified text.")
                    Expect.equal againPreamble 0 (label + ": no preamble appears.")

                    Expect.isTrue
                        (obj.ReferenceEquals(again, detected))
                        (label + ": the written bytes detect as the same encoding.")

                    Expect.isTrue
                        (Array.contains (byte value) written)
                        (label + ": the byte itself is written back unchanged.")
            }

            test "the undetected printer defects are exactly the recorded ones" {
                let detected =
                    [
                        for mutation in catalogue do
                            if mutation.Expectation = Survives then
                                match measureMutation mutation with
                                | Ok verdict when verdict.Refused ->
                                    yield mutation.Name + ": " + verdict.Outcome
                                | _ -> ()
                    ]

                if not (List.isEmpty detected) then
                    failtest (
                        "These mutations are now refused. That is an improvement; record it by\n"
                        + "moving each one to Refused -- or to Unproven, when the refusal is\n"
                        + "only that nothing proves the output -- in the catalogue:\n"
                        + String.concat "\n" detected
                    )
            }
        ]

[<NoComparison; NoEquality>]
type private Site =
    {
        Mutator: string
        Start: int
        Length: int
        Replacement: string
    }

let private directiveTrivia (kind: TriviaKind) =
    match kind with
    | TriviaKind.IfDirectiveTrivia
    | TriviaKind.ElifDirectiveTrivia
    | TriviaKind.ElseDirectiveTrivia
    | TriviaKind.EndIfDirectiveTrivia
    | TriviaKind.RegionDirectiveTrivia
    | TriviaKind.EndRegionDirectiveTrivia
    | TriviaKind.DefineDirectiveTrivia
    | TriviaKind.UndefDirectiveTrivia
    | TriviaKind.ErrorDirectiveTrivia
    | TriviaKind.WarningDirectiveTrivia
    | TriviaKind.LineDirectiveTrivia
    | TriviaKind.LineSpanDirectiveTrivia
    | TriviaKind.PragmaWarningDirectiveTrivia
    | TriviaKind.PragmaChecksumDirectiveTrivia
    | TriviaKind.NullableDirectiveTrivia
    | TriviaKind.ShebangDirectiveTrivia -> true
    | _ -> false

let private commentTrivia (kind: TriviaKind) =
    match kind with
    | TriviaKind.SingleLineCommentTrivia
    | TriviaKind.MultiLineCommentTrivia
    | TriviaKind.SingleLineDocumentationCommentTrivia
    | TriviaKind.MultiLineDocumentationCommentTrivia -> true
    | _ -> false

let private sites (output: string) =
    let tree = SyntaxTree()
    Parser.parse output tree
    let buffer = tree.LexerBuffer
    let found = ResizeArray<Site>()

    let occupiedAfter (offset: int) =
        let mutable index = offset
        let mutable occupied = false

        while index < output.Length && output[index] <> '\n' do
            if output[index] <> ' ' && output[index] <> '\t' && output[index] <> '\r' then
                occupied <- true

            index <- index + 1

        occupied

    let commentOnlyAfter (offset: int) =
        let mutable index = offset

        while index < output.Length && (output[index] = ' ' || output[index] = '\t') do
            index <- index + 1

        index + 1 < output.Length
        && output[index] = '/'
        && (output[index + 1] = '/' || output[index + 1] = '*')

    let occupiedBefore (offset: int) =
        let mutable index = offset - 1
        let mutable occupied = false

        while index >= 0 && output[index] <> '\n' do
            if output[index] <> ' ' && output[index] <> '\t' && output[index] <> '\r' then
                occupied <- true

            index <- index - 1

        occupied

    let terminator (start: int) (length: int) =
        let mutable count = 0

        while count < length
              && (output[start + length - 1 - count] = '\n'
                  || output[start + length - 1 - count] = '\r') do
            count <- count + 1

        count

    for index = 0 to buffer.TriviaCount - 1 do
        let trivia = buffer.Trivia index
        let text = output.Substring(trivia.Start, trivia.Length)

        if commentTrivia trivia.Kind then
            let mutable body = 0

            while body < text.Length && (text[body] = '/' || text[body] = '*') do
                body <- body + 1

            if body < text.Length then
                found.Add
                    {
                        Mutator = "comment-text-changed"
                        Start = trivia.Start + body
                        Length = 0
                        Replacement = "Z"
                    }

            let ending = terminator trivia.Start trivia.Length

            if
                ending > 0
                && trivia.Kind <> TriviaKind.MultiLineCommentTrivia
                && occupiedAfter (trivia.Start + trivia.Length)
            then
                found.Add
                    {
                        Mutator =
                            if commentOnlyAfter (trivia.Start + trivia.Length) then
                                "comment-newline-deleted-before-a-comment"
                            else
                                "comment-newline-deleted"
                        Start = trivia.Start + trivia.Length - ending
                        Length = ending
                        Replacement = " "
                    }

        if directiveTrivia trivia.Kind then
            let ending = terminator trivia.Start trivia.Length

            if ending > 0 && occupiedAfter (trivia.Start + trivia.Length) then
                found.Add
                    {
                        Mutator =
                            if commentOnlyAfter (trivia.Start + trivia.Length) then
                                "directive-newline-deleted-before-a-comment"
                            else
                                "directive-newline-deleted"
                        Start = trivia.Start + trivia.Length - ending
                        Length = ending
                        Replacement = " "
                    }

            let mutable before = trivia.Start

            while before > 0 && (output[before - 1] = ' ' || output[before - 1] = '\t') do
                before <- before - 1

            if before > 0 && output[before - 1] = '\n' && occupiedBefore (before - 1) then
                let span = if before > 1 && output[before - 2] = '\r' then 2 else 1

                found.Add
                    {
                        Mutator = "newline-before-directive-deleted"
                        Start = before - span
                        Length = span
                        Replacement = " "
                    }

        if trivia.Kind = TriviaKind.DisabledTextTrivia then
            let mutable body = 0

            while body < text.Length && (text[body] = ' ' || text[body] = '\t' || text[body] = '\n' || text[body] = '\r') do
                body <- body + 1

            if body < text.Length then
                found.Add
                    {
                        Mutator = "disabled-text-changed"
                        Start = trivia.Start + body
                        Length = 0
                        Replacement = "Z"
                    }

                found.Add
                    {
                        Mutator = "disabled-text-reindented"
                        Start = trivia.Start + body
                        Length = 0
                        Replacement = "    "
                    }

    for index = 0 to buffer.TokenCount - 1 do
        let token = buffer.Token index

        if token.Length >= 3 then
            let text = output.Substring(token.Start, token.Length)

            if
                text.EndsWith("\"", StringComparison.Ordinal)
                && (text.StartsWith("\"", StringComparison.Ordinal)
                    || text.StartsWith("@\"", StringComparison.Ordinal))
                && not (text.StartsWith("\"\"\"", StringComparison.Ordinal))
            then
                found.Add
                    {
                        Mutator = "literal-space-inserted"
                        Start = token.Start + token.Length - 1
                        Length = 0
                        Replacement = " "
                    }

    found

let sweep (argv: string array) =
    if argv.Length < 1 then
        Console.Error.WriteLine "usage: --mutation-sweep <corpus-root> [files] [sites-per-mutator]"
        2
    else

    let root = argv[0]
    let fileLimit = if argv.Length > 1 then Int32.Parse argv[1] else 200
    let siteLimit = if argv.Length > 2 then Int32.Parse argv[2] else 3
    let perConfiguration = argv.Length > 3 && argv[3] = "configurations"

    let files =
        Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories)
        |> Seq.sort
        |> Seq.toArray

    let stride = max 1 (files.Length / max 1 fileLimit)

    let selected =
        [|
            let mutable index = 0

            while index < files.Length do
                yield files[index]
                index <- index + stride
        |]

    let refused = Dictionary<string, int>()
    let survived = Dictionary<string, int>()
    let masked = Dictionary<string, int>()
    let rules = Dictionary<string, int>()
    let examples = Dictionary<string, string>()
    let mutable total = 0
    let mutable skipped = 0

    let bump (table: Dictionary<string, int>) key =
        let mutable count = 0
        table.TryGetValue(key, &count) |> ignore
        table[key] <- count + 1

    for file in selected do
        try
            let source = SourceEncoding.read file

            if source.Length < 200_000 then
                let output = format source
                let available = sites output
                let used = Dictionary<string, int>()

                for site in available do
                    let mutable count = 0
                    used.TryGetValue(site.Mutator, &count) |> ignore

                    if count < siteLimit then
                        used[site.Mutator] <- count + 1

                        let mutated =
                            output.Remove(site.Start, site.Length).Insert(site.Start, site.Replacement)

                        if not (String.Equals(mutated, source, StringComparison.Ordinal)) then
                            total <- total + 1

                            let verdict =
                                measureEditWith
                                    perConfiguration
                                    (Path.GetFileName file)
                                    source
                                    mutated

                            if verdict.Refused then
                                bump refused site.Mutator
                                bump rules (site.Mutator + "/" + verdict.Pipeline)

                                if verdict.OnlyDirectiveLine then
                                    bump rules (
                                        site.Mutator
                                        + "/ONLY the directive-line comparison, in every configuration"
                                    )
                            else
                                bump survived site.Mutator

                                if verdict.Diagnosis <> "ok" then
                                    bump masked site.Mutator

                                if not (examples.ContainsKey site.Mutator) then
                                    examples[site.Mutator] <-
                                        String.Format(
                                            "{0} at offset {1}: {2}",
                                            file,
                                            site.Start,
                                            verdict.Outcome
                                        )
            else
                skipped <- skipped + 1
        with error ->
            skipped <- skipped + 1
            Console.Error.WriteLine(file + ": " + error.Message)

    Console.Out.WriteLine(
        String.Format(
            "{0} files in the corpus, {1} sampled, {2} skipped, {3} mutations",
            files.Length,
            selected.Length,
            skipped,
            total
        )
    )

    Console.Out.WriteLine()
    Console.Out.WriteLine(String.Format("{0}  {1}  {2}  {3}", pad 34 "mutator", pad 9 "refused", pad 9 "survived", "masked a named refusal"))

    for mutator in Seq.sort (Seq.distinct (Seq.append refused.Keys survived.Keys)) do
        let read (table: Dictionary<string, int>) =
            let mutable count = 0
            table.TryGetValue(mutator, &count) |> ignore
            count

        Console.Out.WriteLine(
            String.Format(
                "{0}  {1}  {2}  {3}",
                pad 34 mutator,
                pad 9 (string (read refused)),
                pad 9 (string (read survived)),
                read masked
            )
        )

    Console.Out.WriteLine()

    for pair in Seq.sortBy (fun (pair: KeyValuePair<string, int>) -> pair.Key) rules do
        Console.Out.WriteLine(String.Format("refused by {0}: {1}", pair.Key, pair.Value))

    Console.Out.WriteLine()

    for pair in examples do
        Console.Out.WriteLine(String.Format("survivor example {0}: {1}", pair.Key, pair.Value))

    0
