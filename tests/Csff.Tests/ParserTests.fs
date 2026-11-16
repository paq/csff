module Csff.Tests.ParserTests

open System
open System.Collections.Generic
open System.Diagnostics
open System.Runtime.CompilerServices
open System.Runtime.InteropServices
open System.Threading
open Csff.Conformance
open Csff.Lexer
open Expecto
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax
open Csff.Parser

let private expectConforms result =
    Expect.equal result (Ok()) "A faithful CST must conform."

let private expectSourceConforms filePath source =
    let tree = SyntaxTree()
    NodeOracle.check filePath source tree |> expectConforms
    RoslynOracle.checkBuffer filePath source tree.LexerBuffer |> expectConforms
    RoundTrip.checkBuffer filePath source tree.LexerBuffer |> expectConforms

let private expectFailure fragments result =
    let message = Expect.wantError result "The malformed CST must fail."

    for fragment in fragments do
        Expect.stringContains message fragment "The report must locate and explain the failure."

let private oracleTree (source: string) =
    let options =
        CSharpParseOptions(LanguageVersion.Preview, DocumentationMode.Diagnose)
            .WithFeatures([ KeyValuePair("FileBasedProgram", "true") ])

    let root = CSharpSyntaxTree.ParseText(source, options).GetRoot()
    let tree = SyntaxTree()

    let rec appendNode (node: SyntaxNode) parent =
        let firstToken = tree.TokenCount

        let placeholder =
            {
                Kind = enum<NodeKind> node.RawKind
                Parent = parent
                ChildStart = 0
                ChildCount = 0
                TokenStart = firstToken
                TokenCount = 0
            }

        let index = tree.AddNode placeholder
        let children = ResizeArray<int>()

        for child in node.ChildNodesAndTokens() do
            if child.IsNode then
                children.Add(appendNode (child.AsNode()) index)
            else
                let token = child.AsToken()
                let triviaStart = tree.LexerBuffer.NextTriviaIndex

                for trivia in Seq.append token.LeadingTrivia token.TrailingTrivia do
                    tree.LexerBuffer.AddTrivia(
                        enum<TriviaKind> trivia.RawKind,
                        trivia.FullSpan.Start,
                        trivia.FullSpan.Length
                    )

                let tokenIndex =
                    tree.AddToken
                        {
                            Kind = enum<TokenKind> token.RawKind
                            Start = token.SpanStart
                            Length = token.Span.Length
                            TriviaStart = triviaStart
                            LeadingCount = token.LeadingTrivia.Count
                            TrailingCount = token.TrailingTrivia.Count
                        }

                children.Add(-tokenIndex - 1)

        let childStart = tree.ChildCount

        for child in children do
            tree.AddChild child |> ignore

        tree.SetNode(
            index,
            { placeholder with
                ChildStart = childStart
                ChildCount = children.Count
                TokenCount = tree.TokenCount - firstToken
            }
        )

        index

    appendNode root -1 |> ignore
    tree.CopyLexicalTrivia()
    tree

let private findToken kind (tree: SyntaxTree) =
    [ 0 .. tree.TokenCount - 1 ]
    |> List.find (fun index -> (tree.Token index).Kind = kind)

let private findNode kind (tree: SyntaxTree) =
    [ 0 .. tree.NodeCount - 1 ]
    |> List.find (fun index -> (tree.Node index).Kind = kind)

let private emptyNode =
    {
        Kind = NodeKind.CompilationUnit
        Parent = -1
        ChildStart = 0
        ChildCount = 0
        TokenStart = 0
        TokenCount = 0
    }

let tests =
    testList
        "parser"
        [
            test "a local function's type parameter list ends where C# ends it" {
                for source in
                    [
                        "class C{void M(){int F<[A(X<Y>>=1)] T>() => 1;}}"
                        "class C{void M(){int F<[A(X<Y<Z>>>=1)] T>() => 1;}}"
                        "class C{void M(){int F<[A(X<Y>>1)] T>() => 1;}}"
                        "class C{void M(){int F<[A(1)] T>() => 1;}}"
                        "class C{void M(){int F<[A][B] T>() => 1;}}"
                        "class C{void M(){int F<[A(new[]{1,2})] T>() => 1;}}"
                        "class C{void M(){int F<[A(X<Y>>=1)] T,[B] U>() => 1;}}"
                        "class C{void M(){int F<T>() => 1;}}"
                        "class C{void M(){int F<T,U>() => 1;}}"
                        "class C{void M(){int F<T>() where T : struct => 1;}}"
                        "class C{void M(List<int> a){var x = a[0] < 1;}}"
                        "class C{void M(int a,int b,int c){var x = a<b>>=c;}}"
                        "class C{void M(){var x = new int[]{1}[0];}}"
                        "class C{void M(){Action<int> f = x => {};}}"
                        "class C{void M(){int[] a = {1};var y = a[0];}}"
                    ] do
                    let tree = SyntaxTree()
                    Expect.equal (NodeOracle.check "local.cs" source tree) (Ok()) source
            }
            test "a <= after a type argument list settles it as a generic name" {
                let follower op =
                    let source = $"class C{{void M(){{var r = A<B> {op} C;}}}}"
                    let tree = SyntaxTree()
                    NodeOracle.check "follower.cs" source tree

                for op in [ "<="; ">="; "is"; "as"; "=="; "!="; "&&"; "||" ] do
                    Expect.equal (follower op) (Ok()) $"A<B> {op} C is a generic name."
            }
            test "the followers only invalid C# can reach are left out of the set" {
                for op in [ "{"; "=>" ] do
                    let source = $"class C{{void M(){{var r = A<B> {op} C;}}}}"
                    let tree = SyntaxTree()

                    Expect.notEqual
                        (NodeOracle.check "recovery.cs" source tree)
                        (Ok())
                        $"A<B> {op} C does not compile, and the two parsers recover differently."
            }
            test "an empty format specifier is complete, a missing close brace is not" {
                let complete = SyntaxTree()
                Parser.parse "class C { string M() => $\"{x:}\" + $@\"{x,3:}\"; }" complete

                Expect.isTrue
                    complete.IsComplete
                    "{x:} holds an empty format, which Roslyn reports nothing about."

                let missing = SyntaxTree()
                Parser.parse "class C { string M() => $\"{x:\"; }" missing

                Expect.isFalse
                    missing.IsComplete
                    "{x: without its brace is still incomplete (CS8076)."

                let replaced = SyntaxTree()
                Parser.parse "class C { string M() => $\"{x:}\"; }" replaced

                let index =
                    seq { 0 .. replaced.TokenCount - 1 }
                    |> Seq.find (fun i ->
                        let token = replaced.Token i
                        token.Kind = TokenKind.InterpolatedStringTextToken && token.Length = 0)

                let empty = replaced.Token index
                replaced.SetToken(index, { empty with Kind = TokenKind.BadToken })

                Expect.isFalse
                    replaced.IsComplete
                    "A bad token where the empty text was is incomplete."

                replaced.SetToken(index, { empty with Length = 1 })
                Expect.isTrue replaced.IsComplete "A text with a width there is complete again."

                expectSourceConforms "escape.cs" "class C { string M() => $\"\\q{x:}\"; }"
            }
            test "escaped leading quotes preserve verbatim interpolation" {
                for source in
                    [
                        "class C { string M(int x) => $@\"\"\"hello {x}\"\"\"; }"
                        "class C { string M(int x) => @$\"\"\"hello {x}\"\"\"; }"
                    ] do
                    expectSourceConforms "regression.cs" source
            }
            test "partial before a declarator's name is the field's type" {
                expectSourceConforms
                    "partial-field.cs"
                    "class C { partial field; partial a = null, b; partial class D {} partial void M(); partial T g; }"
            }
            test "final indexer parameter defaults preserve the body" {
                for source in
                    [
                        "class C { public int this[int i, int j = 0] => i + j; }"
                        "class C { public int this[int i, int j = 0] { get => i + j; } }"
                        "class C { public int this[int i, int[] j = [0, 1]] => i; }"
                    ] do
                    expectSourceConforms "regression.cs" source
            }
            test "a top-level delegate may return a tuple" {
                for source in
                    [
                        "delegate (int a, int b) Del((int a, int b) d);"
                        "var f = delegate (int x) { return x; };\nSystem.Action g = delegate { };"
                    ] do
                    expectSourceConforms "tuple-delegate.cs" source
            }
            test "nullable array is types survive a later conditional colon" {
                for source in
                    [
                        "class C { int M(object x, bool flag) => x is int?[] && flag ? 1 : 2; }"
                        "class C { int M(object x, bool flag) => x is int?[][] && flag ? 1 : 2; }"
                        "class C { int M(object x, bool flag) => x is int?[,] && flag ? 1 : 2; }"
                        "class C { int M(object x, bool flag) => x is int? && flag ? 1 : 2; }"
                        "class C { int M(object x, bool flag) => x is int?[] ? flag ? 1 : 2 : 3; }"
                        "class C { object M(object x) => x is int ? [] : new int[0]; }"
                        "class C { int M(object x, bool flag) => x is G<G<int>>?[] && flag ? 1 : 2; }"
                        "class C { int[] M(object x, bool flag) => x is int?[] && flag ? [] : new int[1]; }"
                        "class C { int[] M(object x, bool flag) => x is int?[] && flag ? [1] : [2]; }"
                    ] do
                    expectSourceConforms "regression.cs" source
            }
            test "async partial void methods are modifiers then a return type" {
                for source in
                    [
                        "partial class C { partial void F(); async partial void F() { } }"
                        "partial class C { public partial void F(); public async partial void F() { } }"
                    ] do
                    expectSourceConforms "async-partial.cs" source
            }
            test "async remains an identifier when it names the return type" {
                for source in
                    [
                        "class async {} class C { async M() => null; }"
                        "class async {} class C { async field; async P => null; async[] A; async? N; async M<T>() => null; }"
                        "class async {} class C { async async M() => null; async System.Threading.Tasks.Task N() => null; async Task<int> P() => null; }"
                        "class C { async.Nested M() => null; async<T> N() => null; async operator +(C a, C b) => null; }"
                        "class C { async public Task M() => null; async static Task N() => null; }"
                    ] do
                    expectSourceConforms "regression.cs" source
            }
            test "attribute lists in front of a namespace belong to it" {
                for source in
                    [
                        "[A] namespace N { class C { } }"
                        "[assembly: A]\n[B] [C]\nnamespace N { }"
                        "[A(nameof(await))] namespace N { }"
                        "[A(await(x))] namespace N { }"
                        "[A][B] namespace N;"
                    ] do
                    expectSourceConforms "attributed-namespace.cs" source

                let unterminated = SyntaxTree()
                Parser.parse "[A($\"{x}\")" unterminated

                Expect.isFalse
                    unterminated.IsComplete
                    "An unterminated attribute list is incomplete."
            }
            test "newer syntax from the testbed corpus conforms to Roslyn" {
                for source in
                    [
                        "static class E { extension(Enum) { } extension<T>(EqualityComparer<T>) where T : class { } extension(int x) { } extension(System.Reflection.TypeAttributes) { } }"
                        "class C { void M(int i, __arglist) { F(1, __arglist(2, 3)); var r = __makeref(i); var t = __reftype(r); __refvalue(r, int) += 1; } }"
                        "class C { [DllImport(\"libc\")] static extern void printf(string format, __arglist); }"
                        "public closed class C { public safe uint S; public static extern safe int A(); public static safe partial int B(); int M(char* p) => unsafe(*p); object N() => unsafe(F(1)); }"
                        "closed class D; public closed partial class E { } safe struct F { }"
                        "class C { void M() { int safe = 1; var closed = safe; } }"
                        "class C { void M() { P(static delegate (int x) { }); Q(async static delegate { }); R(static async delegate () { }); } }"
                        "class C { void M() { outer: for (;;) { for (;;) { continue outer; break outer; } } } }"
                        "class C { void M() { var r = from c in cs where !(only) select new object[] { c }; } }"
                        "class C { Task<int> M() { await a.B(c); await a[0]; await a++; await b = 1; await d; return 1; } }"
                        "class C { string M() => $\"total {n::#,#;00} pages\"; string N() => $\"{a::x}{(global::X.Y)}\"; }"
                    ] do
                    expectSourceConforms "regression.cs" source
            }
            test "patterns from the testbed corpus conform to Roslyn" {
                for source in
                    [
                        "class C { string M(float v) => v switch { float.NaN => \"\", int.MaxValue when !a => \"\", _ => \"\" }; }"
                        "class C { bool M(object m) => m is float.NaN || m is { Name: nameof(string.Remove) } || m is nameof(x) or nameof(y.z); }"
                        "class C { void M() { switch (x) { case nameof(string.Concat): break; case nameof(a) or nameof(b): break; case nameof(c) when d: break; } } }"
                        "class C { void M() { var s = (0, int.MaxValue) switch { (0, int.MaxValue) => 1, _ => 2 }; } }"
                        "class C { bool M(object o) => o is T or && !or.I; bool N(object o) => o is not T or; void P() { switch (x) { case A.B or: case C and: case D or when e: break; } } }"
                        "class C { object M() => x switch { T or => 1, [_] and => 2, {} or => 3 }; }"
                        "class C { void M() { if (a is bool when) {} switch (y) { case 1 when x is bool when: break; } } }"
                        "class C { int M() => y switch { 1 when x is bool when => 0, bool when c => 1 }; }"
                        "class C { bool M() => a is A + 1 or B * 2; bool N() => a is B * c; bool O() => a is B * 2; }"
                        "class C { unsafe bool M() => a is B* p; unsafe bool N() => a is B*[] p; }"
                        "class C { bool M() => a is not (string?, string?)[] p; bool N() => a is (int, int)[]; bool O() => a is (A, B) p; }"
                    ] do
                    expectSourceConforms "regression.cs" source
            }
            testSequenced
            <| test "chained access lookaheads reuse suffix results" {
                let allocated count =
                    let source = "x=a" + String.replicate count "?[0]" + ";"
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    Parser.parse source tree

                    Array.init 5 (fun _ ->
                        let before = GC.GetAllocatedBytesForCurrentThread()
                        Parser.parse source tree
                        GC.GetAllocatedBytesForCurrentThread() - before)

                let small = allocated 256
                let large = allocated 512

                Expect.isLessThan
                    (float (Array.min large) / float (Array.min small))
                    3.0
                    $"Doubling the accesses must not rebuild every suffix cache. Warmed bytes: 256=%A{small}; 512=%A{large}."
            }
            test "incomplete nested conditional recovery stays bounded" {
                let allocated count leaf =
                    let source = "x=" + String.replicate count "a?" + leaf + ";"
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    let before = GC.GetAllocatedBytesForCurrentThread()
                    Parser.parse source tree
                    let bytes = GC.GetAllocatedBytesForCurrentThread() - before

                    Expect.isTrue
                        (seq { 0 .. tree.TokenCount - 1 }
                         |> Seq.exists (fun index ->
                             let token = tree.Token index
                             token.Kind = TokenKind.ColonToken && token.Length = 0))
                        "Incomplete arms must still report missing colons."

                    float bytes

                for leaf in
                    [
                        "b ? [0] : []"
                        "()=>b ? [0] : []"
                        "p=>b ? [0] : []"
                        "delegate { x=b ? [0] : []; }"
                        "$\"{b ? [0] : []}\""
                    ] do
                    let small = allocated 8 leaf
                    let large = allocated 12 leaf

                    Expect.isLessThan
                        (large / small)
                        3.0
                        $"Incomplete arms must not repeat failed recovery exponentially: {leaf}"
            }
            testSequenced
            <| test "unambiguous nested true arms parse linearly" {
                for leaf in [ "b"; "F(items?[0])"; "[0]" ] do
                    let workloads =
                        [| 256; 1024 |]
                        |> Array.map (fun count ->
                            struct ("x="
                                    + String.replicate count "a?"
                                    + leaf
                                    + String.replicate count ":c"
                                    + "; y=items?[0];",
                                    SyntaxTree()))

                    let warmup = Stopwatch.StartNew()

                    while warmup.Elapsed.TotalSeconds < 2.0 do
                        for struct (source, tree) in workloads do
                            Parser.parse source tree

                    let elapsed index =
                        let struct (source, tree) = workloads[index]
                        let start = Stopwatch.GetTimestamp()
                        let mutable iterations = 0

                        while Stopwatch.GetElapsedTime(start).TotalMilliseconds < 100.0 do
                            Parser.parse source tree
                            iterations <- iterations + 1

                        Stopwatch.GetElapsedTime(start).TotalMilliseconds / float iterations

                    let samples = Array.init 2 (fun _ -> Array.zeroCreate<float> 5)

                    for sample = 0 to 4 do
                        for offset = 0 to 1 do
                            let index = (sample + offset) % 2
                            samples[index][sample] <- elapsed index

                    let median values =
                        Array.sort values |> fun values -> values[2]

                    let ratio = median samples[1] / median samples[0]
                    printfn "nested true arms / %s: ms per parse=%A; ratio=%.3f" leaf samples ratio

                    Expect.isLessThan
                        ratio
                        8.0
                        $"Four times the depth must not enable quadratic arm rescans ({leaf}). Paired warmed ms/parse: %A{samples}."
            }
            testSequenced
            <| test "interpolation-heavy parsing scales linearly" {
                let allocated count =
                    let source = String.replicate count "x=$\"{a}\";"
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    let before = GC.GetAllocatedBytesForCurrentThread()
                    Parser.parse source tree
                    float (GC.GetAllocatedBytesForCurrentThread() - before)

                Expect.isLessThan
                    (allocated 1024 / allocated 512)
                    3.0
                    "Interpolation allocation grows with the input."

                let workloads =
                    [| 512; 2048 |]
                    |> Array.map (fun count ->
                        struct (String.replicate count "x=$\"{a}\";", SyntaxTree()))

                let warmup = Stopwatch.StartNew()

                while warmup.Elapsed.TotalSeconds < 2.0 do
                    for struct (source, tree) in workloads do
                        Parser.parse source tree

                let elapsed index =
                    let struct (source, tree) = workloads[index]
                    let start = Stopwatch.GetTimestamp()
                    let mutable iterations = 0

                    while Stopwatch.GetElapsedTime(start).TotalMilliseconds < 100.0 do
                        Parser.parse source tree
                        iterations <- iterations + 1

                    Stopwatch.GetElapsedTime(start).TotalMilliseconds / float iterations

                let samples = Array.init 2 (fun _ -> Array.zeroCreate<float> 5)

                for sample = 0 to 4 do
                    for offset = 0 to 1 do
                        let index = (sample + offset) % 2
                        samples[index][sample] <- elapsed index

                let median values =
                    Array.sort values |> fun values -> values[2]

                Expect.isLessThan
                    (median samples[1] / median samples[0])
                    8.0
                    "Four times as many interpolations must not repeat whole-file work."
            }
            test "a query expression can be a whole statement" {
                for source in
                    [
                        "class C { void M() { from s in \"a\" select s; } }"
                        "class C { void M() { from x; from x = 1; } }"
                        "class C { async void M(System.Collections.Generic.IEnumerable<from> xs, System.Collections.Generic.IAsyncEnumerable<from> ys) { foreach (from s in xs) { } await foreach (from t in ys) { } } }"
                    ] do
                    expectSourceConforms "query-statement.cs" source
            }
            test "conditional using resources are expressions" {
                for source in
                    [
                        "class C { void M(bool flag, System.IDisposable a, System.IDisposable b) { using (flag ? a : b) {} } }"
                        "class C { void M() { using (flag ? a = b : c) {} using (flag ? a : b = c) {} } }"
                        "class C { void M() { using (T? a = b) {} using (T? a = flag ? b : c) {} } }"
                        "class C { void M() { using (flag ? a = flag ? b : c : d) {} } }"
                    ] do
                    expectSourceConforms "regression.cs" source
            }
            test "NodeKind is Roslyn's complete non-token non-trivia complement" {
                let expected =
                    Enum.GetValues<SyntaxKind>()
                    |> Array.filter (fun kind ->
                        not (SyntaxFacts.IsAnyToken kind)
                        && not (SyntaxFacts.IsTrivia kind)
                        && not ((string kind).EndsWith("Trivia", StringComparison.Ordinal)))
                    |> Array.map (fun kind -> string kind, int kind)

                let actual =
                    Enum.GetValues<NodeKind>() |> Array.map (fun kind -> string kind, int kind)

                Expect.equal actual expected "Every name and numeric value is Roslyn's."

                for kind in
                    [ SyntaxKind.PreprocessingMessageTrivia; SyntaxKind.SkippedTokensTrivia ] do
                    Expect.isFalse (SyntaxFacts.IsTrivia kind) "Pin Roslyn's trivia predicate trap."

                    Expect.isFalse
                        (Enum.IsDefined(typeof<NodeKind>, int kind))
                        "These are never nodes."

                Expect.isTrue
                    (Enum.IsDefined(typeof<NodeKind>, int SyntaxKind.OmittedTypeArgument))
                    "Omitted type arguments are nodes."

                Expect.isFalse
                    (Enum.IsDefined(
                        typeof<NodeKind>,
                        int SyntaxKind.OmittedArraySizeExpressionToken
                    ))
                    "Omitted array sizes have a token too."
            }
            test "CST nodes are six integers without GC references" {
                Expect.isFalse
                    (RuntimeHelpers.IsReferenceOrContainsReferences<Node>())
                    "No per-node references."

                Expect.equal (Marshal.SizeOf<Node>()) 24 "Six 32-bit fields."
            }
            test "CST storage grows and reset reuses all buffers" {
                let tree = SyntaxTree()
                Expect.equal tree.RootIndex -1 "An empty buffer has no root."

                let fill () =
                    for index in 0..4096 do
                        tree.AddNode emptyNode |> ignore
                        tree.AddChild(-index - 1) |> ignore
                        tree.LexerBuffer.AddTrivia(TriviaKind.WhitespaceTrivia, index, 1)
                        tree.AddTrivia(tree.LexerBuffer.Trivia index) |> ignore

                        tree.AddToken
                            {
                                Kind = TokenKind.IdentifierToken
                                Start = index
                                Length = 1
                                TriviaStart = index
                                LeadingCount = 1
                                TrailingCount = 0
                            }
                        |> ignore

                fill ()

                Expect.equal
                    (tree.NodeSpan().Length,
                     tree.ChildSpan().Length,
                     tree.TokenSpan().Length,
                     tree.TriviaSpan().Length)
                    (4097, 4097, 4097, 4097)
                    "All arrays grow."

                Expect.equal (tree.Child 0) -1 "Token zero is encoded as -1."
                Expect.equal (~~~(tree.Child 4096)) 4096 "The sign encoding round-trips."
                tree.Reset()

                Expect.equal
                    (tree.NodeCount, tree.ChildCount, tree.TokenCount, tree.TriviaCount)
                    (0, 0, 0, 0)
                    "Reset drops contents."

                let before = GC.GetAllocatedBytesForCurrentThread()
                fill ()
                let allocated = GC.GetAllocatedBytesForCurrentThread() - before
                Expect.equal allocated 0L "Once grown, filling allocates no nodes or arrays."
            }
            test "parser tokens can be promoted without changing the lexical stream" {
                let tree = SyntaxTree()
                Lexer.lex "record" tree.LexerBuffer
                let lexical = tree.LexerBuffer.Token 0

                tree.AddToken
                    { lexical with
                        Kind = TokenKind.RecordKeyword
                    }
                |> ignore

                Expect.equal
                    (tree.Token 0).Kind
                    TokenKind.RecordKeyword
                    "The parser owns its stream."

                Expect.equal
                    (tree.LexerBuffer.Token 0).Kind
                    TokenKind.IdentifierToken
                    "The lexer keeps its contract."

                tree.Reset()

                Expect.equal
                    tree.LexerBuffer.TokenCount
                    0
                    "The lexical buffer resets with the tree."
            }
            test "node oracle accepts Roslyn-shaped CSTs including parser-only tokens" {
                let fixtures =
                    [
                        ""
                        " // exterior\r\nclass C {} // tail\r\n"
                        "record C { int P { get; init; } bool M(int x) => x is > 0 and not 3 or 4; }"
                        "class C { List<List<int>> x; int[,] y; System.Type t = typeof(List<>); }"
                        "class C { object M(int[] xs) => from x in xs where x > 0 select x; }"
                        "#!/usr/bin/env dotnet\n#if false\nignored text\n#endif\n/// <summary>Doc</summary>\nclass C {}"
                        "class C { void M( { @@@"
                    ]

                for source in fixtures do
                    NodeOracle.checkTree "fixture.cs" source (oracleTree source) |> expectConforms
            }
            test "the tree's narrow node readers agree with the record they read from" {
                let fixtures =
                    [
                        "class C {}"
                        "class C { void M() { if (a) { b(); } else { c(d, e); } } }"
                        "namespace N { using System; record R(int X) : B { } }"
                        "class C { void M( { @@@"
                    ]

                for source in fixtures do
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    Expect.isGreaterThan tree.NodeCount 0 "The fixture parses to nodes."

                    for index in 0 .. tree.NodeCount - 1 do
                        let node = tree.Node index

                        Expect.equal
                            (tree.NodeKind index)
                            node.Kind
                            $"Node {index} of {source}: the narrow kind must be the record's."

                        let struct (items, start, count) = tree.ChildRange index
                        let memory = tree.ChildMemory index

                        Expect.equal
                            count
                            memory.Length
                            $"Node {index} of {source}: both child ranges must be one length."

                        Expect.sequenceEqual
                            (items[start .. start + count - 1])
                            (memory.ToArray())
                            $"Node {index} of {source}: both child ranges must be one slice."
            }
            test "node oracle traverses children independently of node allocation order" {
                let source = "class C {} class D {}"
                let tree = oracleTree source
                let first = tree.Node 1
                let second = tree.Node 2
                tree.SetNode(1, second)
                tree.SetNode(2, first)
                let root = tree.Node 0
                tree.SetChild(root.ChildStart, 2)
                tree.SetChild(root.ChildStart + 1, 1)
                NodeOracle.checkTree "order.cs" source tree |> expectConforms
            }
            test "node oracle detects node kind, start, and length changes" {
                let source = "class C {}"

                let changes: (Node -> Node) list =
                    [
                        (fun node ->
                            { node with
                                Kind = NodeKind.IdentifierName
                            })
                        (fun node ->
                            { node with
                                TokenStart = 1
                                TokenCount = node.TokenCount - 1
                            })
                        (fun node ->
                            { node with
                                TokenCount = node.TokenCount - 1
                            })
                    ]

                for change in changes do
                    let tree = oracleTree source
                    tree.SetNode(1, change (tree.Node 1))

                    NodeOracle.checkTree "node.cs" source tree
                    |> expectFailure
                        [
                            "node.cs: offset 0"
                            "node 0 mismatch"
                            "Roslyn: ClassDeclaration"
                            "csff:"
                            "text="
                        ]
            }
            test "node oracle detects contextual promotion, split closers, and omitted tokens" {
                let cases =
                    [
                        "record C;", TokenKind.RecordKeyword, TokenKind.IdentifierToken
                        "class C { List<List<int>> x; }",
                        TokenKind.GreaterThanToken,
                        TokenKind.GreaterThanGreaterThanToken
                        "class C { int[,] x; }",
                        TokenKind.OmittedArraySizeExpressionToken,
                        TokenKind.None
                        "class C { System.Type t = typeof(List<>); }",
                        TokenKind.OmittedTypeArgumentToken,
                        TokenKind.None
                    ]

                for source, expected, wrong in cases do
                    let tree = oracleTree source
                    let index = findToken expected tree
                    let token = tree.Token index
                    tree.SetToken(index, { token with Kind = wrong })

                    NodeOracle.checkTree "parser-token.cs" source tree
                    |> expectFailure
                        [
                            $"parser-token.cs: offset {token.Start}"
                            $"token {index} mismatch"
                            $"Roslyn: {expected}"
                            $"csff: {wrong}"
                            "text="
                        ]
            }
            test "node oracle detects token offsets and widths including zero-width EOF" {
                for start, length in [ 0, 0; 1, 1 ] do
                    let tree = oracleTree " "
                    let token = tree.Token 0

                    tree.SetToken(
                        0,
                        { token with
                            Start = start
                            Length = length
                        }
                    )

                    NodeOracle.checkTree "token-span.cs" " " tree
                    |> expectFailure
                        [
                            "token-span.cs: offset 1"
                            "token 0 mismatch"
                            "Roslyn: EndOfFileToken"
                            "csff:"
                            "text="
                        ]
            }
            test "node oracle detects mixed child order and corrupt parent links" {
                let source = "class C {} class D {}"
                let tree = oracleTree source
                let root = tree.Node 0
                tree.SetChild(root.ChildStart, 2)
                tree.SetChild(root.ChildStart + 1, 1)

                NodeOracle.checkTree "order.cs" source tree
                |> expectFailure [ "order.cs: offset 0"; "node 0 mismatch"; "text=" ]

                let tree = oracleTree "class C {}"
                let node = tree.Node 1
                let first = tree.Child node.ChildStart
                tree.SetChild(node.ChildStart, tree.Child(node.ChildStart + 1))
                tree.SetChild(node.ChildStart + 1, first)

                NodeOracle.checkTree "punctuation.cs" "class C {}" tree
                |> expectFailure
                    [
                        "punctuation.cs: offset 0"
                        "token 0 mismatch"
                        "Roslyn: ClassKeyword"
                        "csff: IdentifierToken"
                    ]

                tree.SetNode(1, { node with Parent = 1 })

                NodeOracle.checkTree "parent.cs" "class C {}" tree
                |> expectFailure [ "parent.cs: offset"; "node parent mismatch" ]
            }
            test "node oracle rejects reparenting even when pre-order and spans are unchanged" {
                let source = "class C { int x; }"
                let tree = oracleTree source
                let fieldIndex = findNode NodeKind.FieldDeclaration tree
                let variableIndex = findNode NodeKind.VariableDeclaration tree
                let declaratorIndex = findNode NodeKind.VariableDeclarator tree
                let field = tree.Node fieldIndex
                let variable = tree.Node variableIndex
                let semicolon = tree.Child(field.ChildStart + 1)

                tree.SetNode(
                    variableIndex,
                    { variable with
                        ChildCount = variable.ChildCount - 1
                    }
                )

                tree.SetNode(
                    declaratorIndex,
                    { tree.Node declaratorIndex with
                        Parent = fieldIndex
                    }
                )

                let childStart = tree.ChildCount

                for child in [ variableIndex; declaratorIndex; semicolon ] do
                    tree.AddChild child |> ignore

                tree.SetNode(
                    fieldIndex,
                    { field with
                        ChildStart = childStart
                        ChildCount = 3
                    }
                )

                NodeOracle.checkTree "reparent-node.cs" source tree
                |> expectFailure
                    [
                        "reparent-node.cs: offset 14"
                        "node 4 parent mismatch"
                        "Roslyn: VariableDeclarator"
                        "parent=VariableDeclaration"
                        "parent=FieldDeclaration"
                    ]

                let tree = oracleTree source
                let field = tree.Node fieldIndex
                let variable = tree.Node variableIndex
                let childStart = tree.ChildCount

                for index in variable.ChildStart .. variable.ChildStart + variable.ChildCount - 1 do
                    tree.AddChild(tree.Child index) |> ignore

                tree.AddChild semicolon |> ignore

                tree.SetNode(
                    variableIndex,
                    { variable with
                        ChildStart = childStart
                        ChildCount = variable.ChildCount + 1
                    }
                )

                tree.SetNode(fieldIndex, { field with ChildCount = 1 })

                NodeOracle.checkTree "reparent-token.cs" source tree
                |> expectFailure
                    [
                        "reparent-token.cs: offset 15"
                        "token 5 parent mismatch"
                        "Roslyn: SemicolonToken"
                        "parent=FieldDeclaration"
                        "parent=VariableDeclaration"
                    ]
            }
            test "node oracle detects missing and extra nodes and tokens" {
                NodeOracle.checkTree "missing-node.cs" "class C {}" (SyntaxTree())
                |> expectFailure
                    [
                        "missing-node.cs: offset 0"
                        "Roslyn: ClassDeclaration"
                        "csff: <missing node>"
                    ]

                let tree = oracleTree "class C {}"

                NodeOracle.checkTree "extra-node.cs" "" tree
                |> expectFailure
                    [
                        "extra-node.cs: offset 0"
                        "Roslyn: <missing node>"
                        "csff: ClassDeclaration"
                    ]

                let tree = SyntaxTree()
                tree.AddNode emptyNode |> ignore

                NodeOracle.checkTree "missing-token.cs" "" tree
                |> expectFailure
                    [
                        "missing-token.cs: offset 0"
                        "Roslyn: EndOfFileToken"
                        "csff: <missing token>"
                    ]

                let tree = oracleTree ""
                let index = tree.AddToken(tree.Token 0)
                tree.AddChild(-index - 1) |> ignore

                tree.SetNode(
                    0,
                    { tree.Node 0 with
                        ChildCount = 2
                        TokenCount = 2
                    }
                )

                NodeOracle.checkTree "extra-token.cs" "" tree
                |> expectFailure
                    [
                        "extra-token.cs: offset 0"
                        "token 1 count mismatch"
                        "Roslyn: <missing token>"
                        "csff: EndOfFileToken"
                    ]
            }
            test "node oracle rejects invalid ranges, cycles, and unreachable storage" {
                let source = "class C {}"
                let tree = oracleTree source

                tree.SetNode(
                    1,
                    { tree.Node 1 with
                        ChildCount = Int32.MaxValue
                    }
                )

                NodeOracle.checkTree "range.cs" source tree
                |> expectFailure [ "range.cs: offset"; "invalid child range" ]

                let tree = oracleTree source

                tree.SetNode(
                    1,
                    { tree.Node 1 with
                        TokenCount = Int32.MaxValue
                    }
                )

                NodeOracle.checkTree "range.cs" source tree
                |> expectFailure [ "range.cs: offset"; "invalid node token range" ]

                let tree = oracleTree source
                tree.SetChild((tree.Node 0).ChildStart, 0)

                NodeOracle.checkTree "cycle.cs" source tree
                |> expectFailure [ "cycle.cs: offset"; "repeated child node" ]

                let tree = oracleTree source
                tree.AddNode emptyNode |> ignore

                NodeOracle.checkTree "unreachable.cs" source tree
                |> expectFailure [ "unreachable.cs: offset"; "unreachable node" ]
            }
            test
                "node oracle detects interpolation-hole trivia, split-closer trivia, and completeness mismatches" {
                let holeSource = "class C { string s = $\"a { /*c*/ x + 1 /*d*/ } b\"; }"

                let freshTree () =
                    let t = SyntaxTree()
                    Parser.parse holeSource t
                    t

                let holeIdent =
                    let t = freshTree ()

                    [ 0 .. t.TokenCount - 1 ]
                    |> List.find (fun i ->
                        let tok = t.Token i

                        tok.Kind = TokenKind.IdentifierToken
                        && holeSource.Substring(tok.Start, tok.Length) = "x")

                let tree = freshTree ()
                let tok = tree.Token holeIdent
                let badTriviaStart = tree.TriviaCount
                let origTrivia = tree.Trivia tok.TriviaStart

                tree.AddTrivia
                    { origTrivia with
                        Length = origTrivia.Length + 1
                    }
                |> ignore

                for i = 1 to tok.LeadingCount + tok.TrailingCount - 1 do
                    tree.AddTrivia(tree.Trivia(tok.TriviaStart + i)) |> ignore

                tree.SetToken(
                    holeIdent,
                    { tok with
                        TriviaStart = badTriviaStart
                    }
                )

                NodeOracle.checkTree "hole-trivia-content.cs" holeSource tree
                |> expectFailure
                    [
                        "hole-trivia-content.cs: offset"
                        $"token {holeIdent} trailing trivia 0 mismatch"
                    ]

                let tree = freshTree ()
                let tok = tree.Token holeIdent

                tree.SetToken(
                    holeIdent,
                    { tok with
                        TriviaStart = tree.TriviaCount
                    }
                )

                NodeOracle.checkTree "hole-trivia-range.cs" holeSource tree
                |> expectFailure
                    [
                        "hole-trivia-range.cs: offset"
                        $"token {holeIdent} trailing trivia range invalid"
                    ]

                let tree = freshTree ()
                let tok = tree.Token holeIdent
                tree.SetToken(holeIdent, { tok with LeadingCount = 1 })

                NodeOracle.checkTree "hole-leading-count.cs" holeSource tree
                |> expectFailure
                    [
                        "hole-leading-count.cs: offset"
                        $"token {holeIdent} leading trivia 0 mismatch"
                    ]

                let tree = freshTree ()
                let tok = tree.Token holeIdent
                tree.SetToken(holeIdent, { tok with TrailingCount = 0 })

                NodeOracle.checkTree "hole-trailing-count.cs" holeSource tree
                |> expectFailure
                    [
                        "hole-trailing-count.cs: offset"
                        $"token {holeIdent} trailing trivia 0 mismatch"
                    ]

                let holeZeroTrivia = findToken TokenKind.InterpolatedStringTextToken (freshTree ())
                let tree = freshTree ()
                let zeroTok = tree.Token holeZeroTrivia
                tree.SetToken(holeZeroTrivia, { zeroTok with TriviaStart = -1 })

                NodeOracle.checkTree "hole-zero-trivia-range.cs" holeSource tree
                |> expectFailure
                    [
                        "hole-zero-trivia-range.cs: offset"
                        $"token {holeZeroTrivia} leading trivia range invalid"
                    ]

                let splitSource = "class C { List<List<int>> /*a*/ x; }"

                let firstCloser, secondCloser =
                    let t = SyntaxTree()
                    Parser.parse splitSource t

                    let indices =
                        [ 0 .. t.TokenCount - 1 ]
                        |> List.filter (fun i -> (t.Token i).Kind = TokenKind.GreaterThanToken)

                    indices[0], indices[1]

                let splitTree () =
                    let t = SyntaxTree()
                    Parser.parse splitSource t
                    t

                let tree = splitTree ()
                let gt1 = tree.Token firstCloser
                tree.SetToken(firstCloser, { gt1 with TrailingCount = 1 })

                NodeOracle.checkTree "split-first.cs" splitSource tree
                |> expectFailure
                    [ "split-first.cs: offset"; $"token {firstCloser} trailing trivia 0 mismatch" ]

                let tree = splitTree ()
                let gt2 = tree.Token secondCloser
                tree.SetToken(secondCloser, { gt2 with TrailingCount = 0 })

                NodeOracle.checkTree "split-second.cs" splitSource tree
                |> expectFailure
                    [
                        "split-second.cs: offset"
                        $"token {secondCloser} trailing trivia 0 mismatch"
                    ]

                let validSource = "class C {}"
                let tree = SyntaxTree()
                Parser.parse validSource tree
                tree.Recover()

                NodeOracle.checkTree "recovered.cs" validSource tree
                |> expectFailure
                    [
                        "recovered.cs: offset 0"
                        "completeness mismatch"
                        "Roslyn: IsComplete=True"
                        "csff: IsComplete=False"
                    ]

                let skippedSource = "class C {} @@@"
                let skippedTree = oracleTree skippedSource

                NodeOracle.checkTree "skipped.cs" skippedSource skippedTree
                |> expectFailure
                    [
                        "skipped.cs: offset 0"
                        "completeness mismatch"
                        "Roslyn: IsComplete=False"
                        "csff: IsComplete=True"
                    ]
            }
            test "parser emits declarations and its own token stream" {
                let tree = SyntaxTree()
                NodeOracle.check "class.cs" "class C {}" tree |> expectConforms
                Expect.equal tree.NodeCount 2 "CompilationUnit and ClassDeclaration."
                Expect.equal tree.TokenCount 5 "The parser includes EOF."
                Expect.equal tree.LexerBuffer.TokenCount 5 "The lexer still runs independently."
            }
            for title, source in
                [
                    "empty unit", " // comment\r\n"
                    "extern alias", "extern alias X;"
                    "usings",
                    "global using System; using static System.Math; using X = A.B; using Y = global::A.B;"
                    "block namespaces", "namespace A.B { using X; namespace C { class D {} } };"
                    "file namespace", "namespace A.B; using X; class C {}"
                    "types",
                    "public partial class C {} readonly struct S {} interface I {} record R; record class R2; record struct R3; enum E {} delegate void D();"
                    "primary constructors",
                    "class C(int x) : B(x), I {} record R(int X, string Y); struct S(int x) {}"
                    "type parameters",
                    "interface I<out T, in U> {} class C<[A] T> where T : class?, I, new() {}"
                    "constraints",
                    "class C<T, U, V> where T : unmanaged where U : notnull where V : allows ref struct {}"
                    "fields",
                    "class C { int x, y; public const int X = 1; event D E; volatile int z; }"
                    "generic types",
                    "class C { A<B<C<int>>> x; int?[] y; int[,] z; (int x, string y) pair; int* p; }"
                    "methods",
                    "interface I { void M(); T M<T>(ref int x, out T y, in int z, params int[] a) where T : struct; }"
                    "constructors",
                    "class C { public C() : base() {} C(int x) : this() {} ~C() {} }"
                    "properties",
                    "class C { public required int P { get; private set; } int Q { get; init; } = 1; int X => 3; }"
                    "indexers", "interface I { int this[int x] { get; set; } }"
                    "events", "class C { event D E { add {} remove {} } }"
                    "operators",
                    "class C { public static C operator +(C a, C b) {} public static implicit operator int(C c) {} public static explicit operator checked C(int x) {} }"
                    "attributes",
                    "[assembly: A] [module: B] [A(1, Name = \"x\"), B(typeof(C))] class C { [return: A] int M([param: B] int x = 1) {} }"
                    "explicit interface",
                    "class C { int I.P { get; } void I.M() {} int I.this[int x] { get; } }"
                    "contextual names",
                    "class record { int required; int partial; int file; int scoped; int get; }"
                    "scoped parameters",
                    "interface I { void M(scoped ref int x, scoped in int y); }"
                    "file modifier", "file partial class C {}"
                    "ref return", "interface I { ref readonly int M(); }"
                    "enum values", "enum E : byte { [A] X = 1, Y = 2, Z, }"
                    "attribute targets",
                    "[type: A] class C<[typevar: A] T> { [field: A] int x; [property: A] int P { get; } [method: A] void M([param: A] int x) {} [event: A] event D E; }"
                    "nested declarations",
                    "class C { partial class N<T> where T : struct {} enum E { A } delegate int D(int x); interface I {} readonly record struct R(int X); }"
                    "generic explicit interfaces",
                    "class C { void N.I<A<B<int>>>.M<T>() {} int global::N.I<int>.P { get; } event D I<int>.E { add {} remove {} } }"
                    "explicit interface operators",
                    "class C { static C I<C>.operator +(C a, C b) {} static implicit I<C>.operator int(C c) {} }"
                    "ref struct modifiers",
                    "readonly ref partial struct S {} readonly ref struct T {}"
                    "using type aliases",
                    "using unsafe P = int*; using T = (int X, string Y); using A = int[,];"
                    "escaped contextual type names",
                    "class C { @required P; @partial Q; @file R; @scoped S; @async T; }"
                    "fixed buffers", "unsafe struct S { fixed int x[4], y[8]; }"
                    "default parameters",
                    "delegate void D(int x = -1, string y = null, object z = default, int w = default(int));"
                ] do
                test ("declarations: " + title) {
                    NodeOracle.check "declaration.cs" source (SyntaxTree()) |> expectConforms
                }
            for source in
                [
                    "a = b = c"
                    "a += b * c"
                    "a ?? b ?? c"
                    "a ? b : c ? d : e"
                    "a + b * c - d / e % f"
                    "a << b + c >> d >>> e"
                    "a | b ^ c & d == e < f && g || h"
                    "-a + +b + ~c + !d"
                    "++a + b-- + *p + &v"
                    "await F() + 1"
                    "(a)"
                    "(a)b"
                    "(a) => b"
                    "(a, b)"
                    "(A)(b)"
                    "(A<B>)+c"
                    "(A?) + c"
                    "(A*) + c"
                    "(A[])x"
                    "(a)+b"
                    "(a)++"
                    "F(a < b, c > d)"
                    "F(a<b,c>, d)"
                    "F<List<List<int>>>(a)"
                    "a >> b"
                    "a<int> + c"
                    "a<b> + c"
                    "a<b> < c"
                    "nameof(A.B)"
                    "typeof(List<>)"
                    "typeof(Dictionary<,>)"
                    "typeof(List<List<int>>)"
                    "typeof(int[,][])"
                    "default(int)"
                    "sizeof(int)"
                    "checked(a+b)"
                    "unchecked(a*b)"
                    "a.B<C>().D"
                    "p->X"
                    "a?.B.C(x)?[i].D"
                    "a?[x..^1]"
                    "a!.B++"
                    "new C()"
                    "new C { X = 1, Y = { 2,3 }, [k] = v }"
                    "new C { 1, {2,3}, 4 }"
                    "new { a, X = b, c.D }"
                    "new()"
                    "new(1) { X = 2 }"
                    "new int[2,3][]"
                    "new int[,] {{1,2},{3,4}}"
                    "new[] {1,2}"
                    "new[,] {{1,2},{3,4}}"
                    "stackalloc int[4]"
                    "stackalloc int[] {1,2}"
                    "stackalloc[] {1,2}"
                    "[a, ..b, c,]"
                    "x => x + 1"
                    "async x => await F(x)"
                    "static x => x"
                    "() => 1"
                    "(x, y) => x + y"
                    "async (int x, y) => x + y"
                    "int (int x) => x"
                    "static async (int x = 1) => await F(x)"
                    "[A] (x) => x"
                    "delegate {}"
                    "async delegate(int x) {}"
                    "(x: a, y: b)"
                    "x with { P = 2 }"
                    "a + b with { P = c }"
                    "-a with { P = b }"
                    "x switch { 1 => 2, _ => 3 }"
                    "x switch { int y when y > 0 => y, _ => 0 }"
                    "a + b switch { _ => c }"
                    "-a switch { _ => b }"
                    "x is int"
                    "x is A"
                    "x is null"
                    "x as A"
                    "throw new E()"
                    "x ?? throw new E()"
                    "ref a"
                    "..b"
                    "a.."
                    "a..b + c"
                    "a..b..c"
                    "$\"hello {a + b,10:00} !\""
                    "$@\"a {{ { F(1) /*x*/ , -2 :X} }}\""
                    "$$\"\"\"x {{F(a)}} y\"\"\""
                    "$\"{x:}\""
                    "$\"{(a ? b : c)}\""
                    "$\"{new C { X = 1 }}\""
                    "$\"{F($\"{x}\")}\""
                    "\"abc\"u8"
                    "F(x: a = b, out int y, ref z)"
                    "class C { int[] a = { 1,2 }; int[,] b = {{1,2},{3,4}}; }"
                    "typeof(int[ , ])"
                    "typeof(List< /*x*/ >)"
                    "typeof(Dictionary< /*x*/, /*y*/ >)"
                    "class C { int x = F(a < b, c > d); int y = F(a<b,c>, d); }"
                    "(A<B<C>>)x"
                    "(A.B<C>)x"
                    "(a)~b"
                    "(a)^b"
                    "(a)&b"
                    "(a)*b"
                    "(a)[b]"
                    "(A<B<int>>)+c"
                    "x => (y => y)(x)"
                    "async => async"
                    "async (x) => x"
                    "(async) => async"
                    "(a, b) => (a, b)"
                    "$\"{{{x}}}\""
                    "$\"{x, 10}\""
                    "$\"{x/*c*/:00}\""
                    "$\"{ F(1, 2) }\""
                    "$\"{new { a, b }}\""
                    "$$\"\"\"{{{x}}}\"\"\""
                    "new C { P = { X = 1 } }"
                    "class C { int P => a * b + c; [A(Name = 1+2)] int f = a ? b : c; }"
                    "a ? [1] : [2]"
                    "a?[1]:[2]"
                    "a ? [1]"
                    "a?[b] ? c : d"
                    "a ? [b] + c : d"
                    "a?.B ? [x] : [y]"
                    "a ? [b] : c?[d]"
                    "class C { object P => $$\"\"\"\n     x {{F(a)}}\n     y\n     \"\"\"; }"
                    "class C { object P => $\"{ }\"; }"
                    "class C { object P => $\"{x, /*comment*/ 10:X}\"; }"
                    "class C { object P => @$\"a {x} b\"; }"
                    "class C { object P => $\"\"\"{x}\"\"\"; }"
                    "class C { object P => $$$\"\"\"x {{{a + b}}} y\"\"\"; }"
                    "class C { object P => $\"{x // comment\n}\"; }"
                    "class C { object P => $\"\"; }"
                    "class C { int P => (a)!b; int Q => (a)~b; }"
                    "class C { object P => (int)++a; }"
                    "class C { object P => F<A<B<C>>>(x) >> 1; }"
                    "class C { object P => a<List<int>> + c; }"
                    "class C { object P => (A<int>)+c; }"
                    "await(x)"
                    "await (x)"
                    "await + x"
                    "await.F()"
                    "async x => await(x)"
                    "async x => await + x"
                    "async x => y => await(x)"
                    "class C { async Task M() => await(F()); Task N() => await(F()); }"
                    "field"
                    "class C { object x = field; object P => field; object M() => field; object Q { get => field; set => field = value; } }"
                    "global::A.B"
                    "global::A<B>.C"
                    "X::A < b"
                    "typeof(A<B<>>)"
                    "typeof(A<B<,>>)"
                    "F<A<B<>>>()"
                    "a -= b"
                    "a *= b"
                    "a /= b"
                    "a %= b"
                    "a &= b"
                    "a ^= b"
                    "a |= b"
                    "a <<= b"
                    "a >>= b"
                    "a >>>= b"
                    "a ??= b"
                    "a <= b"
                    "a >= b"
                    "a != b"
                    "a<> + c"
                    "a<,> + c"
                    "F<A<>> + c"
                    "(A<>) + c"
                    "a<(T,U)> + c"
                    "((A,B)) + x"
                    "a<(int,int)> + c"
                    "a<A[]> + c"
                    "(A<>)x"
                ] do
                test ("expressions: " + source) {
                    let source =
                        if source.StartsWith("class ", StringComparison.Ordinal) then
                            source
                        else
                            "class C { object P => " + source + "; }"

                    let tree = SyntaxTree()
                    NodeOracle.check "expression.cs" source tree |> expectConforms

                    RoslynOracle.checkBuffer "expression.cs" source tree.LexerBuffer
                    |> expectConforms

                    RoundTrip.checkBuffer "expression.cs" source tree.LexerBuffer |> expectConforms
                    let parsed = TokenBuffer()

                    for index in 0 .. tree.TriviaCount - 1 do
                        let trivia = tree.Trivia index
                        parsed.AddTrivia(trivia.Kind, trivia.Start, trivia.Length)

                    for index in 0 .. tree.TokenCount - 1 do
                        parsed.AddToken(tree.Token index)

                    RoundTrip.checkBuffer "parsed-expression.cs" source parsed |> expectConforms
                }
            for body in
                [
                    "{}"
                    "{ { ; } }"
                    "; ;"
                    "int x;"
                    "int x = 1, y = 2;"
                    "const int x = 1, y = 2;"
                    "var x = F();"
                    "int[] x = { 1, 2 };"
                    "int[,] x = {{1,2},{3,4}};"
                    "A<B<C<int>>> x = new();"
                    "(int X, string Y) x = (1, \"a\");"
                    "int?[] x = null;"
                    "a * b;"
                    "a < b > c;"
                    "a.b * c;"
                    "a.b < c > d;"
                    "a * F(b);"
                    "a < b;"
                    "a = b;"
                    "F(a < b, c > d);"
                    "F<A<B<int>>>(x);"
                    "x++; --x;"
                    "if (a) F();"
                    "if (a) F(); else G();"
                    "if (a) if (b) F(); else G();"
                    "if (a) {} else if (b) {} else {}"
                    "switch (x) {}"
                    "switch (x) { case 1: break; default: return; }"
                    "switch (x) { case 1: case 2: F(); break; case 3: { G(); break; } }"
                    "switch (x) { case X.Y: break; case null: break; case true: break; }"
                    "switch (x) { case int y when y > 0: return; case X when F(): break; }"
                    "switch (x) { case _: break; case int _: break; }"
                    "for (;;) ;"
                    "for (int i = 0, j = 1; i < n; i++, j--) {}"
                    "for (i = 0, j = 1; i < n; i++, F()) F();"
                    "for (var (a,b) = F(); a < n; a++) {}"
                    "foreach (var x in xs) F(x);"
                    "foreach (A<B<int>> x in xs) {}"
                    "foreach (ref readonly var x in xs) {}"
                    "foreach (var (a,b) in xs) {}"
                    "foreach (var (a,(b,_)) in xs) {}"
                    "foreach ((int a, int b) in xs) {}"
                    "foreach ((a,b) in xs) {}"
                    "while (F()) { break; }"
                    "do { continue; } while (a);"
                    "do F(); while (a);"
                    "try {} catch {}"
                    "try {} finally {}"
                    "try { F(); } catch (E) { throw; }"
                    "try {} catch (A e) {} catch (B e) {} finally {}"
                    "try {} catch (E e) when (F(e)) {}"
                    "try {} catch when (F()) {} finally {}"
                    "using (F()) G();"
                    "using (var x = F()) {}"
                    "using (A x = F(), y = G()) {}"
                    "using var x = F();"
                    "using A<B<int>> x = F(), y = G();"
                    "lock (gate) { F(); }"
                    "fixed (int* p = &x) {}"
                    "fixed (char* p = text, q = text) F();"
                    "unsafe { int* p = &x; }"
                    "checked { x++; } unchecked { x--; }"
                    "checked(F()); unchecked(F());"
                    "return;"
                    "return F();"
                    "return ref x;"
                    "break; continue;"
                    "goto label; label: F();"
                    "label: other: ;"
                    "switch(x) { case 1: goto case 2; case 2: goto default; default: break; }"
                    "throw; throw new E();"
                    "yield return F(); yield break;"
                    "yield(); yield = x; int yield = 1;"
                    "@yield(); @yield = x;"
                    "void F() { return; } F();"
                    "int F(int x) => x + 1;"
                    "T F<T>(T x) where T : class => x;"
                    "static int F(int x = 1) { return x; }"
                    "unsafe int* F() => null;"
                    "ref readonly int F() => ref x;"
                    "[A] int F<[B] T>([A] int x) where T : new() => x;"
                    "async Task F() { await G(); } await F();"
                    "async F();"
                    "async async F() => x; static async async G() => x;"
                    "await x; await x = y; await F(); await(x);"
                    "await F() => x; await G() {} await H(int x) => x; await I<T>() => x;"
                    "a < b > c();"
                    "var (a,b) = F();"
                    "var (a,(b,_)) = F();"
                    "var (a, @_) = F();"
                    "(var (a,b), c) = F(); (c, var (a,b)) = F();"
                    "foreach ((var (a,b), c) in xs) {}"
                    "foreach ((int _, int b) in xs) {}"
                    "(int a, int b) = F();"
                    "(int a, (int b, int c)) = F();"
                    "(a, b) = F();"
                    "var(a,b);"
                    "scoped ref readonly int x = ref y;"
                    "scoped var x = F(); scoped int y;"
                    "scoped x;"
                    "ref int x = ref y;"
                    "F(out int x, out var _, ref y);"
                    "Func<int> f = () => { return 1; };"
                    "Action f = delegate { F(); };"
                    "Func<Task> f = async () => { await F(); };"
                ] do
                test ("statements: " + body) {
                    let source = "class C { void M() { " + body + " } }"
                    let tree = SyntaxTree()
                    NodeOracle.check "statement.cs" source tree |> expectConforms

                    RoslynOracle.checkBuffer "statement.cs" source tree.LexerBuffer
                    |> expectConforms

                    RoundTrip.checkBuffer "statement.cs" source tree.LexerBuffer |> expectConforms
                    let parsed = TokenBuffer()

                    for index in 0 .. tree.TriviaCount - 1 do
                        let trivia = tree.Trivia index
                        parsed.AddTrivia(trivia.Kind, trivia.Start, trivia.Length)

                    for index in 0 .. tree.TokenCount - 1 do
                        parsed.AddToken(tree.Token index)

                    RoundTrip.checkBuffer "parsed-statement.cs" source parsed |> expectConforms
                }
            for source in
                [
                    "F();"
                    "var x = 1; if (x > 0) F(); class C {}"
                    "int F(int x) => x; var x = F(1);"
                    "using X.Y; using static X.Y; using A = X.Y; using var a = F(); using X.Y b = F();"
                    "[assembly: A] [A] class C {} [A] int F() => 1; static void G() {}"
                    "await F(); await(F()); await + x;"
                    "await using var x = F(); await using (var y = F()) {}"
                    "await foreach (var x in xs) {}"
                    "await foreach (var (a,b) in xs) {}"
                    "class C { async Task M() { await using var x = F(); await using (F()) {} await foreach (var x in xs) {} } }"
                    "class C { int P { get { return field; } set { field = value; } } }"
                    "class C { int P { get { int F() => field; return F(); } } }"
                    "class C { async Task M() { Task F() { return await(x); } async Task G() { return await(x); } } }"
                    "class C { async Task M() { await x; await F(); await x = y; } }"
                    "class C { async Task M() { return (await x, await y); } }"
                    "class C { void M() { F((await x, await y)); } }"
                    "class C { event D E { add { F(); } remove { G(); } } C() { F(); } ~C() { G(); } }"
                ] do
                test ("statement contexts: " + source) {
                    NodeOracle.check "context.cs" source (SyntaxTree()) |> expectConforms
                }
            test "yield promotion belongs only to yield statements" {
                let source =
                    "class C { void M() { yield return x; yield break; yield(); yield = x; int yield; @yield(); } }"

                let tree = SyntaxTree()
                NodeOracle.check "yield.cs" source tree |> expectConforms

                let count kind tokens =
                    tokens |> Array.filter (fun (token: Token) -> token.Kind = kind) |> Array.length

                Expect.equal
                    (count TokenKind.YieldKeyword (tree.TokenSpan().ToArray()))
                    2
                    "Only the two statements promote yield."

                Expect.equal
                    (count TokenKind.YieldKeyword (tree.LexerBuffer.TokenSpan().ToArray()))
                    0
                    "Lexical identifiers retain their original kinds."
            }
            test "truncated statements and unsupported patterns and queries make progress" {
                let tree = SyntaxTree()

                for body in
                    [
                        "if (x) { F(); } else { G(); }"
                        "for (int i = 0; i < n; i++) { F(); }"
                        "foreach (var (a,(b,_)) in xs) { F(); }"
                        "try { F(); } catch (E e) when (F(e)) {} finally {}"
                        "switch (x) { case 1: case 2: break; default: return; }"
                        "await using var x = F(); yield return x;"
                        "[A] static int F<T>(T x) where T : class { return 1; }"
                        "if (x is { P: [1, ..var tail] }) F();"
                        "var xs = from x in items where x > 0 select x;"
                        "switch (x) { case { P: [1, ..] }: F(); break; }"
                    ] do
                    let source = "class C { void M() { " + body + " } int x; } class D {}"

                    for length in 0 .. source.Length do
                        let fragment = source.Substring(0, length)
                        Parser.parse fragment tree

                        RoundTrip.checkBuffer "fragment.cs" fragment tree.LexerBuffer
                        |> expectConforms

                        let parsed = TokenBuffer()

                        for index in 0 .. tree.TriviaCount - 1 do
                            let trivia = tree.Trivia index
                            parsed.AddTrivia(trivia.Kind, trivia.Start, trivia.Length)

                        for index in 0 .. tree.TokenCount - 1 do
                            parsed.AddToken(tree.Token index)

                        RoundTrip.checkBuffer "parsed-fragment.cs" fragment parsed |> expectConforms
            }
            test "pointer argument certainty follows the final name segment at every depth" {
                for certain, shapes in
                    [
                        true,
                        [
                            "int"
                            "int*"
                            "int**"
                            "int?"
                            "int?*"
                            "B[]"
                            "B[,]"
                            "B[][]"
                            "B?"
                            "B?*"
                            "B[]*"
                            "B*[]"
                            "B*[]*"
                            "G<int>[]"
                            "delegate*<B,C>"
                            "G<int>*"
                            "G<int>**"
                            "G<G<B>>*"
                            "G<G<G<B>>>*"
                            "G<G<int>>*"
                            "G<G<int>.H<B>>*"
                            "G<G<int>.H<B>,int>*"
                        ]
                        false,
                        [
                            "B"
                            "G<int>"
                            "G<B>"
                            "N.B"
                            "(B,C)"
                            "G<int*>"
                            "G<B*>"
                            "B*"
                            "B**"
                            "G<B>*"
                            "N.B*"
                            "(B,C)*"
                            "B.C*"
                            "G<int>.H*"
                            "(int,B)*"
                            "G<(int,B)>*"
                            "G<int>.H<B>*"
                            "(G<int>,B)*"
                            "G<(B,C)>*"
                            "G<G<int>.H>*"
                        ]
                    ] do
                    for shape in shapes do
                        let source =
                            $"class C {{ unsafe void M(int b) {{ var v = A<{shape}> + b; }} }}"

                        let root = CSharpSyntaxTree.ParseText(source).GetRoot()

                        let roslyn =
                            root.DescendantNodes()
                            |> Seq.exists (function
                                | :? GenericNameSyntax as node -> node.Identifier.ValueText = "A"
                                | _ -> false)

                        Expect.equal roslyn certain $"Roslyn settles A<{shape}> before +."
                        let tree = SyntaxTree()
                        Parser.parse source tree

                        let actual =
                            seq { 0 .. tree.NodeCount - 1 }
                            |> Seq.exists (fun index ->
                                let node = tree.Node index

                                if node.Kind <> NodeKind.GenericName then
                                    false
                                else
                                    let token = tree.Token node.TokenStart
                                    source.Substring(token.Start, token.Length) = "A")

                        Expect.equal actual roslyn $"Type-argument certainty for {shape}."

                        expectSourceConforms
                            "cast.cs"
                            $"class C {{ unsafe void M(int b) {{ var v = ({shape}) b; }} }}"
            }
            test "pointer argument certainty agrees across nested qualifiers and aliases" {
                let seeds =
                    [ "B"; "int"; "B*"; "int*"; "B[]"; "B?"; "(B,C)"; "(int,B)"; "G<B>"; "G<int>" ]

                let wrap shape =
                    [
                        shape + "*"
                        "G<" + shape + ">"
                        "G<" + shape + ">*"
                        "G<" + shape + ">.H*"
                        "G<" + shape + ">.H<B>*"
                        "N::G<" + shape + ">*"
                        "G<N::G<" + shape + ">>*"
                    ]

                let shapes =
                    seeds
                    @ (seeds |> List.collect wrap)
                    @ (seeds |> List.collect wrap |> List.collect wrap)
                    |> List.distinct

                Expect.equal
                    shapes.Length
                    514
                    "The generated campaign covers two levels of each wrapper."

                for shape in shapes do
                    let source = $"class C {{ unsafe void M(int b) {{ var v = A<{shape}> + b; }} }}"
                    let root = CSharpSyntaxTree.ParseText(source).GetRoot()

                    let expected =
                        root.DescendantNodes()
                        |> Seq.exists (function
                            | :? GenericNameSyntax as node -> node.Identifier.ValueText = "A"
                            | _ -> false)

                    let tree = SyntaxTree()
                    Parser.parse source tree

                    let actual =
                        seq { 0 .. tree.NodeCount - 1 }
                        |> Seq.exists (fun index ->
                            let node = tree.Node index

                            if node.Kind <> NodeKind.GenericName then
                                false
                            else
                                let token = tree.Token node.TokenStart
                                source.Substring(token.Start, token.Length) = "A")

                    Expect.equal actual expected $"Roslyn's type-argument decision for {shape}."
            }
            test "generic lookahead splits only confirmed type argument closers" {
                let source = "class C { object P => F<A<B<int>>>(a < b, c > d) >> 1; }"
                let tree = SyntaxTree()
                NodeOracle.check "generic.cs" source tree |> expectConforms

                let count kind tokens =
                    tokens |> Seq.filter (fun (token: Token) -> token.Kind = kind) |> Seq.length

                let lexical = tree.LexerBuffer.TokenSpan().ToArray()
                let parsed = tree.TokenSpan().ToArray()

                Expect.equal
                    (count TokenKind.GreaterThanGreaterThanGreaterThanToken lexical)
                    1
                    "The lexer joins the three generic closers."

                Expect.equal
                    (count TokenKind.GreaterThanGreaterThanGreaterThanToken parsed)
                    0
                    "The parser splits all three type closers."

                Expect.equal
                    (count TokenKind.GreaterThanGreaterThanToken parsed)
                    1
                    "The shift operator remains joined."

                Expect.equal
                    (count TokenKind.GreaterThanToken parsed)
                    4
                    "Three type closers and the comparison."
            }
            test "a > run that ends in = closes a list, and the >= it ends with closes none" {
                let count kind tokens =
                    tokens |> Seq.filter (fun (token: Token) -> token.Kind = kind) |> Seq.length

                for source, closers, equals, shift, unsigned in
                    [
                        "class C { void M() { A<B>>=1; } }", 1, 1, 0, 0
                        "class C { void M() { A<B<C>>=1; } }", 1, 1, 0, 0
                        "class C { void M() { A<B<C>>>=1; } }", 2, 1, 0, 0
                        "class C { void M() { A<B<C<D>>>=1; } }", 2, 1, 0, 0
                        "class C { void M() { A<B,C>>=1; } }", 1, 1, 0, 0
                        "class C { void M() { var v = new X { A<B<C>>=1 }; } }", 1, 1, 0, 0
                        "class C { void M() { var v = new X { A<B<C>>>=1 }; } }", 2, 1, 0, 0
                        "class C { void M(int a) { a >>= 1; } }", 0, 0, 1, 0
                        "class C { void M(int a) { a >>>= 1; } }", 0, 0, 0, 1
                        "class C { void M(int a) { a >>= a >> 1; } }", 0, 0, 1, 0
                        "class C { void M() { A<B>>>=1; } }", 0, 0, 0, 1
                        "class C { void M() { A<B>=1; } }", 0, 1, 0, 0
                        "class C { void M() { A<B<C>> x; } }", 2, 0, 0, 0
                    ] do
                    let tree = SyntaxTree()
                    NodeOracle.check "run.cs" source tree |> expectConforms
                    let parsed = tree.TokenSpan().ToArray()

                    Expect.equal
                        (count TokenKind.GreaterThanToken parsed)
                        closers
                        $"Closers cut out of the run: {source}"

                    Expect.equal
                        (count TokenKind.GreaterThanEqualsToken parsed)
                        equals
                        $"The >= C# lexes last: {source}"

                    Expect.equal
                        (count TokenKind.GreaterThanGreaterThanEqualsToken parsed)
                        shift
                        $"Runs left whole as >>=: {source}"

                    Expect.equal
                        (count TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken parsed)
                        unsigned
                        $"Runs left whole as >>>=: {source}"
            }
            test "an initializer element holding a shift-assignment run is read as C# reads it" {
                let source = "class C { void M() { var v = new X{X<Y<Z>>=() => {return 1;}}; } }"
                let tree = SyntaxTree()
                Parser.parse source tree

                let kinds =
                    seq { 0 .. tree.NodeCount - 1 }
                    |> Seq.map (fun index -> (tree.Node index).Kind)
                    |> Set.ofSeq

                Expect.isTrue
                    (kinds.Contains NodeKind.GreaterThanOrEqualExpression)
                    "The element compares the generic name against the parenthesised term."

                Expect.isTrue (kinds.Contains NodeKind.GenericName) "The run's first > closes Y<Z>."

                Expect.isFalse
                    (kinds.Contains NodeKind.RightShiftAssignmentExpression)
                    "The run is not an operator here: C# spends its first > on a closer."

                Expect.isFalse
                    (kinds.Contains NodeKind.ParenthesizedLambdaExpression)
                    "Nothing assigns a lambda, so the arrow belongs to no parameter list."
            }
            test "parser token gap preserves lookahead across relocation and growth" {
                let input = TokenInput()
                let expected = ResizeArray<Token>()

                let token index =
                    {
                        Kind = TokenKind.IdentifierToken
                        Start = index
                        Length = 1
                        TriviaStart = index
                        LeadingCount = 1
                        TrailingCount = 2
                    }

                for index = 0 to 2046 do
                    input.Add(token index)
                    expected.Add(token index)

                for index in [ 1000; 1001; 0; -1; 500; 501; -1 ] do
                    let item = token (expected.Count + 1000)

                    if index < 0 then
                        input.Add item
                        expected.Add item
                    else
                        input.Insert(index, item)
                        expected.Insert(index, item)

                    Expect.equal input.Count expected.Count "Logical length includes each edit."

                    for cursor = 0 to expected.Count - 1 do
                        Expect.equal input[cursor] expected[cursor] "All token fields survive."

                input[1500] <- token 9999
                Expect.equal input[1500] (token 9999) "Logical replacement crosses the gap."
                input.Clear()
                Expect.equal input.Count 0 "Reset drops the previous file."
                Expect.equal input.CopiedTokenCount 0L "Reset drops the previous work count."
                input.Add(token 1)
                Expect.equal input[0] (token 1) "Retained storage starts a new stream."
            }
            for family, statement in
                [
                    "generic closers", "_ = typeof(G<G<int>>);\n"
                    "independent interpolations", "_ = $\"{x}\";\n"
                ] do
                test ($"parse-only token movement stays linear / {family}") {
                    let measure count =
                        let source =
                            "class G<T> {} class C { void M(int x) {\n"
                            + String.replicate count statement
                            + "} }"

                        let tree = SyntaxTree()

                        let prepare () =
                            tree.Reset()
                            Lexer.lex source tree.LexerBuffer

                        for _ = 1 to 3 do
                            prepare ()
                            Parser.parseLexed source tree

                        prepare ()
                        let before = GC.GetAllocatedBytesForCurrentThread()
                        Parser.parseLexed source tree
                        let bytes = GC.GetAllocatedBytesForCurrentThread() - before
                        let copies = tree.InputTokenCopyCount

                        printfn "%s n=%d: %d input copies, %d bytes" family count copies bytes

                        Expect.isLessThan
                            copies
                            (6L * int64 tree.TokenCount)
                            "Token preparation and splitting must move bounded work per token."

                        struct (copies, bytes)

                    let struct (smallCopies, smallBytes) = measure 1024
                    let struct (largeCopies, largeBytes) = measure 8192

                    Expect.isLessThan
                        largeCopies
                        (10L * smallCopies)
                        "Eight times as many statements must not shift every file suffix."

                    Expect.isLessThanOrEqual
                        largeBytes
                        (12L * smallBytes)
                        "Parse-only allocation must grow with the statements."
                }
            test "parentheses choose lambda, cast, tuple, and expression without orphan nodes" {
                let source =
                    "class C { object A => (a); object B => (a)b; object Cc => (a) => b; object D => (a, b); object E => (A)(b); }"

                let tree = SyntaxTree()
                NodeOracle.check "parentheses.cs" source tree |> expectConforms

                let count kind =
                    tree.NodeSpan().ToArray()
                    |> Array.filter (fun node -> node.Kind = kind)
                    |> Array.length

                Expect.equal (count NodeKind.CastExpression) 2 "Both forms of cast."

                Expect.equal
                    (count NodeKind.ParenthesizedExpression)
                    2
                    "The standalone expression and the cast operand."

                Expect.equal
                    (count NodeKind.ParenthesizedLambdaExpression)
                    1
                    "The arrow selects a lambda."

                Expect.equal (count NodeKind.TupleExpression) 1 "The comma selects a tuple."
            }
            for family, opening, closing, kind in
                [
                    "calls", "F(", ")", NodeKind.InvocationExpression
                    "parentheses", "(", ")", NodeKind.ParenthesizedExpression
                    "collections", "[", "]", NodeKind.CollectionExpression
                ] do
                test ($"lambda delimiter discovery stays linear / {family}") {
                    let tree = SyntaxTree()

                    for suffix in [ ";}"; ";object N()=>(int y)=>y;}" ] do
                        let visits = ResizeArray<int>()

                        for depth in [ 16; 32; 64; 128; 256 ] do
                            let source =
                                "class C{object M()=>"
                                + String.replicate depth opening
                                + "x"
                                + String.replicate depth closing
                                + suffix

                            Parser.parse source tree
                            let before = GC.GetAllocatedBytesForCurrentThread()
                            Parser.parse source tree
                            let bytes = GC.GetAllocatedBytesForCurrentThread() - before
                            visits.Add tree.LambdaBalanceVisits

                            printfn
                                "lambda delimiters %s d=%d visits=%d tokens=%d bytes=%d"
                                family
                                depth
                                tree.LambdaBalanceVisits
                                tree.LexerBuffer.TokenCount
                                bytes

                            Expect.equal
                                (seq { 0 .. tree.NodeCount - 1 }
                                 |> Seq.filter (fun index -> (tree.Node index).Kind = kind)
                                 |> Seq.length)
                                depth
                                "Lookahead preserves every nested expression."

                            Expect.isLessThanOrEqual
                                tree.LambdaBalanceVisits
                                tree.LexerBuffer.TokenCount
                                "Each token is inspected at most once for delimiter discovery."

                        if visits[0] = 0 then
                            Expect.equal
                                visits[visits.Count - 1]
                                0
                                "Arrow-bound fast exit skips delimiter discovery when no lambda arrow follows."
                        else
                            Expect.isLessThan
                                visits[visits.Count - 1]
                                (18 * visits[0])
                                "Sixteen times the nesting needs only linear delimiter discovery."
                }
            test "lambda delimiter cache reset stays bounded after a large file" {
                let tree = SyntaxTree()
                let large = "class C{void M(){" + String.replicate 8192 "F(x);" + "}}"
                let small = "class C{void M(){F(x);}}"
                Parser.parse large tree
                Parser.parse small tree

                for _ = 1 to 32 do
                    Parser.parse small tree

                    Expect.isLessThanOrEqual
                        tree.LambdaDelimiterResetWork
                        (32 * tree.LexerBuffer.TokenCount)
                        "Retained cache capacity must follow the files being parsed."
            }
            testSequenced
            <| test "reading ahead over types and lambda heads allocates nothing" {
                let tree = SyntaxTree()
                let calls = 2048

                let source =
                    "class C{void M(){"
                    + String.replicate calls "a.b.c(x);G<A<B<int>>> g=d.e<f>(y);"
                    + "}}"

                Parser.parse source tree
                Parser.parse source tree

                let samples =
                    Array.init 5 (fun _ ->
                        let before = GC.GetAllocatedBytesForCurrentThread()
                        Parser.parse source tree
                        GC.GetAllocatedBytesForCurrentThread() - before)

                let bytes = Array.min samples
                printfn "lookahead allocation: %d calls, samples=%A bytes" calls samples

                Expect.isGreaterThan
                    tree.NodeCount
                    calls
                    "The file must be large enough for the lookahead to dominate."

                Expect.isLessThan
                    bytes
                    (int64 calls)
                    $"Type and lambda-head lookahead must not allocate per scan. Warmed bytes: %A{samples}."
            }
            test "lambda delimiter endpoints survive generic splitting and interpolation expansion" {
                let tree = SyntaxTree()

                for source in
                    [
                        "class C{void M(){F(G<A<B<int>>>(x),F((x)),F([x]),F($\"{F(x)}\"));F((x));}}"
                        "class C{object M()=>F(G<A<B<int>>>(F((x))),F($\"{F(G<A<B<int>>>(F(x)))}\"));}"
                        "class C{void M(){var s=$\"{F(G<A<B<int>>>(x))}\";F((x),[x],$\"{F(x)}\");}}"
                        "class C{void M(){var f=[A(typeof(G<G<int>>))] static async G<G<int>> (G<G<int>> x)=>F($\"{F(x)}\");}}"
                        "class C{void M(){F(G<G<int>>(x),[A] (int x)=>x,static async (int x)=>x);}}"
                        "class C{object M()=>F((G<G<int>>)x,(x,x),int (int x)=>x);}"
                        "class C{void M(){F($\"{F($\"{G<G<int>>(x)}\")}\",F((x)));}}"
                    ] do
                    NodeOracle.check "lambda-delimiters.cs" source tree |> expectConforms

                    RoslynOracle.checkBuffer "lambda-delimiters.cs" source tree.LexerBuffer
                    |> expectConforms

                    RoundTrip.checkBuffer "lambda-delimiters.cs" source tree.LexerBuffer
                    |> expectConforms

                Parser.parse "class C{}" tree
                Expect.equal tree.LambdaBalanceVisits 0 "Reset drops delimiter discovery state."
            }
            test "interpolation re-lexing preserves parser trivia and reusable lexical storage" {
                let source =
                    " // lead\nclass C { object P => $\"text { /*hole*/ F(x), 10:X} tail\"; } // end\n"

                let tree = SyntaxTree()
                NodeOracle.check "interpolation.cs" source tree |> expectConforms

                let root =
                    CSharpSyntaxTree
                        .ParseText(source, CSharpParseOptions(LanguageVersion.Preview))
                        .GetRoot()

                let expected = root.DescendantTokens() |> Seq.toArray
                Expect.equal tree.TokenCount expected.Length "All hole tokens are present."

                for index in 0 .. tree.TokenCount - 1 do
                    let token = tree.Token index

                    let expectedTrivia =
                        Seq.append expected[index].LeadingTrivia expected[index].TrailingTrivia
                        |> Seq.toArray

                    Expect.equal
                        (token.LeadingCount, token.TrailingCount)
                        (expected[index].LeadingTrivia.Count, expected[index].TrailingTrivia.Count)
                        "Trivia attaches to the same token."

                    for offset in 0 .. expectedTrivia.Length - 1 do
                        let trivia = tree.Trivia(token.TriviaStart + offset)

                        Expect.equal
                            (int trivia.Kind, trivia.Start, trivia.Length)
                            (expectedTrivia[offset].RawKind,
                             expectedTrivia[offset].FullSpan.Start,
                             expectedTrivia[offset].FullSpan.Length)
                            "Hole trivia retains its source coordinates."

                Expect.isGreaterThan
                    tree.TriviaCount
                    tree.LexerBuffer.TriviaCount
                    "Hole trivia belongs only to parser storage."

                NodeOracle.check "next.cs" "class C {}" tree |> expectConforms

                Expect.equal
                    tree.TriviaCount
                    tree.LexerBuffer.TriviaCount
                    "Reset drops interpolation trivia."
            }
            test "mixed leading interpolation comments preserve later holes" {
                for prefix, suffix, width in
                    [ "$\"", "\"", 1; "$@\"", "\"", 1; "$$\"\"\"", "\"\"\"", 2 ] do
                    let opening = String('{', width)
                    let closing = String('}', width)

                    let source =
                        "class C { object P => "
                        + prefix
                        + opening
                        + "/*c*//**d*/#if false\nx"
                        + closing
                        + " tail "
                        + opening
                        + "x"
                        + closing
                        + suffix
                        + "; }"

                    let tree = SyntaxTree()
                    Parser.parse source tree
                    let start = source.LastIndexOf(opening + "x", StringComparison.Ordinal)

                    let tokens =
                        tree.TokenSpan().ToArray()
                        |> Array.filter (fun token ->
                            token.Start >= start && token.Start < start + width * 2 + 1)
                        |> Array.map (fun token -> token.Kind, token.Start, token.Length)

                    Expect.equal
                        tokens
                        [|
                            TokenKind.OpenBraceToken, start, width
                            TokenKind.IdentifierToken, start + width, 1
                            TokenKind.CloseBraceToken, start + width + 1, width
                        |]
                        "The malformed directive cannot swallow the following hole."
            }
            test "interpolation recovery retains every source character" {
                for expression in
                    [
                        "$\"{ #if false\n/*\n#endif\nz }\""
                        "$\" { x \n /* } \""
                        "$\"hello abc\n"
                        "$$\"\"\"hello {{x}}"
                        "$\"\"\"{{x} {\"a\"}\"\"\""
                        "$\"\"\" } {\"a\"} \"\"\""
                        "$\"{ \"x\""
                        "$\"\"\"{{x} tail"
                    ] do
                    let source = "class C { string M() => " + expression + "; }"
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    let ranges = ResizeArray<struct (int * int)>()

                    for i = 0 to tree.TokenCount - 1 do
                        let token = tree.Token i

                        if token.Length > 0 then
                            ranges.Add(struct (token.Start, token.Length))

                        for j = token.TriviaStart to token.TriviaStart
                                                     + token.LeadingCount
                                                     + token.TrailingCount
                                                     - 1 do
                            let trivia = tree.Trivia j

                            if trivia.Length > 0 then
                                ranges.Add(struct (trivia.Start, trivia.Length))

                    let ordered = ranges.ToArray() |> Array.sortBy (fun struct (start, _) -> start)
                    let mutable position = 0

                    for struct (start, length) in ordered do
                        Expect.equal
                            start
                            position
                            "Parser tokens and owned trivia form an exact partition."

                        position <- start + length

                    Expect.equal position source.Length "No EOF trivia or literal tail is lost."
                    RoundTrip.checkBuffer "recovery.cs" source tree.LexerBuffer |> expectConforms
            }
            test "interpolation boundary recovery matches Roslyn" {
                for expression in
                    [
                        "$\" { x \n /* } \""
                        "$\"\"\"\nhello\n{x}\"\"\""
                        "$\"\"\"\nhello\nworld\"\"\""
                        "$\"hello abc\n"
                        "$$\"\"\"hello {{x}}"
                        "$$\"\"\"{{x:}00}}\"\"\""
                        "$\"\"\"{x:\"}\"\"\""
                        "$$\"\"\"{{x:\"}}\"\"\""
                        "$\"\"\"{{x} {\"a\"}\"\"\""
                        "$\"\"\" } {\"a\"} \"\"\""
                    ] do
                    expectSourceConforms
                        "boundary.cs"
                        ("class C { string M() => " + expression + "; }")
            }
            testSequenced
            <| test "flat interpolation allocation grows with holes rather than suffixes" {
                let allocated source =
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    Parser.parse source tree

                    Array.init 5 (fun _ ->
                        let before = GC.GetAllocatedBytesForCurrentThread()
                        Parser.parse source tree
                        GC.GetAllocatedBytesForCurrentThread() - before)

                for raw in [ false; true ] do
                    let hole, prefix, suffix =
                        if raw then
                            "{{x}}", "$$\"\"\"", "\"\"\""
                        else
                            "{x}", "$\"", "\""

                    let source count text =
                        "class C { string M(int x) => "
                        + prefix
                        + String.concat text (Array.create count hole)
                        + suffix
                        + "; }"

                    let small = allocated (source 128 "")
                    let large = allocated (source 1024 "")

                    Expect.isLessThanOrEqual
                        (Array.min large)
                        (12L * Array.min small)
                        $"Eight times the holes stays linear (raw={raw}). Warmed bytes: 128=%A{small}; 1024=%A{large}."

                    let shortText = allocated (source 8 (String('a', 128)))
                    let longText = allocated (source 8 (String('a', 1024)))

                    Expect.isLessThanOrEqual
                        (Array.min longText)
                        (2L * Array.min shortText)
                        $"Literal text is never copied into the hole lexer (raw={raw}). Warmed bytes: short=%A{shortText}; long=%A{longText}."
            }
            test "truncated expressions and interpolations always make progress" {
                let tree = SyntaxTree()

                for expression in
                    [
                        "F<A<B<int>>>(a < b, c > d)"
                        "(int x, int y) => new C { X = x + y }"
                        "new int[2,3][] { }"
                        "a ? [1, ..b] : []"
                        "$\"a {F(x),10:X} b\""
                        "$$\"\"\"x {{a + b}} y\"\"\""
                    ] do
                    let source = "class C { object P => " + expression + "; } class D {}"

                    for length in 0 .. source.Length do
                        let fragment = source.Substring(0, length)
                        Parser.parse fragment tree

                        RoundTrip.checkBuffer "fragment.cs" fragment tree.LexerBuffer
                        |> expectConforms
            }
            for source in
                [
                    "unsafe class C { bool a; byte b; sbyte c; short d; ushort e; int f; uint g; long h; ulong i; float j; double k; decimal l; char m; string n; object o; void M() {} }"
                    "unsafe class C { global::N.G<A.B<int?>[,], C*[]>[][] x; int*[][,] y; (int X, (string, bool) Y)?[,] z; }"
                    "using unsafe P = delegate*<void>; using T = (int X, string Y); using A = int[,,][];"
                    "unsafe class C { delegate*<int, void> p; delegate* managed<int, int> q; delegate* unmanaged[Cdecl, Stdcall]<in int, ref readonly int, out int, void> r; }"
                    "unsafe class C { G<delegate*<G<int>, G<G<int>>>> p; void M() { delegate*<int, void> f; var x = (delegate*<int, void>)p; } }"
                    "class C { ref readonly int M() => ref x; void N(scoped ref int x, scoped in int y, out int z) { scoped ref readonly int a = ref x; scoped Span<int> b = default; z = 0; } }"
                    "class C { object P => new (string Name, Action<int> Run)[] { (\"a\", x => F(x)) }; object Q => new (int, int)[2,3][]; }"
                    "class C { object P => new(a, b) {}; object Q => new (int, int)(1, 2); }"
                    "class C { object P => (G<T>)[1, 2]; object Q => (T)[1]; object R => new (int, int)?[count]; }"
                    "public union U<T>(A, N.B<T>, (int X, int Y), int[]) where T : class;"
                    "public static class E { extension<T>(ref T x) where T : class { public int P => 1; public void M() {} } extension(int[] x) { public int N() => x.Length; } }"
                ] do
                test ("types and preview declarations: " + source) {
                    let tree = SyntaxTree()
                    NodeOracle.check "types.cs" source tree |> expectConforms
                    RoslynOracle.checkBuffer "types.cs" source tree.LexerBuffer |> expectConforms
                    RoundTrip.checkBuffer "types.cs" source tree.LexerBuffer |> expectConforms
                }
            for pattern in
                [
                    "null"
                    "42"
                    "-1"
                    "int value"
                    "T<int> value"
                    "global::N.T<int[]> value"
                    "var value"
                    "var _"
                    "var (a, (b, c))"
                    "_"
                    "int"
                    "T<int>"
                    "A.B<int[]>"
                    "int[]"
                    "not null"
                    "not not null"
                    ">= 1 and < 10 or 42"
                    "T and not null or int"
                    "(not null)"
                    "(int)"
                    "(1)"
                    "((1))"
                    "(A | B)"
                    "(1) + 2"
                    "((1) + 2) * 3"
                    "(C.Value + 1)"
                    "(a ? 1 : 2)"
                    "(int x, string y)"
                    "(1, 2) pair"
                    "(1) pair"
                    "(X: 1, Y: var y)"
                    "T()"
                    "T(1, var y) { Z: not null } value"
                    "{}"
                    "{ X: 1, Y: { Z: > 0 }, A.B: var b }"
                    "[]"
                    "[1, > 0, ..]"
                    "[_, ..var rest] all"
                    "[1, .. [2, 3]]"
                    "@not"
                    "@and"
                ] do
                test ("patterns: " + pattern) {
                    let source =
                        "class C { object M(object x) => x switch { "
                        + pattern
                        + " => 1, _ => 0 }; }"

                    let tree = SyntaxTree()
                    NodeOracle.check "pattern.cs" source tree |> expectConforms
                    RoslynOracle.checkBuffer "pattern.cs" source tree.LexerBuffer |> expectConforms
                    RoundTrip.checkBuffer "pattern.cs" source tree.LexerBuffer |> expectConforms
                }
            for expression in
                [
                    "x is T"
                    "x is A.B<int>"
                    "x is int?"
                    "x is int? y"
                    "x is T ? a : b"
                    "x is int ? F(a, b) : c"
                    "x is A.B or C.D ? 2 : 1"
                    "x is not null && y != null"
                    "x is null == y is null"
                    "x is int and > 0 or string"
                    "x is (int, string)"
                    "x is (A | B)"
                    "x switch { _ when F() => (a, b), _ => (c, d) }"
                    "x switch { _ when F((int x) => true) => 1, _ => 0 }"
                    "x switch { A | B => 1, A == B => 2, A ?? B => 3, _ => 0 }"
                    "(x ? a : b, y ? c : d)"
                ] do
                test ("pattern expression boundaries: " + expression) {
                    NodeOracle.check
                        "boundaries.cs"
                        ("class C { object P => " + expression + "; }")
                        (SyntaxTree())
                    |> expectConforms
                }
            for query in
                [
                    "from x in xs select x"
                    "from int x in xs select x"
                    "from x in xs where x is T select x"
                    "from x in xs select x is T into y select y"
                    "from x in xs orderby x is T descending select x"
                    "from x in xs join y in ys on x is T equals y is T select x"
                    "from N.G<int[]> x in xs select x"
                    "from x in xs from y in ys let z = x + y where z > 0 select z"
                    "from x in xs join y in ys on x.Id equals y.Id select new { x, y }"
                    "from x in xs join int y in ys on x equals y into matches from z in matches select z"
                    "from x in xs orderby x.A, x.B ascending, x.C descending select x"
                    "from x in xs group x.Value by x.Key"
                    "from x in xs select x into y where y > 0 select y into z group z by z"
                    "from x in (from y in ys select y) select x"
                    "from x in xs select from y in ys select x + y"
                    "from @select in xs let @where = @select where @where > 0 select @where"
                    "from x in xs select x.@select(@from, @select, @where, @join, @orderby, @ascending, @descending, @group, @by, @on, @equals, @into)"
                ] do
                test ("queries: " + query) {
                    let source = "class C { object P => " + query + "; }"
                    let tree = SyntaxTree()
                    NodeOracle.check "query.cs" source tree |> expectConforms
                    RoslynOracle.checkBuffer "query.cs" source tree.LexerBuffer |> expectConforms
                    RoundTrip.checkBuffer "query.cs" source tree.LexerBuffer |> expectConforms
                }
            test "query and pattern words remain identifiers outside their grammars" {
                let source =
                    "class C { object M() { var from = select + where + join + on + equals + into + orderby + ascending + descending + group + by + let + and + or + not; return from; } }"

                NodeOracle.check "context.cs" source (SyntaxTree()) |> expectConforms
            }
            test "tuple switch conditions preserve their own parentheses" {
                let source =
                    "class C { void M() { switch (a, b) { case (1, 2): break; } switch ((a, b)) { default: break; } switch (F<A,B>()) { case _: break; } } }"

                NodeOracle.check "tuple-switch.cs" source (SyntaxTree()) |> expectConforms
            }
            test "truncated types patterns and queries always make progress" {
                let tree = SyntaxTree()

                for source in
                    [
                        "unsafe class C { delegate* unmanaged[Cdecl]<ref int, void> p; }"
                        "class C { bool M(object x) => x is T(1, var y) { A.B: [1, ..var rest] } value and not null; }"
                        "class C { object P => from x in xs join y in ys on x equals y into z orderby x descending select z into q group q by q; }"
                        "public union U(A, G<B<int>>, (int, int)); static class E { extension<T>(T x) { int P => 1; } }"
                    ] do
                    for length in 0 .. source.Length do
                        let fragment = source.Substring(0, length)
                        Parser.parse fragment tree

                        RoundTrip.checkBuffer "fragment.cs" fragment tree.LexerBuffer
                        |> expectConforms
            }
            test "parsing reuses storage without mutating lexical tokens or trivia" {
                let tree = SyntaxTree()

                let source =
                    " // lead\r\nrecord R { A<B<int /* inner */>> /* outer */ P { get; init; } int[,] x; } // tail\r\n"

                NodeOracle.check "record.cs" source tree |> expectConforms
                RoslynOracle.checkBuffer "record.cs" source tree.LexerBuffer |> expectConforms
                RoundTrip.checkBuffer "record.cs" source tree.LexerBuffer |> expectConforms
                let parsed = TokenBuffer()

                for index in 0 .. tree.TriviaCount - 1 do
                    let trivia = tree.Trivia index
                    parsed.AddTrivia(trivia.Kind, trivia.Start, trivia.Length)

                for index in 0 .. tree.TokenCount - 1 do
                    parsed.AddToken(tree.Token index)

                RoundTrip.checkBuffer "parsed.cs" source parsed |> expectConforms
                NodeOracle.check "next.cs" "class C {}" tree |> expectConforms
            }
            test "statement bodies preserve following declarations" {
                let tree = SyntaxTree()

                let source =
                    "[A(1 << 2, typeof(C), new[] { 1, 2 })] class C { int x = F(1 + 2, 3); void M() { while (true) { M(); } } int y; } class D {}"

                Parser.parse source tree
                let kinds = [ for index in 0 .. tree.NodeCount - 1 -> (tree.Node index).Kind ]

                Expect.equal
                    (kinds |> List.filter ((=) NodeKind.ClassDeclaration) |> List.length)
                    2
                    "Both classes survive."

                Expect.equal
                    (kinds |> List.filter ((=) NodeKind.FieldDeclaration) |> List.length)
                    2
                    "Both fields survive."

                let first = findNode NodeKind.ClassDeclaration tree
                let next = source.IndexOf("class D", StringComparison.Ordinal)

                Expect.equal
                    (tree.SourceSpan first)
                    (struct (0, next - 1))
                    "The first class ends at its own closing brace."

                RoundTrip.checkBuffer "opaque.cs" source tree.LexerBuffer |> expectConforms

                NodeOracle.checkTree "opaque.cs" source tree |> expectConforms
            }
            test "unfinished declarations and opaque bodies always make progress" {
                let tree = SyntaxTree()

                let source =
                    "[A] public partial record R<T>(int X) : B(X) where T : class { int P { get; init; } void M() { if (true) { M(); } } }"

                for length in 0 .. source.Length do
                    let fragment = source.Substring(0, length)
                    Parser.parse fragment tree
                    RoundTrip.checkBuffer "fragment.cs" fragment tree.LexerBuffer |> expectConforms

                for fragment in
                    [
                        "ref readonly struct T {}"
                        "class C { @@@"
                        "class C { required P; partial Q; file R; scoped S; async T; }"
                        "class C { List<List<int>> x;"
                        "namespace A { using"
                        "[assembly:"
                    ] do
                    Parser.parse fragment tree
                    RoundTrip.checkBuffer "fragment.cs" fragment tree.LexerBuffer |> expectConforms
            }
            test "nesting past the thread's stack fails the file, not the process" {
                let depth = 20000

                let parsedOn (bytes: int) (source: string) =
                    let mutable failure: exn = null

                    let worker =
                        Thread(
                            ThreadStart(fun () ->
                                try
                                    Parser.parse source (SyntaxTree())
                                with error ->
                                    failure <- error),
                            bytes
                        )

                    worker.Start()
                    worker.Join()
                    failure

                let nest (opening: string) (middle: string) (closing: string) =
                    String.replicate depth opening + middle + String.replicate depth closing

                for name, source in
                    [
                        "Expression", "class C { void M() { var x = " + nest "(" "1" ")" + "; } }"
                        "UnaryExpression",
                        "class C { void M() { var x = " + String.replicate depth "!" + "f; } }"
                        "Type", "class C { " + nest "G<" "int" ">" + " F; }"
                        "Postfix",
                        "class C { void M() { var x = a" + String.replicate depth "?.b" + "; } }"
                        "Pattern", "class C { void M() { var x = o is " + nest "(" "1" ")" + "; } }"
                        "PatternAtom",
                        "class C { void M() { var x = o is "
                        + String.replicate depth "not "
                        + "1; } }"
                        "ExpressionInitializer",
                        "class C { void M() { var x = new int[] " + nest "{ " "1" " }" + "; } }"
                        "Designation",
                        "class C { void M() { var " + nest "(" "a, b" ")" + " = t; } }"
                        "Statement", "class C { void M() { " + nest "if (a) " "b();" "" + " } }"
                        "Member", nest "class C { " "" "}"
                        "Declarations", nest "namespace N { " "" "}"
                        "directive condition", "#if " + nest "(" "A" ")" + "\n#endif\nclass C { }"
                        "interpolation",
                        "class C { void M() { var x = " + nest "$\"{" "1" "}\"" + "; } }"
                    ] do
                    match parsedOn (1024 * 1024) source with
                    | null ->
                        failtestf "%s must not parse %d levels deep on a 1 MB stack." name depth
                    | error ->
                        Expect.isTrue
                            (error :? InsufficientExecutionStackException)
                            $"{name}: exhaustion must stay catchable, not {error.GetType().Name}."

                        Expect.stringContains
                            error.Message
                            "nested too deeply"
                            $"{name}: the failure must describe the file."

                        Expect.isNotNull
                            error.InnerException
                            $"{name}: the runtime's own report must be retained."

                for source in
                    [
                        "class C { void M() { var x = "
                        + String.replicate 64 "("
                        + "1"
                        + String.replicate 64 ")"
                        + "; } }"
                        "class C { "
                        + String.replicate 64 "G<"
                        + "int"
                        + String.replicate 64 ">"
                        + " F; }"
                    ] do
                    match parsedOn (1024 * 1024) source with
                    | null -> ()
                    | error -> failtestf "Ordinary nesting must still parse: %s" error.Message
            }
            test
                "SyntaxTree reuses parser working buffers and fast-paths non-interpolated token copy" {
                let tree = SyntaxTree()
                let plain = "class C { int X = 1; string S = \"plain\"; object Q = a ? [b] : c; }"
                let flatInterp = "class C { string S = $\"value = {1 + 2}\"; }"
                let nestedInterp = "class C { string S = $\"outer = {$\"inner = {3}\"}\"; }"

                Parser.parse plain tree
                Expect.isFalse tree.LexerBuffer.HasInterpolated "Plain source has no interpolation."
                let retainedConditionals = tree.CollectionConditionals
                let retainedEnds = tree.ExpressionEnds

                Parser.parse flatInterp tree
                Expect.isTrue tree.LexerBuffer.HasInterpolated "Flat interpolation sets flag."
                NodeOracle.check "flat-interp.cs" flatInterp tree |> expectConforms

                Parser.parse nestedInterp tree
                Expect.isTrue tree.LexerBuffer.HasInterpolated "Nested interpolation sets flag."
                NodeOracle.check "nested-interp.cs" nestedInterp tree |> expectConforms

                Parser.parse plain tree
                Expect.isFalse tree.LexerBuffer.HasInterpolated "Reset clears interpolation flag."

                Expect.isTrue
                    (obj.ReferenceEquals(retainedConditionals, tree.CollectionConditionals))
                    "Small parse retains CollectionConditionals array."

                Expect.isTrue
                    (obj.ReferenceEquals(retainedEnds, tree.ExpressionEnds))
                    "Small parse retains ExpressionEnds dictionary."

                NodeOracle.check "plain.cs" plain tree |> expectConforms
            }
            test "interpolation segmentation matches Roslyn's own token boundaries" {
                let describeCsff (source: string) =
                    let buffer = TokenBuffer()
                    Lexer.lex source buffer
                    let tree = SyntaxTree()
                    let entries = ResizeArray<int * string>()
                    let recovered = ResizeArray<int>()

                    let rec walk (token: Token) =
                        if token.Kind = TokenKind.InterpolatedStringToken then
                            let holes = ResizeArray<struct (int * int)>()
                            tree.Reset()

                            let expanded =
                                (InterpolationLexer.expandWithHoles source token tree holes)
                                    .ToArray()

                            if tree.RecoveredTokens > 0 then
                                recovered.Add token.Start

                            let insideHole start =
                                let mutable hit = false

                                for index = 0 to holes.Count - 1 do
                                    let struct (holeStart, holeLength) = holes[index]

                                    if start >= holeStart && start < holeStart + holeLength then
                                        hit <- true

                                hit

                            let first = expanded[0]
                            let last = expanded[expanded.Length - 1]
                            let parts = ResizeArray<string>()

                            parts.Add(
                                String.Format(
                                    "start {0} [{1},{2})",
                                    first.Kind,
                                    first.Start,
                                    first.End
                                )
                            )

                            let mutable holeIndex = 0

                            for index = 1 to expanded.Length - 2 do
                                let item = expanded[index]

                                if holeIndex < holes.Count then
                                    let struct (holeStart, holeLength) = holes[holeIndex]

                                    if item.Start = holeStart then
                                        parts.Add(
                                            String.Format(
                                                "hole [{0},{1})",
                                                holeStart,
                                                holeStart + holeLength
                                            )
                                        )

                                        holeIndex <- holeIndex + 1

                                if
                                    item.Kind = TokenKind.InterpolatedStringTextToken
                                    && not (insideHole item.Start)
                                then
                                    parts.Add(String.Format("text [{0},{1})", item.Start, item.End))

                            parts.Add(
                                String.Format("end {0} [{1},{2})", last.Kind, last.Start, last.End)
                            )

                            entries.Add(token.Start, String.concat " " parts)

                            for index = 1 to expanded.Length - 2 do
                                walk expanded[index]

                    for index = 0 to buffer.TokenCount - 1 do
                        walk (buffer.Token index)

                    let described = entries |> Seq.sortBy fst |> Seq.map snd |> String.concat "\n"

                    described, List.ofSeq recovered

                let describeRoslyn (source: string) =
                    let tree = CSharpSyntaxTree.ParseText source
                    let root = tree.GetRoot()
                    let entries = ResizeArray<int * string>()

                    for node in root.DescendantNodes() do
                        match node with
                        | :? InterpolatedStringExpressionSyntax as expression ->
                            let first = expression.StringStartToken
                            let last = expression.StringEndToken
                            let parts = ResizeArray<string>()

                            parts.Add(
                                String.Format(
                                    "start {0} [{1},{2})",
                                    first.Kind(),
                                    first.SpanStart,
                                    first.Span.End
                                )
                            )

                            for content in expression.Contents do
                                match content with
                                | :? InterpolationSyntax as hole ->
                                    parts.Add(
                                        String.Format(
                                            "hole [{0},{1})",
                                            hole.SpanStart,
                                            hole.Span.End
                                        )
                                    )
                                | _ ->
                                    parts.Add(
                                        String.Format(
                                            "text [{0},{1})",
                                            content.SpanStart,
                                            content.Span.End
                                        )
                                    )

                            parts.Add(
                                String.Format(
                                    "end {0} [{1},{2})",
                                    last.Kind(),
                                    last.SpanStart,
                                    last.Span.End
                                )
                            )

                            entries.Add(first.SpanStart, String.concat " " parts)
                        | _ -> ()

                    let errors =
                        tree.GetDiagnostics()
                        |> Seq.filter (fun diagnostic ->
                            diagnostic.Severity = DiagnosticSeverity.Error)
                        |> Seq.length

                    entries |> Seq.sortBy fst |> Seq.map snd |> String.concat "\n", errors

                for literal in
                    [
                        "$\"\"\"\n    alpha\n    \"\"\""
                        "$\"\"\"\n    alpha {x} beta\n    gamma\n    \"\"\""
                        "$\"\"\"\n    {x}{y}\n    \"\"\""
                        "$\"\"\"\n    {x} a {y}\n    \"\"\""
                        "$$\"\"\"\n    alpha {{x}} {single}\n    \"\"\""
                        "$$$\"\"\"\n    alpha {{{x}}} {{pair}}\n    \"\"\""
                        "$\"\"\"\n    alpha {x,5}\n    \"\"\""
                        "$\"\"\"\n    alpha {x:F2}\n    \"\"\""
                        "$\"\"\"\n    alpha {x,-10:yyyy MM dd}\n    \"\"\""
                        "$\"\"\"\n    alpha {x:F\n2} beta\n    \"\"\""
                        "$\"\"\"\n    alpha {x +\n        y}\n    \"\"\""
                        "$\"\"\"\n    alpha {new[] { 1, 2 }.Length}\n    \"\"\""
                        "$\"\"\"\n    alpha {x switch { _ => 1 }}\n    \"\"\""
                        "$\"\"\" alpha {x} beta \"\"\""
                        "$@\"alpha\n{x}\nbeta\""
                        "@$\"alpha\n{x}\nbeta\""
                        "$@\"\n    alpha\"\"\"\" {x}\n    \""
                        "$\"alpha{x}beta\""
                        "$\"alpha{{escaped}}beta{x}\""
                        "$\"\"\"\n    alpha {$@\"p\nq\"} beta\n    \"\"\""
                        "$\"\"\"\n    alpha {F(@\"p\nq\")} beta\n    \"\"\""
                        "$\"\"\"\n    alpha {$\"inner {y}\"} beta\n    \"\"\""
                        "$\"\"\"\n    alpha {x /* } */ + y}\n    \"\"\""
                        "$\"\"\"\n    alpha {F(\"}\")}\n    \"\"\""
                        "$\"\"\"\n    #if ALPHA\n    {x}\n    #endif\n    \"\"\""
                    ] do
                    let source = "class C{string s=" + literal + ";}"
                    let csff, recovered = describeCsff source
                    let roslyn, errors = describeRoslyn source

                    Expect.equal errors 0 ("The fixture must be valid C#: " + literal)

                    Expect.equal recovered [] ("A valid literal needs no recovery: " + literal)

                    Expect.equal
                        csff
                        roslyn
                        ("csff must cut this literal exactly where Roslyn does: " + literal)

                for malformed in
                    [
                        "$\"\"\"\n    alpha {x\n    \"\"\""
                        "$\"\"\"\n    alpha {x}\n    "
                        "$\"\"\"\n    alpha {x:F\n    \"\"\""
                        "$$@\"alpha{x}\""
                    ] do
                    let _, recovered = describeCsff ("class C{string s=" + malformed + ";}")

                    Expect.isNonEmpty
                        recovered
                        ("An uncertain segmentation must report recovery: " + malformed)

                for rejected in
                    [
                        "$\"\"\"\n    alpha {{x}}\n    \"\"\""
                        "$\"\"\"\n    alpha {x}}\n    \"\"\""
                        "$\"\"\"\"\n    alpha {x}\n    \"\"\""
                    ] do
                    let source = "class C{string s=" + rejected + ";}"
                    let csff, recovered = describeCsff source
                    let roslyn, errors = describeRoslyn source

                    Expect.isGreaterThan errors 0 ("The fixture must be rejected: " + rejected)

                    Expect.isTrue
                        (not (List.isEmpty recovered) || csff = roslyn)
                        ("Decline or agree, never a third answer: "
                         + rejected
                         + "\ncsff:   "
                         + csff
                         + "\nroslyn: "
                         + roslyn)
            }
            test "borrowed trivia growth during interpolation expansion preserves all hole trivia" {
                let source =
                    "class C { string s = $\"{"
                    + String.concat " + " (List.replicate 20 "a /*c*/")
                    + "}\"; }"

                let tree = SyntaxTree()
                Parser.parse source tree
                let mutable comments = 0

                for i = 0 to tree.TriviaCount - 1 do
                    if (tree.Trivia i).Kind = TriviaKind.MultiLineCommentTrivia then
                        comments <- comments + 1

                Expect.equal comments 20 "Every interpolation comment survives trivia array growth."
            }
            test
                "parseFromLexed succeeds on unlexed SyntaxTree for code, empty, and trivia-only inputs" {
                for source in
                    [ ""; "   \n"; "// only comment\n"; "class C { int M() => 1 + 2; }\n" ] do
                    let expected = SyntaxTree()
                    Parser.parse source expected
                    let actual = SyntaxTree()
                    Parser.parseFromLexed source actual

                    Expect.equal
                        actual.IsComplete
                        expected.IsComplete
                        "IsComplete matches Parser.parse"

                    Expect.equal
                        actual.RootIndex
                        expected.RootIndex
                        "RootIndex matches Parser.parse"

                    Expect.equal
                        (actual.NodeSpan().ToArray())
                        (expected.NodeSpan().ToArray())
                        "Nodes match Parser.parse"

                    Expect.equal
                        (actual.TokenSpan().ToArray())
                        (expected.TokenSpan().ToArray())
                        "Tokens match Parser.parse"

                    Expect.equal
                        (actual.TriviaSpan().ToArray())
                        (expected.TriviaSpan().ToArray())
                        "Trivia matches Parser.parse"

                    Expect.equal
                        actual.ChildCount
                        expected.ChildCount
                        "ChildCount matches Parser.parse"
            }
            test "parseFromLexed succeeds after lexUnlessGenerated skips a generated file" {
                let source = "// <auto-generated />\nclass G { int X => 1; }\n"
                let expected = SyntaxTree()
                Parser.parse source expected
                let actual = SyntaxTree()
                let isGenerated = Parser.lexUnlessGenerated source actual
                Expect.isTrue isGenerated "Generated file header should skip initial lexing"
                Expect.equal actual.TokenCount 0 "Skipped lexing leaves TokenCount at zero"
                Parser.parseFromLexed source actual
                Expect.equal actual.IsComplete expected.IsComplete "IsComplete matches Parser.parse"
                Expect.equal actual.RootIndex expected.RootIndex "RootIndex matches Parser.parse"

                Expect.equal
                    (actual.NodeSpan().ToArray())
                    (expected.NodeSpan().ToArray())
                    "Nodes match Parser.parse"

                Expect.equal
                    (actual.TokenSpan().ToArray())
                    (expected.TokenSpan().ToArray())
                    "Tokens match Parser.parse"

                Expect.equal
                    (actual.TriviaSpan().ToArray())
                    (expected.TriviaSpan().ToArray())
                    "Trivia matches Parser.parse"

                Expect.equal actual.ChildCount expected.ChildCount "ChildCount matches Parser.parse"
            }
            test "repeated parseFromLexed calls reset parsed CST state without duplication" {
                let source = "class C {\n    string M(int x) => $\"v={x /* c */ + 1}\";\n}\n"

                let expected = SyntaxTree()
                Parser.parse source expected
                let actual = SyntaxTree()
                Parser.lexOnly source actual
                Parser.parseFromLexed source actual
                Parser.parseFromLexed source actual

                Expect.equal
                    actual.IsComplete
                    expected.IsComplete
                    "IsComplete matches after repeat parseFromLexed"

                Expect.equal
                    actual.RootIndex
                    expected.RootIndex
                    "RootIndex matches after repeat parseFromLexed"

                Expect.equal actual.NodeCount expected.NodeCount "NodeCount does not accumulate"
                Expect.equal actual.TokenCount expected.TokenCount "TokenCount does not accumulate"

                Expect.equal
                    actual.TriviaCount
                    expected.TriviaCount
                    "TriviaCount does not accumulate"

                Expect.equal actual.ChildCount expected.ChildCount "ChildCount does not accumulate"

                Expect.equal
                    (actual.NodeSpan().ToArray())
                    (expected.NodeSpan().ToArray())
                    "Nodes match after repeat parseFromLexed"

                Expect.equal
                    (actual.TokenSpan().ToArray())
                    (expected.TokenSpan().ToArray())
                    "Tokens match after repeat parseFromLexed"

                Expect.equal
                    (actual.TriviaSpan().ToArray())
                    (expected.TriviaSpan().ToArray())
                    "Trivia matches after repeat parseFromLexed"
            }
            test "malformed Unicode escapes in identifiers make the tree incomplete" {
                for source in
                    [
                        "class C { int a\\u41 = 1; }"
                        "class C { int \\u41 = 1; }"
                        "class C { int @\\u41 = 1; }"
                        "class C { int a\\U0041 = 1; }"
                        "class C { int a\\U00110000 = 1; }"
                    ] do
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    Expect.isFalse tree.IsComplete ("Expected incomplete parse for: " + source)
            }
            test "directives or # inside interpolation holes make the tree incomplete" {
                for source in
                    [
                        "var s = $\"{ # \" }\";"
                        "var s = $@\"{\n#if FOO\n1+1\n#else\n2+2\n#endif\n}\";"
                        "#define FOO\nvar s = $\"{\n#if FOO\n1\n#endif\n}\";"
                        "var s = $\"{ /* unclosed\n#if FOO\n\";"
                    ] do
                    let tree = SyntaxTree()
                    Parser.parse source tree
                    Expect.isFalse tree.IsComplete ("Expected incomplete parse for: " + source)
            }
            test "malformed preprocessor directives mark HasMalformedTrivia" {
                for source in [ "#define @foo\nclass A {}\n"; "#if\nclass A {}\n#endif\n" ] do
                    let tree = SyntaxTree()
                    Parser.parse source tree

                    Expect.isTrue
                        tree.IsComplete
                        ("Valid code after malformed directive parses cleanly: " + source)

                    Expect.isTrue
                        tree.LexerBuffer.HasMalformedTrivia
                        ("Expected malformed trivia for: " + source)
            }
        ]
