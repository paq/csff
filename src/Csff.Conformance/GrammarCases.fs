namespace Csff.Conformance

open System

type GeneratedPattern =
    | Constant of int
    | Null
    | Relation of string * int
    | Negated of GeneratedPattern
    | Combined of string * GeneratedPattern * GeneratedPattern
    | Property of GeneratedPattern
    | ListPattern of GeneratedPattern list * bool

type GeneratedExpression =
    | Number of int
    | RawString of quotes: int * multiline: bool * utf8: bool * lines: string list
    | Interpolated of dollars: int * quotes: int * multiline: bool * GeneratedExpression

type TriviaSite =
    | ConstInitializer
    | FieldInitializer
    | PropertyInitializer
    | LocalInitializer
    | AfterBinaryOperator
    | BeforeBinaryOperator
    | ArgumentListOpen
    | ArgumentListComma
    | ArgumentListClose
    | ParameterListOpen
    | ParameterListComma
    | CollectionInitializer
    | CollectionExpression
    | ObjectInitializer
    | AttributeListOpen
    | AttributeArgument
    | InterpolationHole
    | BeforeInterpolatedString
    | AfterInterpolatedString
    | TypeArgumentList
    | StackallocBracket
    | MemberAccessDot
    | AfterReturn
    | AfterArrow
    | SwitchArm

type TriviaFrame =
    | IfEndif
    | IfElseEndif
    | IfElifEndif
    | IfElifElseEndif
    | SplitArms
    | ActiveSplitArms
    | DifferingArms
    | InactiveArm
    | NestedFrames
    | AdjacentFrames
    | RegionFrame
    | PragmaLine
    | NullableLine
    | WarningLine
    | LineNumberLine
    | EndOfLineComment
    | EmptyComment
    | DocumentationComment
    | DelimitedComment

type TriviaPayload =
    | LiteralValue
    | LocalName
    | MemberPath
    | Call
    | Sum
    | InterpolatedText
    | Creation
    | CollectionLiteral
    | RawLiteral

type TriviaContext =
    | FlushLeft
    | IndentedTrivia
    | BlankBefore
    | BlankAfter
    | CommentBefore
    | TrailingAtEndOfFile

type GrammarCase =
    | RawStrings of GeneratedExpression list
    | Interpolation of GeneratedExpression
    | Patterns of GeneratedPattern list
    | Directives of conditions: string list * nested: bool
    | Ignore of range: bool * statements: bool * count: int
    | TriviaSplit of
        site: TriviaSite *
        frame: TriviaFrame *
        payload: TriviaPayload *
        context: TriviaContext

module GrammarCases =
    let rec pattern value =
        match value with
        | Constant n -> string n
        | Null -> "null"
        | Relation(op, n) -> op + " " + string n
        | Negated p -> "not (" + pattern p + ")"
        | Combined(op, left, right) -> "(" + pattern left + ") " + op + " (" + pattern right + ")"
        | Property p -> "{ Length:" + pattern p + "}"
        | ListPattern(patterns, rest) ->
            "["
            + String.concat
                ","
                (List.map pattern patterns @ (if rest then [ ".. var rest" ] else []))
            + "]"

    let rec expression value =
        match value with
        | Number n -> string n
        | RawString(quotes, multiline, utf8, lines) ->
            let delimiter = String('"', quotes)

            let body =
                if multiline then
                    "\n    " + String.concat "\n    " lines + "\n    "
                else
                    String.concat " " lines

            delimiter + body + delimiter + (if utf8 then "u8" else "")
        | Interpolated(dollars, quotes, multiline, inner) ->
            let delimiter =
                if dollars = 1 && quotes = 1 then
                    "\""
                else
                    String('"', quotes)

            let hole =
                String('{', dollars) + expression inner + ",10:000" + String('}', dollars)

            String('$', dollars)
            + delimiter
            + (if multiline then
                   "\n    before " + hole + " after\n    "
               else
                   "before " + hole + " after")
            + delimiter

    let triviaSites =
        [
            ConstInitializer
            FieldInitializer
            PropertyInitializer
            LocalInitializer
            AfterBinaryOperator
            BeforeBinaryOperator
            ArgumentListOpen
            ArgumentListComma
            ArgumentListClose
            ParameterListOpen
            ParameterListComma
            CollectionInitializer
            CollectionExpression
            ObjectInitializer
            AttributeListOpen
            AttributeArgument
            InterpolationHole
            BeforeInterpolatedString
            AfterInterpolatedString
            TypeArgumentList
            StackallocBracket
            MemberAccessDot
            AfterReturn
            AfterArrow
            SwitchArm
        ]

    let triviaFrames =
        [
            IfEndif
            IfElseEndif
            IfElifEndif
            IfElifElseEndif
            SplitArms
            ActiveSplitArms
            DifferingArms
            InactiveArm
            NestedFrames
            AdjacentFrames
            RegionFrame
            PragmaLine
            NullableLine
            WarningLine
            LineNumberLine
            EndOfLineComment
            EmptyComment
            DocumentationComment
            DelimitedComment
        ]

    let triviaPayloads =
        [
            LiteralValue
            LocalName
            MemberPath
            Call
            Sum
            InterpolatedText
            Creation
            CollectionLiteral
            RawLiteral
        ]

    let triviaContexts =
        [
            FlushLeft
            IndentedTrivia
            BlankBefore
            BlankAfter
            CommentBefore
            TrailingAtEndOfFile
        ]

    let isCommentFrame frame =
        match frame with
        | EndOfLineComment
        | EmptyComment
        | DocumentationComment
        | DelimitedComment -> true
        | _ -> false

    let admitsTrivia site frame =
        match site with
        | InterpolationHole -> isCommentFrame frame
        | _ -> true

    let private payloadText payload =
        match payload with
        | LiteralValue -> "1", "2"
        | LocalName -> "value", "other"
        | MemberPath -> "Holder.First", "Holder.Second"
        | Call -> "Compute(1)", "Compute(2)"
        | Sum -> "1 + value", "2 + value"
        | InterpolatedText -> "$\"a{value}b\"", "$\"c{value}d\""
        | Creation -> "new Holder()", "new Holder(1)"
        | CollectionLiteral -> "[1, value]", "[2, value]"
        | RawLiteral -> "\"\"\"text\"\"\"", "\"\"\"other\"\"\""

    let private splitSite site payload =
        let first, second = payloadText payload
        let spread = "Compute(\n                " + second + ")"

        match site with
        | ConstInitializer ->
            "class C\n{\n    public const int Field =\n",
            "        " + first + ";\n",
            "        " + second + ";\n",
            "        " + spread + ";\n",
            "}\n"
        | FieldInitializer ->
            "class C\n{\n    public int field =\n",
            "        " + first + ";\n",
            "        " + second + ";\n",
            "        " + spread + ";\n",
            "}\n"
        | PropertyInitializer ->
            "class C\n{\n    public int Value { get; } =\n",
            "        " + first + ";\n",
            "        " + second + ";\n",
            "        " + spread + ";\n",
            "}\n"
        | LocalInitializer ->
            "class C\n{\n    int M(int value)\n    {\n        var local =\n",
            "            " + first + ";\n",
            "            " + second + ";\n",
            "            " + spread + ";\n",
            "        return 0;\n    }\n}\n"
        | AfterBinaryOperator ->
            "class C\n{\n    int M(int value)\n    {\n        return value +\n",
            "            " + first + ";\n",
            "            " + second + ";\n",
            "            " + spread + ";\n",
            "    }\n}\n"
        | BeforeBinaryOperator ->
            "class C\n{\n    int M(int value)\n    {\n        return value\n",
            "            + " + first + ";\n",
            "            + " + second + ";\n",
            "            + " + spread + ";\n",
            "    }\n}\n"
        | ArgumentListOpen ->
            "class C\n{\n    int M(int value)\n    {\n        return Compute(\n",
            "            " + first + ");\n",
            "            " + second + ");\n",
            "            " + spread + ");\n",
            "    }\n}\n"
        | ArgumentListComma ->
            "class C\n{\n    int M(int value)\n    {\n        return Compute(value,\n",
            "            " + first + ");\n",
            "            " + second + ");\n",
            "            " + spread + ");\n",
            "    }\n}\n"
        | ArgumentListClose ->
            "class C\n{\n    int M(int value)\n    {\n        return Compute("
            + first
            + "\n",
            "            );\n",
            "            , " + second + ");\n",
            "            , " + spread + ");\n",
            "    }\n}\n"
        | ParameterListOpen ->
            "class C\n{\n    int M(\n",
            "        int value) => " + first + ";\n",
            "        long value) => " + second + ";\n",
            "        int value) => " + spread + ";\n",
            "}\n"
        | ParameterListComma ->
            "class C\n{\n    int M(int value,\n",
            "        int other) => " + first + ";\n",
            "        long other) => " + second + ";\n",
            "        int other) => " + spread + ";\n",
            "}\n"
        | CollectionInitializer ->
            "class C\n{\n    int[] M(int value)\n    {\n        return new int[]\n        {\n",
            "            " + first + ",\n        };\n",
            "            " + second + ", " + second + ",\n        };\n",
            "            " + spread + ",\n        };\n",
            "    }\n}\n"
        | CollectionExpression ->
            "class C\n{\n    int[] M(int value)\n    {\n        return [\n",
            "            " + first + ",\n        ];\n",
            "            " + second + ", " + second + ",\n        ];\n",
            "            " + spread + ",\n        ];\n",
            "    }\n}\n"
        | ObjectInitializer ->
            "class C\n{\n    object M(int value)\n    {\n        return new Holder\n        {\n",
            "            First = " + first + ",\n        };\n",
            "            Second = " + second + ",\n        };\n",
            "            First = " + spread + ",\n        };\n",
            "    }\n}\n"
        | AttributeListOpen ->
            "class C\n{\n    [\n",
            "        Marker(" + first + ")]\n",
            "        Other(" + second + ")]\n",
            "        Marker(" + spread + ")]\n",
            "    int field;\n}\n"
        | AttributeArgument ->
            "class C\n{\n    [Marker(\n",
            "        " + first + ")]\n",
            "        " + second + ", " + second + ")]\n",
            "        " + spread + ")]\n",
            "    int field;\n}\n"
        | InterpolationHole ->
            "class C\n{\n    string M(int value)\n    {\n        return $\"\"\"\"\nbefore {\n",
            first + "} after\n\"\"\"\";\n",
            second + "} after\n\"\"\"\";\n",
            spread + "} after\n\"\"\"\";\n",
            "    }\n}\n"
        | BeforeInterpolatedString ->
            "class C\n{\n    string M(int value)\n    {\n        return\n",
            "            $\"before {value} after\" + " + first + ";\n",
            "            $\"other {value} tail\" + " + second + ";\n",
            "            $\"before {value} after\" + " + spread + ";\n",
            "    }\n}\n"
        | AfterInterpolatedString ->
            "class C\n{\n    string M(int value)\n    {\n        return $\"before {value} after\"\n",
            "            + " + first + ";\n",
            "            + " + second + " + " + second + ";\n",
            "            + " + spread + ";\n",
            "    }\n}\n"
        | TypeArgumentList ->
            "class C\n{\n    int M(int value)\n    {\n        return GetValue<\n",
            "            int>(" + first + ");\n",
            "            long>(" + second + ");\n",
            "            int>(" + spread + ");\n",
            "    }\n}\n"
        | StackallocBracket ->
            "class C\n{\n    void M(int value)\n    {\n        var span = stackalloc int[\n",
            "            " + first + "];\n",
            "            " + second + "];\n",
            "            " + spread + "];\n",
            "    }\n}\n"
        | MemberAccessDot ->
            "class C\n{\n    int M(int value)\n    {\n        return Holder.\n",
            "            First + " + first + ";\n",
            "            Second + " + second + ";\n",
            "            First + " + spread + ";\n",
            "    }\n}\n"
        | AfterReturn ->
            "class C\n{\n    int M(int value)\n    {\n        return\n",
            "            " + first + ";\n",
            "            " + second + ";\n",
            "            " + spread + ";\n",
            "    }\n}\n"
        | AfterArrow ->
            "class C\n{\n    int M(int value) =>\n",
            "        " + first + ";\n",
            "        " + second + ";\n",
            "        " + spread + ";\n",
            "}\n"
        | SwitchArm ->
            "class C\n{\n    int M(int value)\n    {\n        return value switch\n        {\n",
            "            1 => " + first + ",\n            _ => 0,\n        };\n",
            "            2 => " + second + ",\n            _ => 0,\n        };\n",
            "            1 => " + spread + ",\n            _ => 0,\n        };\n",
            "    }\n}\n"

    let private triviaSkeleton frame =
        match frame with
        | IfEndif
        | SplitArms
        | ActiveSplitArms
        | DifferingArms
        | InactiveArm -> "#if COND\n#endif"
        | IfElseEndif -> "#if COND\n#else\n#endif"
        | IfElifEndif -> "#if COND\n#elif OTHER\n#endif"
        | IfElifElseEndif -> "#if COND\n#elif OTHER\n#else\n#endif"
        | NestedFrames -> "#if COND\n#if OTHER\n#endif\n#endif"
        | AdjacentFrames -> "#if COND\n#endif\n#if OTHER\n#endif"
        | RegionFrame -> "#region Marker\n#endregion"
        | PragmaLine -> "#pragma warning disable 1591"
        | NullableLine -> "#nullable enable"
        | WarningLine -> "#warning generated"
        | LineNumberLine -> "#line default"
        | EndOfLineComment -> "// comment"
        | EmptyComment -> "//"
        | DocumentationComment -> "/// <summary>text</summary>"
        | DelimitedComment -> "/* comment */"

    let private indentTrivia (text: string) =
        text.Split('\n')
        |> Array.map (fun line ->
            if
                line.StartsWith("#", StringComparison.Ordinal)
                || line.StartsWith("//", StringComparison.Ordinal)
                || line.StartsWith("/*", StringComparison.Ordinal)
            then
                "        " + line
            else
                line)
        |> String.concat "\n"

    let private triviaBlock frame live alternative spread =
        match frame with
        | SplitArms -> "#if COND\n" + alternative + "#else\n" + live + "#endif\n"
        | ActiveSplitArms -> "#if COND\n" + live + "#else\n" + alternative + "#endif\n"
        | DifferingArms -> "#if COND\n" + spread + "#else\n" + live + "#endif\n"
        | InactiveArm -> "#if COND\nthis is not C# at all ((\n#endif\n" + live
        | _ -> triviaSkeleton frame + "\n" + live

    let private renderTriviaSplit site frame payload context =
        let prefix, live, alternative, spread, tail = splitSite site payload
        let gap = if context = BlankAfter then "\n" else ""
        let block = triviaBlock frame (gap + live) alternative spread

        let block =
            match context with
            | FlushLeft
            | BlankAfter
            | TrailingAtEndOfFile -> block
            | IndentedTrivia -> indentTrivia block
            | BlankBefore -> "\n" + block
            | CommentBefore -> "// neighbour\n" + block

        let definition = if frame = ActiveSplitArms then "#define COND\n" else ""
        let source = definition + prefix + block + tail

        if context = TrailingAtEndOfFile then
            source.TrimEnd('\n') + "\n" + triviaSkeleton frame
        else
            source

    let render value =
        let memberBody body =
            "class C{object M(object value){" + body + "}}"

        match value with
        | RawStrings expressions ->
            "class C{"
            + (expressions
               |> List.mapi (fun i e -> $"object field{i}=" + expression e + ";")
               |> String.concat "")
            + "}"
        | Interpolation e -> memberBody ("return " + expression e + ";")
        | Patterns patterns ->
            memberBody (
                "return value switch{"
                + (patterns |> List.mapi (fun i p -> pattern p + $"=>{i},") |> String.concat "")
                + "_=>0};"
            )
        | Directives(conditions, nested) ->
            let conditional i condition =
                $"#if {condition}\nclass A{i}{{int a=1;}}\n"
                + (if nested then
                       $"#if OTHER\nclass N{i}{{int n=2;}}\n#endif\n"
                   else
                       "")
                + $"#elif SECOND\nclass B{i}{{int b=2;}}\n#else\nclass C{i}{{int c=3;}}\n#endif\n"

            "#define ACTIVE\n" + (conditions |> List.mapi conditional |> String.concat "")
        | Ignore(range, statements, count) ->
            let ignored i =
                if statements then
                    $"var x{i} =  1 +  2;\n"
                else
                    $"int x{i} =  1 +  2;\n"

            let body =
                if range then
                    "// csff-ignore-start\n"
                    + ([ 0 .. count - 1 ] |> List.map ignored |> String.concat "")
                    + "// csff-ignore-end\n"
                    + (if statements then "return 1;\n" else "int last=0;\n")
                else
                    "// csff-ignore\n"
                    + ignored 0
                    + (if statements then "return 1;\n" else "int last=0;\n")

            if statements then
                memberBody ("\n" + body)
            else
                "class C{\n" + body + "}"
        | TriviaSplit(site, frame, payload, context) -> renderTriviaSplit site frame payload context

    let rec shrinkPattern value =
        seq {
            match value with
            | Constant n
            | Relation(_, n) when n <> 0 -> yield Constant 0
            | Negated p
            | Property p ->
                yield p

                for smaller in shrinkPattern p do
                    yield
                        (match value with
                         | Negated _ -> Negated smaller
                         | _ -> Property smaller)
            | Combined(op, left, right) ->
                yield left
                yield right

                for smaller in shrinkPattern left do
                    yield Combined(op, smaller, right)

                for smaller in shrinkPattern right do
                    yield Combined(op, left, smaller)
            | ListPattern(patterns, rest) ->
                for p in patterns do
                    yield p

                if not (List.isEmpty patterns) then
                    yield ListPattern([], rest)

                if rest then
                    yield ListPattern(patterns, false)
            | _ -> ()
        }

    let rec shrinkExpression value =
        seq {
            match value with
            | Number n when n <> 0 -> yield Number 0
            | RawString(quotes, multiline, utf8, lines) ->
                if quotes > 3 then
                    yield RawString(3, multiline, utf8, lines)

                if utf8 then
                    yield RawString(quotes, multiline, false, lines)

                if lines <> [ "a" ] then
                    yield RawString(quotes, multiline, utf8, [ "a" ])
            | Interpolated(dollars, quotes, multiline, inner) ->
                yield inner

                for smaller in shrinkExpression inner do
                    yield Interpolated(dollars, quotes, multiline, smaller)

                if dollars > 1 then
                    yield Interpolated(1, quotes, multiline, inner)
            | _ -> ()
        }

    let shrink value =
        seq {
            match value with
            | RawStrings expressions ->
                for e in expressions do
                    yield RawStrings [ e ]

                    for smaller in shrinkExpression e do
                        yield RawStrings [ smaller ]
            | Interpolation e ->
                for smaller in shrinkExpression e do
                    yield Interpolation smaller
            | Patterns patterns ->
                for p in patterns do
                    if patterns.Length > 1 then
                        yield Patterns [ p ]

                    for smaller in shrinkPattern p do
                        yield Patterns [ smaller ]
            | Directives(conditions, nested) ->
                if nested then
                    yield Directives(conditions, false)

                if conditions.Length > 1 then
                    for condition in conditions do
                        yield Directives([ condition ], nested)
            | Ignore(range, statements, count) ->
                if count > 1 then
                    yield Ignore(range, statements, 1)

                if range then
                    yield Ignore(false, statements, 1)
            | TriviaSplit(site, frame, payload, context) ->
                if context <> FlushLeft then
                    yield TriviaSplit(site, frame, payload, FlushLeft)

                let simplest =
                    if admitsTrivia site IfEndif then
                        IfEndif
                    else
                        EndOfLineComment

                if frame <> simplest then
                    yield TriviaSplit(site, simplest, payload, context)

                if payload <> LiteralValue then
                    yield TriviaSplit(site, frame, LiteralValue, context)
        }
        |> Seq.filter ((<>) value)
        |> Seq.distinct
