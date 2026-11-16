namespace Csff.Parser

open System
open Csff.Lexer

module internal ExpressionSyntax =
    let predefined kind =
        int kind >= int TokenKind.BoolKeyword && int kind <= int TokenKind.ObjectKeyword

    let private binaryCase kind =
        match kind with
        | TokenKind.EqualsToken -> struct (1, NodeKind.SimpleAssignmentExpression)
        | TokenKind.PlusEqualsToken -> struct (1, NodeKind.AddAssignmentExpression)
        | TokenKind.MinusEqualsToken -> struct (1, NodeKind.SubtractAssignmentExpression)
        | TokenKind.AsteriskEqualsToken -> struct (1, NodeKind.MultiplyAssignmentExpression)
        | TokenKind.SlashEqualsToken -> struct (1, NodeKind.DivideAssignmentExpression)
        | TokenKind.PercentEqualsToken -> struct (1, NodeKind.ModuloAssignmentExpression)
        | TokenKind.AmpersandEqualsToken -> struct (1, NodeKind.AndAssignmentExpression)
        | TokenKind.BarEqualsToken -> struct (1, NodeKind.OrAssignmentExpression)
        | TokenKind.CaretEqualsToken -> struct (1, NodeKind.ExclusiveOrAssignmentExpression)
        | TokenKind.LessThanLessThanEqualsToken ->
            struct (1, NodeKind.LeftShiftAssignmentExpression)
        | TokenKind.GreaterThanGreaterThanEqualsToken ->
            struct (1, NodeKind.RightShiftAssignmentExpression)
        | TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken ->
            struct (1, NodeKind.UnsignedRightShiftAssignmentExpression)
        | TokenKind.QuestionQuestionEqualsToken -> struct (1, NodeKind.CoalesceAssignmentExpression)
        | TokenKind.QuestionQuestionToken -> struct (3, NodeKind.CoalesceExpression)
        | TokenKind.BarBarToken -> struct (4, NodeKind.LogicalOrExpression)
        | TokenKind.AmpersandAmpersandToken -> struct (5, NodeKind.LogicalAndExpression)
        | TokenKind.BarToken -> struct (6, NodeKind.BitwiseOrExpression)
        | TokenKind.CaretToken -> struct (7, NodeKind.ExclusiveOrExpression)
        | TokenKind.AmpersandToken -> struct (8, NodeKind.BitwiseAndExpression)
        | TokenKind.EqualsEqualsToken -> struct (9, NodeKind.EqualsExpression)
        | TokenKind.ExclamationEqualsToken -> struct (9, NodeKind.NotEqualsExpression)
        | TokenKind.LessThanToken -> struct (10, NodeKind.LessThanExpression)
        | TokenKind.LessThanEqualsToken -> struct (10, NodeKind.LessThanOrEqualExpression)
        | TokenKind.GreaterThanToken -> struct (10, NodeKind.GreaterThanExpression)
        | TokenKind.GreaterThanEqualsToken -> struct (10, NodeKind.GreaterThanOrEqualExpression)
        | TokenKind.IsKeyword -> struct (10, NodeKind.IsExpression)
        | TokenKind.AsKeyword -> struct (10, NodeKind.AsExpression)
        | TokenKind.LessThanLessThanToken -> struct (11, NodeKind.LeftShiftExpression)
        | TokenKind.GreaterThanGreaterThanToken -> struct (11, NodeKind.RightShiftExpression)
        | TokenKind.GreaterThanGreaterThanGreaterThanToken ->
            struct (11, NodeKind.UnsignedRightShiftExpression)
        | TokenKind.PlusToken -> struct (12, NodeKind.AddExpression)
        | TokenKind.MinusToken -> struct (12, NodeKind.SubtractExpression)
        | TokenKind.AsteriskToken -> struct (13, NodeKind.MultiplyExpression)
        | TokenKind.SlashToken -> struct (13, NodeKind.DivideExpression)
        | TokenKind.PercentToken -> struct (13, NodeKind.ModuloExpression)
        | TokenKind.DotDotToken -> struct (14, NodeKind.RangeExpression)
        | _ -> struct (0, NodeKind.None)

    let private binaryTable =
        Array.init 9100 (fun value ->
            let struct (precedence, node) = binaryCase (enum<TokenKind> value)
            (precedence <<< 16) ||| int node)

    [<System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices
                                                    .MethodImplOptions.AggressiveInlining)>]
    let binary (kind: TokenKind) =
        let value = int kind

        if uint value < uint binaryTable.Length then
            let packed = binaryTable[value]
            struct (packed >>> 16, enum<NodeKind>(packed &&& 0xFFFF))
        else
            struct (0, NodeKind.None)

    let unary kind =
        match kind with
        | TokenKind.PlusToken -> NodeKind.UnaryPlusExpression
        | TokenKind.MinusToken -> NodeKind.UnaryMinusExpression
        | TokenKind.ExclamationToken -> NodeKind.LogicalNotExpression
        | TokenKind.TildeToken -> NodeKind.BitwiseNotExpression
        | TokenKind.PlusPlusToken -> NodeKind.PreIncrementExpression
        | TokenKind.MinusMinusToken -> NodeKind.PreDecrementExpression
        | TokenKind.AsteriskToken -> NodeKind.PointerIndirectionExpression
        | TokenKind.AmpersandToken -> NodeKind.AddressOfExpression
        | TokenKind.CaretToken -> NodeKind.IndexExpression
        | _ -> NodeKind.None

    let expressionStart kind =
        predefined kind
        || unary kind <> NodeKind.None
        || match kind with
           | TokenKind.IdentifierToken
           | TokenKind.NumericLiteralToken
           | TokenKind.StringLiteralToken
           | TokenKind.CharacterLiteralToken
           | TokenKind.SingleLineRawStringLiteralToken
           | TokenKind.MultiLineRawStringLiteralToken
           | TokenKind.Utf8StringLiteralToken
           | TokenKind.Utf8SingleLineRawStringLiteralToken
           | TokenKind.Utf8MultiLineRawStringLiteralToken
           | TokenKind.InterpolatedStringToken
           | TokenKind.InterpolatedStringStartToken
           | TokenKind.InterpolatedVerbatimStringStartToken
           | TokenKind.InterpolatedSingleLineRawStringStartToken
           | TokenKind.InterpolatedMultiLineRawStringStartToken
           | TokenKind.OpenParenToken
           | TokenKind.OpenBracketToken
           | TokenKind.NewKeyword
           | TokenKind.ThisKeyword
           | TokenKind.BaseKeyword
           | TokenKind.TrueKeyword
           | TokenKind.FalseKeyword
           | TokenKind.NullKeyword
           | TokenKind.DefaultKeyword
           | TokenKind.TypeOfKeyword
           | TokenKind.SizeOfKeyword
           | TokenKind.CheckedKeyword
           | TokenKind.UncheckedKeyword
           | TokenKind.DelegateKeyword
           | TokenKind.StaticKeyword
           | TokenKind.StackAllocKeyword
           | TokenKind.ThrowKeyword
           | TokenKind.RefKeyword
           | TokenKind.ArgListKeyword
           | TokenKind.MakeRefKeyword
           | TokenKind.RefTypeKeyword
           | TokenKind.RefValueKeyword
           | TokenKind.DotDotToken -> true
           | _ -> false

    let literalStart kind =
        match kind with
        | TokenKind.NumericLiteralToken
        | TokenKind.StringLiteralToken
        | TokenKind.CharacterLiteralToken
        | TokenKind.SingleLineRawStringLiteralToken
        | TokenKind.MultiLineRawStringLiteralToken
        | TokenKind.Utf8StringLiteralToken
        | TokenKind.Utf8SingleLineRawStringLiteralToken
        | TokenKind.Utf8MultiLineRawStringLiteralToken
        | TokenKind.InterpolatedStringToken
        | TokenKind.InterpolatedStringStartToken
        | TokenKind.InterpolatedVerbatimStringStartToken
        | TokenKind.InterpolatedSingleLineRawStringStartToken
        | TokenKind.InterpolatedMultiLineRawStringStartToken
        | TokenKind.TrueKeyword
        | TokenKind.FalseKeyword
        | TokenKind.NullKeyword -> true
        | _ -> false

    let genericFollower kind =
        match kind with
        | TokenKind.OpenParenToken
        | TokenKind.CloseParenToken
        | TokenKind.CloseBracketToken
        | TokenKind.CloseBraceToken
        | TokenKind.ColonToken
        | TokenKind.SemicolonToken
        | TokenKind.CommaToken
        | TokenKind.DotToken
        | TokenKind.QuestionToken
        | TokenKind.EqualsEqualsToken
        | TokenKind.ExclamationEqualsToken
        | TokenKind.BarToken
        | TokenKind.CaretToken
        | TokenKind.AmpersandToken
        | TokenKind.BarBarToken
        | TokenKind.AmpersandAmpersandToken
        | TokenKind.OpenBracketToken
        | TokenKind.LessThanToken
        | TokenKind.LessThanEqualsToken
        | TokenKind.GreaterThanEqualsToken
        | TokenKind.IsKeyword
        | TokenKind.AsKeyword
        | TokenKind.EndOfFileToken -> true
        | _ -> false

    let closing kind =
        match kind with
        | TokenKind.GreaterThanToken
        | TokenKind.GreaterThanGreaterThanToken
        | TokenKind.GreaterThanGreaterThanGreaterThanToken
        | TokenKind.GreaterThanGreaterThanEqualsToken
        | TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken -> true
        | _ -> false

    let closers kind =
        match kind with
        | TokenKind.GreaterThanToken -> 1
        | TokenKind.GreaterThanGreaterThanToken -> 2
        | TokenKind.GreaterThanGreaterThanGreaterThanToken -> 3
        | TokenKind.GreaterThanGreaterThanEqualsToken -> 1
        | TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken -> 2
        | _ -> 0

    let runShape kind =
        match kind with
        | TokenKind.GreaterThanToken -> struct (1, false)
        | TokenKind.GreaterThanGreaterThanToken -> struct (2, false)
        | TokenKind.GreaterThanGreaterThanGreaterThanToken -> struct (3, false)
        | TokenKind.GreaterThanEqualsToken -> struct (1, true)
        | TokenKind.GreaterThanGreaterThanEqualsToken -> struct (2, true)
        | TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken -> struct (3, true)
        | _ -> struct (0, false)

    let runToken greaters equals =
        match greaters, equals with
        | 1, false -> TokenKind.GreaterThanToken
        | 2, false -> TokenKind.GreaterThanGreaterThanToken
        | 3, false -> TokenKind.GreaterThanGreaterThanGreaterThanToken
        | 1, true -> TokenKind.GreaterThanEqualsToken
        | 2, true -> TokenKind.GreaterThanGreaterThanEqualsToken
        | 3, true -> TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken
        | _ -> TokenKind.None

    let residual kind consumed =
        match kind, consumed with
        | TokenKind.GreaterThanGreaterThanToken, 1
        | TokenKind.GreaterThanGreaterThanGreaterThanToken, 2 -> TokenKind.GreaterThanToken
        | TokenKind.GreaterThanGreaterThanGreaterThanToken, 1 ->
            TokenKind.GreaterThanGreaterThanToken
        | TokenKind.GreaterThanGreaterThanEqualsToken, 1
        | TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken, 2 ->
            TokenKind.GreaterThanEqualsToken
        | TokenKind.GreaterThanGreaterThanGreaterThanEqualsToken, 1 ->
            TokenKind.GreaterThanGreaterThanEqualsToken
        | _ -> TokenKind.None

    type TypeMode =
        | Normal
        | AfterIs
        | DefinitePattern
        | AsExpression
        | NewExpression

    let nullableQualifier
        (source: string)
        (input: TokenInput)
        mode
        question
        expressionHasColon
        queryKeyword
        =
        let kind cursor =
            if cursor < input.Count then
                input.KindOf cursor
            else
                TokenKind.EndOfFileToken

        let word cursor (value: string) =
            cursor < input.Count
            && input.KindOf cursor = TokenKind.IdentifierToken
            && source
                .AsSpan(input[cursor].Start, input[cursor].Length)
                .SequenceEqual(value.AsSpan())

        let next = question + 1

        match mode, kind next with
        | AfterIs, TokenKind.OpenBracketToken ->
            match kind (next + 1) with
            | TokenKind.CommaToken -> true
            | TokenKind.CloseBracketToken -> not (expressionHasColon next)
            | _ -> false
        | (AfterIs | DefinitePattern | AsExpression), TokenKind.IdentifierToken ->
            if queryKeyword next && not (word next "from") then
                true
            elif
                word next "async"
                || word next "await"
                || word next "from"
                || word (next + 1) "with"
            then
                false
            else
                let follower = kind (next + 1)

                predefined follower
                || queryKeyword (next + 1)
                || ((mode = AfterIs || mode = DefinitePattern)
                    && (word (next + 1) "and" || word (next + 1) "or" || word (next + 1) "when"))
                || match follower with
                   | TokenKind.NumericLiteralToken
                   | TokenKind.StringLiteralToken
                   | TokenKind.CharacterLiteralToken
                   | TokenKind.SingleLineRawStringLiteralToken
                   | TokenKind.MultiLineRawStringLiteralToken
                   | TokenKind.Utf8StringLiteralToken
                   | TokenKind.Utf8SingleLineRawStringLiteralToken
                   | TokenKind.Utf8MultiLineRawStringLiteralToken
                   | TokenKind.TrueKeyword
                   | TokenKind.FalseKeyword
                   | TokenKind.NullKeyword
                   | TokenKind.CloseParenToken
                   | TokenKind.CloseBracketToken
                   | TokenKind.CloseBraceToken
                   | TokenKind.OpenBraceToken
                   | TokenKind.CommaToken
                   | TokenKind.SemicolonToken
                   | TokenKind.EndOfFileToken -> true
                   | _ -> false
        | (AfterIs | DefinitePattern | AsExpression), TokenKind.OpenBracketToken -> true
        | (AfterIs | DefinitePattern | AsExpression), follower -> not (expressionStart follower)
        | NewExpression, follower ->
            follower = TokenKind.OpenParenToken
            || follower = TokenKind.OpenBracketToken
            || follower = TokenKind.OpenBraceToken
        | Normal, _ -> true

    [<Struct; NoEquality; NoComparison>]
    type private TypeScan =
        val mutable Source: string
        val mutable Input: TokenInput
        val mutable Mode: TypeMode
        val mutable ExpressionHasColon: int -> bool
        val mutable QueryKeyword: int -> bool
        val mutable NullableAlways: bool
        val mutable SuffixAllowed: bool
        val mutable ArraySizes: bool
        val mutable Cursor: int
        val mutable Offset: int
        val mutable Definite: bool
        val mutable Arguments: bool
        val mutable Certainties: int
        val mutable Pointer: bool

        private new
            (
                source,
                input,
                start,
                mode,
                expressionHasColon,
                queryKeyword,
                nullableAlways,
                suffixAllowed,
                arraySizes
            ) =
            {
                Source = source
                Input = input
                Mode = mode
                ExpressionHasColon = expressionHasColon
                QueryKeyword = queryKeyword
                NullableAlways = nullableAlways
                SuffixAllowed = suffixAllowed
                ArraySizes = arraySizes
                Cursor = start
                Offset = 0
                Definite = false
                Arguments = false
                Certainties = 0
                Pointer = false
            }

        static member Any(input, start, suffixAllowed, arraySizes) =
            TypeScan(
                null,
                input,
                start,
                Normal,
                Unchecked.defaultof<_>,
                Unchecked.defaultof<_>,
                true,
                suffixAllowed,
                arraySizes
            )

        static member Qualified
            (source, input, start, mode, expressionHasColon, queryKeyword, suffixAllowed, arraySizes) =
            TypeScan(
                source,
                input,
                start,
                mode,
                expressionHasColon,
                queryKeyword,
                (mode = Normal),
                suffixAllowed,
                arraySizes
            )

    let inline private kindAt (st: byref<TypeScan>) =
        if st.Cursor >= st.Input.Count then TokenKind.EndOfFileToken
        elif st.Offset = 0 then st.Input.KindOf st.Cursor
        else residual (st.Input.KindOf st.Cursor) st.Offset

    let inline private advance (st: byref<TypeScan>) =
        st.Cursor <- st.Cursor + 1
        st.Offset <- 0

    let inline private accept (st: byref<TypeScan>) token =
        if kindAt &st = token then
            advance &st
            true
        else
            false

    let inline private qualifies (st: byref<TypeScan>) =
        st.NullableAlways
        || nullableQualifier
            st.Source
            st.Input
            st.Mode
            st.Cursor
            st.ExpressionHasColon
            st.QueryKeyword

    let private closeRun (st: byref<TypeScan>) =
        let current = kindAt &st

        if current = TokenKind.GreaterThanToken then
            advance &st
            true
        elif closing current then
            if
                st.Pointer
                && current <> TokenKind.GreaterThanGreaterThanToken
                && current <> TokenKind.GreaterThanGreaterThanGreaterThanToken
            then
                false
            else
                st.Offset <- st.Offset + 1
                true
        else
            false

    let rec private typeSyntax (st: byref<TypeScan>) depth =
        if depth > 128 then
            false
        else
            let mutable valid = true
            let certaintyStart = st.Certainties
            let mutable certain = false
            let mutable genericName = false

            if (accept &st TokenKind.RefKeyword) then
                (accept &st TokenKind.ReadOnlyKeyword) |> ignore

            if predefined ((kindAt &st)) then
                st.Definite <- true
                certain <- true
                (advance &st)
            elif (accept &st TokenKind.DelegateKeyword) then
                st.Definite <- true
                certain <- true
                valid <- (accept &st TokenKind.AsteriskToken)

                if valid && (kindAt &st) = TokenKind.IdentifierToken then
                    (advance &st)

                    if (accept &st TokenKind.OpenBracketToken) then
                        valid <- (accept &st TokenKind.IdentifierToken)

                        while valid && (accept &st TokenKind.CommaToken) do
                            valid <- (accept &st TokenKind.IdentifierToken)

                        valid <- valid && (accept &st TokenKind.CloseBracketToken)

                valid <- valid && (accept &st TokenKind.LessThanToken)
                let mutable more = valid

                while more do
                    while (kindAt &st) = TokenKind.RefKeyword
                          || (kindAt &st) = TokenKind.InKeyword
                          || (kindAt &st) = TokenKind.OutKeyword
                          || (kindAt &st) = TokenKind.ReadOnlyKeyword do
                        (advance &st)

                    valid <- (typeSyntax &st (depth + 1))

                    if valid && (accept &st TokenKind.CommaToken) then
                        ()
                    else
                        more <- false

                valid <- valid && (closeRun &st)
            elif (accept &st TokenKind.OpenParenToken) then
                let outerDefinite = st.Definite
                valid <- (typeSyntax &st (depth + 1))

                if (kindAt &st) = TokenKind.IdentifierToken then
                    (advance &st)

                let mutable count = 1

                while valid && (accept &st TokenKind.CommaToken) do
                    count <- count + 1
                    valid <- (typeSyntax &st (depth + 1))

                    if (kindAt &st) = TokenKind.IdentifierToken then
                        (advance &st)

                valid <- valid && count > 1 && (accept &st TokenKind.CloseParenToken)
                st.Definite <- outerDefinite
                st.Certainties <- certaintyStart
            elif (accept &st TokenKind.IdentifierToken) then
                let outerDefinite = st.Definite
                let mutable aliasName = (kindAt &st) = TokenKind.ColonColonToken
                let mutable qualifiers = 0

                genericName <- (kindAt &st) = TokenKind.LessThanToken

                if genericName then
                    valid <- (typeArguments &st (depth + 1))

                while valid
                      && ((kindAt &st) = TokenKind.DotToken
                          || (kindAt &st) = TokenKind.ColonColonToken) do
                    st.Certainties <- certaintyStart

                    if qualifiers > 0 then
                        aliasName <- false

                    qualifiers <- qualifiers + 1
                    (advance &st)
                    valid <- (accept &st TokenKind.IdentifierToken)

                    genericName <- valid && (kindAt &st) = TokenKind.LessThanToken

                    if genericName then
                        valid <- (typeArguments &st (depth + 1))

                if aliasName then
                    genericName <- false
                    st.Certainties <- certaintyStart

                st.Definite <- outerDefinite
            else
                valid <- false

            let mutable suffixKind = NodeKind.None
            let mutable suffix = valid && (st.SuffixAllowed || depth > 0)

            while suffix do
                if
                    (kindAt &st) = TokenKind.QuestionToken
                    && suffixKind <> NodeKind.NullableType
                    && suffixKind <> NodeKind.PointerType
                    && (depth > 0 || (qualifies &st))
                then
                    (advance &st)
                    suffixKind <- NodeKind.NullableType
                    st.Definite <- true
                    certain <- true
                elif (accept &st TokenKind.AsteriskToken) then
                    suffixKind <- NodeKind.PointerType
                    certain <- certain || (genericName && st.Certainties > certaintyStart)
                    st.Definite <- st.Definite || not st.Arguments || certain
                    st.Pointer <- true
                elif (accept &st TokenKind.OpenBracketToken) then
                    suffixKind <- NodeKind.ArrayType
                    st.Definite <- true
                    certain <- true

                    if st.ArraySizes then
                        let mutable brackets = 1

                        while brackets > 0 && (kindAt &st) <> TokenKind.EndOfFileToken do
                            if (kindAt &st) = TokenKind.OpenBracketToken then
                                brackets <- brackets + 1
                            elif (kindAt &st) = TokenKind.CloseBracketToken then
                                brackets <- brackets - 1

                            (advance &st)

                        valid <- brackets = 0
                    else
                        while (accept &st TokenKind.CommaToken) do
                            ()

                        valid <- (accept &st TokenKind.CloseBracketToken)

                    suffix <- valid
                else
                    suffix <- false

            st.Certainties <-
                certaintyStart
                + (if certain || (genericName && suffixKind = NodeKind.None) then
                       1
                   else
                       0)

            valid

    and private typeArguments (st: byref<TypeScan>) depth =
        let mutable valid = (accept &st TokenKind.LessThanToken)
        let mutable more = valid
        let mutable omitted, supplied = false, false

        while more do
            if (kindAt &st) <> TokenKind.CommaToken && not (closing ((kindAt &st))) then
                supplied <- true
                valid <- typeSyntax &st depth
            else
                omitted <- true
                st.Definite <- true
                st.Certainties <- st.Certainties + 1

            if valid && (accept &st TokenKind.CommaToken) then
                ()
            else
                more <- false

        valid && not (omitted && supplied) && (closeRun &st)

    let inline private runScan (st: byref<TypeScan>) arguments =
        ParseStats.event ParseStats.nTypeScans
        st.Arguments <- arguments

        let valid = if arguments then typeArguments &st 0 else typeSyntax &st 0

        struct (valid, st.Cursor, st.Offset, st.Definite)

    let scan (input: TokenInput) start arguments =
        if not arguments && start + 1 < input.Count then
            let k = input.KindOf start

            if k = TokenKind.IdentifierToken then
                match input.KindOf(start + 1) with
                | TokenKind.LessThanToken
                | TokenKind.DotToken
                | TokenKind.ColonColonToken
                | TokenKind.QuestionToken
                | TokenKind.AsteriskToken
                | TokenKind.OpenBracketToken ->
                    let mutable st = TypeScan.Any(input, start, true, false)
                    runScan &st false
                | _ ->
                    ParseStats.event ParseStats.nTypeScans
                    struct (true, start + 1, 0, false)
            elif predefined k then
                match input.KindOf(start + 1) with
                | TokenKind.QuestionToken
                | TokenKind.AsteriskToken
                | TokenKind.OpenBracketToken ->
                    let mutable st = TypeScan.Any(input, start, true, false)
                    runScan &st false
                | _ ->
                    ParseStats.event ParseStats.nTypeScans
                    struct (true, start + 1, 0, true)
            elif
                k = TokenKind.RefKeyword
                || k = TokenKind.DelegateKeyword
                || k = TokenKind.OpenParenToken
            then
                let mutable st = TypeScan.Any(input, start, true, false)
                runScan &st false
            else
                ParseStats.event ParseStats.nTypeScans
                struct (false, start, 0, false)
        else
            let mutable st = TypeScan.Any(input, start, true, false)
            runScan &st arguments

    let scanType source (input: TokenInput) start mode expressionHasColon queryKeyword =
        let mutable st =
            TypeScan.Qualified(
                source,
                input,
                start,
                mode,
                expressionHasColon,
                queryKeyword,
                true,
                (mode = DefinitePattern || mode = AfterIs)
            )

        runScan &st false

    let scanTypeHead (input: TokenInput) start =
        if start + 1 < input.Count then
            let k = input.KindOf start

            if k = TokenKind.IdentifierToken then
                match input.KindOf(start + 1) with
                | TokenKind.LessThanToken
                | TokenKind.DotToken
                | TokenKind.ColonColonToken ->
                    let mutable st = TypeScan.Any(input, start, false, false)
                    runScan &st false
                | _ ->
                    ParseStats.event ParseStats.nTypeScans
                    struct (true, start + 1, 0, false)
            elif predefined k then
                ParseStats.event ParseStats.nTypeScans
                struct (true, start + 1, 0, true)
            elif
                k = TokenKind.RefKeyword
                || k = TokenKind.DelegateKeyword
                || k = TokenKind.OpenParenToken
            then
                let mutable st = TypeScan.Any(input, start, false, false)
                runScan &st false
            else
                ParseStats.event ParseStats.nTypeScans
                struct (false, start, 0, false)
        else
            let mutable st = TypeScan.Any(input, start, false, false)
            runScan &st false
