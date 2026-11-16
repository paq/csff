namespace Csff.Printer

open System
open System.Collections.Generic
open System.Globalization
open System.Runtime.CompilerServices
open System.Text
open Csff.Lexer
open Csff.Parser

module Preprocessor =
    [<AbstractClass; Sealed>]
    type private Scratch =
        [<ThreadStatic; DefaultValue>]
        static val mutable private escapingTokens: TokenBuffer

        [<ThreadStatic; DefaultValue>]
        static val mutable private directiveTokens: TokenBuffer

        [<ThreadStatic; DefaultValue>]
        static val mutable private probeTokens: TokenBuffer

        [<ThreadStatic; DefaultValue>]
        static val mutable private lexicalTree: SyntaxTree

        static member EscapingTokens() =
            let current = Scratch.escapingTokens

            if isNull (box current) then
                let created = TokenBuffer()
                Scratch.escapingTokens <- created
                created
            else
                current

        static member DirectiveTokens() =
            let current = Scratch.directiveTokens

            if isNull (box current) then
                let created = TokenBuffer()
                Scratch.directiveTokens <- created
                created
            else
                current

        static member ProbeTokens() =
            let current = Scratch.probeTokens

            if isNull (box current) then
                let created = TokenBuffer()
                Scratch.probeTokens <- created
                created
            else
                current

        static member LexicalTree() =
            let current = Scratch.lexicalTree

            if isNull (box current) then
                let created = SyntaxTree()
                Scratch.lexicalTree <- created
                created
            else
                current

    type private Expression =
        | Constant of bool
        | Symbol of int
        | Not of int
        | And of int * int
        | Or of int * int
        | Equal of int * int

    type private Expressions() =
        let nodes = ResizeArray<Expression>()
        let defaults = ResizeArray<bool>()
        let names = ResizeArray<string>()
        let values = Dictionary<string, int>(StringComparer.Ordinal)
        let interned = Dictionary<struct (int * int * int), int>()

        do
            nodes.Add(Constant false)
            nodes.Add(Constant true)
            defaults.Add false
            defaults.Add true

        member _.Nodes = nodes
        member _.Names = names
        member _.Default index = defaults[index]

        member _.Add expression =
            let index = nodes.Count
            nodes.Add expression

            defaults.Add(
                match expression with
                | Constant flag -> flag
                | Symbol _ -> false
                | Not child -> not defaults[child]
                | And(left, right) -> defaults[left] && defaults[right]
                | Or(left, right) -> defaults[left] || defaults[right]
                | Equal(left, right) -> defaults[left] = defaults[right]
            )

            index

        member private this.Intern(tag: int, left: int, right: int, expression: Expression) =
            let key = struct (tag, left, right)

            match interned.TryGetValue key with
            | true, existing -> existing
            | _ ->
                let created = this.Add expression
                interned.Add(key, created)
                created

        member this.Value name =
            match values.TryGetValue name with
            | true, value -> value
            | _ ->
                let index = names.Count
                names.Add name
                let value = this.Add(Symbol index)
                values.Add(name, value)
                value

        member _.Set(name, value) = values[name] <- value

        member _.Assigned name =
            match values.TryGetValue name with
            | true, value -> value
            | _ -> 0

        member this.Negate value =
            match nodes[value] with
            | Constant flag -> if flag then 0 else 1
            | Not child -> child
            | _ -> this.Intern(0, value, 0, Not value)

        member this.Conjoin(left, right) =
            if left = 0 || right = 0 then
                0
            elif left = 1 then
                right
            elif right = 1 || left = right then
                left
            else
                match nodes[left], nodes[right] with
                | Not child, _ when child = right -> 0
                | _, Not child when child = left -> 0
                | _ -> this.Intern(1, left, right, And(left, right))

        member this.Disjoin(left, right) =
            if left = 1 || right = 1 then
                1
            elif left = 0 then
                right
            elif right = 0 || left = right then
                left
            else
                match nodes[left], nodes[right] with
                | Not child, _ when child = right -> 1
                | _, Not child when child = left -> 1
                | _ -> this.Intern(2, left, right, Or(left, right))

        member this.Choose(condition, yes, no) =
            if condition = 1 || yes = no then
                yes
            elif condition = 0 then
                no
            else
                this.Disjoin(this.Conjoin(condition, yes), this.Conjoin(this.Negate condition, no))

        member this.Compare(left, right) =
            if left = 0 then
                this.Negate right
            elif right = 0 then
                this.Negate left
            elif left = 1 then
                right
            elif right = 1 then
                left
            elif left = right then
                1
            else
                match nodes[left], nodes[right] with
                | Not child, _ when child = right -> 0
                | _, Not child when child = left -> 0
                | _ -> this.Intern(3, left, right, Equal(left, right))

    let private whitespace ch =
        ch = ' '
        || ch = '\t'
        || ch = '\v'
        || ch = '\f'
        || ch = '\u001a'
        || ch = '\ufeff'
        || Char.GetUnicodeCategory ch = UnicodeCategory.SpaceSeparator

    let private newline ch =
        ch = '\r' || ch = '\n' || ch = '\u0085' || ch = '\u2028' || ch = '\u2029'

    let private identifierStart ch =
        ch = '_'
        || match Char.GetUnicodeCategory ch with
           | UnicodeCategory.UppercaseLetter
           | UnicodeCategory.LowercaseLetter
           | UnicodeCategory.TitlecaseLetter
           | UnicodeCategory.ModifierLetter
           | UnicodeCategory.OtherLetter
           | UnicodeCategory.LetterNumber -> true
           | _ -> false

    let private identifierPart ch =
        identifierStart ch
        || match Char.GetUnicodeCategory ch with
           | UnicodeCategory.DecimalDigitNumber
           | UnicodeCategory.ConnectorPunctuation
           | UnicodeCategory.NonSpacingMark
           | UnicodeCategory.SpacingCombiningMark
           | UnicodeCategory.Format -> true
           | _ -> false

    let private classifyNewline = newline
    let private classifyWhitespace = whitespace
    let private classifyIdentifierStart = identifierStart
    let private classifyIdentifierPart = identifierPart

    module internal Classify =
        let newLine ch = classifyNewline ch
        let whitespace ch = classifyWhitespace ch
        let identifierStart ch = classifyIdentifierStart ch
        let identifierPart ch = classifyIdentifierPart ch

    let private identifier (source: string) start limit =
        let mutable text: StringBuilder = null
        let mutable position = start
        let mutable scanning = true

        while position < limit && scanning do
            let mutable ch = source[position]
            let mutable finish = position + 1

            if ch = '\\' then
                if isNull text then
                    text <- StringBuilder(16)

                    if position > start then
                        text.Append(source, start, position - start) |> ignore

                finish <- position

                if
                    position + 1 < limit
                    && (source[position + 1] = 'u' || source[position + 1] = 'U')
                then
                    let digits = if source[position + 1] = 'u' then 4 else 8
                    let mutable number = 0u
                    finish <- position + 2
                    let mutable reading = true

                    while reading && finish < limit && finish < position + 2 + digits do
                        let digit = source[finish]

                        let value =
                            if digit >= '0' && digit <= '9' then
                                int digit - int '0'
                            elif digit >= 'a' && digit <= 'f' then
                                int digit - int 'a' + 10
                            elif digit >= 'A' && digit <= 'F' then
                                int digit - int 'A' + 10
                            else
                                -1

                        if value < 0 then
                            reading <- false
                        else
                            number <- (number <<< 4) ||| uint32 value
                            finish <- finish + 1

                    ch <- if number <= 0xffffu then char number else '\ud800'

            if
                finish > position
                && (if position = start then
                        identifierStart ch
                    else
                        identifierPart ch)
            then
                if ch > '\u007f' && Char.GetUnicodeCategory ch = UnicodeCategory.Format then
                    if isNull text then
                        text <- StringBuilder(16)

                        if position > start then
                            text.Append(source, start, position - start) |> ignore
                elif not (isNull text) then
                    text.Append ch |> ignore

                position <- finish
            else
                scanning <- false

        let name =
            if not (isNull text) then text.ToString()
            elif position = start then ""
            else source.Substring(start, position - start)

        struct (name, position)

    let private expression (arena: Expressions) (source: string) start limit =
        let mutable position = start

        let skip () =
            while position < limit && whitespace source[position] do
                position <- position + 1

        let accept (value: string) =
            skip ()

            if
                position + value.Length <= limit
                && source.AsSpan(position, value.Length).SequenceEqual(value.AsSpan())
            then
                position <- position + value.Length
                true
            else
                false

        let rec primary () =
            RuntimeHelpers.EnsureSufficientExecutionStack()
            skip ()

            if
                position < limit
                && source[position] = '!'
                && not (position + 1 < limit && source[position + 1] = '=')
            then
                position <- position + 1
                arena.Negate(primary ())
            elif accept "(" then
                let result = disjunction ()
                accept ")" |> ignore
                result
            else
                let struct (name, finish) = identifier source position limit
                position <- finish

                match Boolean.TryParse name with
                | true, flag -> if flag then 1 else 0
                | _ when name.Length = 0 -> arena.Assigned ""
                | _ -> arena.Value name

        and equality () =
            let mutable result = primary ()
            let mutable scanning = true

            while scanning do
                if accept "==" then
                    result <- arena.Compare(result, primary ())
                elif accept "!=" then
                    result <- arena.Negate(arena.Compare(result, primary ()))
                else
                    scanning <- false

            result

        and conjunction () =
            let mutable result = equality ()

            while accept "&&" do
                result <- arena.Conjoin(result, equality ())

            result

        and disjunction () =
            let mutable result = conjunction ()

            while accept "||" do
                result <- arena.Disjoin(result, conjunction ())

            result

        disjunction ()

    let private solveExpression (arena: Expressions) root =
        let seen = HashSet<int>()
        let pending = Stack<int>()
        pending.Push root

        while pending.Count > 0 do
            let index = pending.Pop()

            if seen.Add index then
                match arena.Nodes[index] with
                | Not child -> pending.Push child
                | And(left, right)
                | Or(left, right)
                | Equal(left, right) ->
                    pending.Push left
                    pending.Push right
                | Constant _
                | Symbol _ -> ()

        let order = seen |> Seq.sort |> Seq.toArray
        let indices = Dictionary<int, int>(order.Length)

        for i = 0 to order.Length - 1 do
            indices.Add(order[i], i)

        let nodes =
            order
            |> Array.map (fun index ->
                match arena.Nodes[index] with
                | Not child -> Not indices[child]
                | And(left, right) -> And(indices[left], indices[right])
                | Or(left, right) -> Or(indices[left], indices[right])
                | Equal(left, right) -> Equal(indices[left], indices[right])
                | node -> node)

        let parents = Array.init nodes.Length (fun _ -> ResizeArray<int>())

        for i = 0 to nodes.Length - 1 do
            match nodes[i] with
            | Not child -> parents[child].Add i
            | And(left, right)
            | Or(left, right)
            | Equal(left, right) ->
                parents[left].Add i
                parents[right].Add i
            | _ -> ()

        let values = Array.create nodes.Length -1y
        let trail = ResizeArray<int>()
        let work = Stack<int>()
        let mutable possible = true

        let require index value =
            if possible then
                if values[index] < 0y then
                    values[index] <- value
                    trail.Add index
                    work.Push index
                elif values[index] <> value then
                    possible <- false

        let imply index =
            let value = values[index]

            match nodes[index] with
            | Constant flag -> require index (if flag then 1y else 0y)
            | Symbol _ -> ()
            | Not child ->
                if value >= 0y then
                    require child (1y - value)

                if values[child] >= 0y then
                    require index (1y - values[child])
            | And(left, right) ->
                if value = 1y then
                    require left 1y
                    require right 1y
                elif value = 0y then
                    if values[left] = 1y then
                        require right 0y

                    if values[right] = 1y then
                        require left 0y

                if values[left] = 0y || values[right] = 0y then
                    require index 0y
                elif values[left] = 1y && values[right] = 1y then
                    require index 1y
            | Or(left, right) ->
                if value = 0y then
                    require left 0y
                    require right 0y
                elif value = 1y then
                    if values[left] = 0y then
                        require right 1y

                    if values[right] = 0y then
                        require left 1y

                if values[left] = 1y || values[right] = 1y then
                    require index 1y
                elif values[left] = 0y && values[right] = 0y then
                    require index 0y
            | Equal(left, right) ->
                if value >= 0y then
                    if values[left] >= 0y then
                        require right (if value = 1y then values[left] else 1y - values[left])

                    if values[right] >= 0y then
                        require left (if value = 1y then values[right] else 1y - values[right])

                if values[left] >= 0y && values[right] >= 0y then
                    require index (if values[left] = values[right] then 1y else 0y)

        let propagate () =
            while possible && work.Count > 0 do
                let index = work.Pop()
                imply index

                for parent in parents[index] do
                    imply parent

        for i = 0 to nodes.Length - 1 do
            match nodes[i] with
            | Constant flag -> require i (if flag then 1y else 0y)
            | _ -> ()

        require indices[root] 1y

        let mutable remaining = 4096

        let rec search () =
            propagate ()

            if not possible then
                false
            else
                let mutable choice = -1
                let mutable index = nodes.Length - 1

                while choice < 0 && index >= 0 do
                    match nodes[index] with
                    | And(left, right) when values[index] = 0y ->
                        if values[left] < 0y && values[right] < 0y then
                            choice <- right
                    | Or(left, right) when values[index] = 1y ->
                        if values[left] < 0y && values[right] < 0y then
                            choice <- right
                    | Equal(left, right) when values[index] >= 0y ->
                        if values[left] < 0y && values[right] < 0y then
                            choice <- right
                    | _ -> ()

                    index <- index - 1

                if choice < 0 then
                    true
                elif remaining = 0 then
                    false
                else
                    remaining <- remaining - 1
                    let checkpoint = trail.Count

                    let reset () =
                        work.Clear()

                        for i = trail.Count - 1 downto checkpoint do
                            values[trail[i]] <- -1y

                        trail.RemoveRange(checkpoint, trail.Count - checkpoint)
                        possible <- true

                    require choice 0y

                    if search () then
                        true
                    else
                        reset ()
                        require choice 1y

                        if search () then
                            true
                        else
                            reset ()
                            false

        if search () then
            Some
                [|
                    for i = 0 to nodes.Length - 1 do
                        match nodes[i] with
                        | Symbol symbol when values[i] = 1y -> arena.Names[symbol]
                        | _ -> ()
                |]
        else
            None

    let private solve (arena: Expressions) root =
        if arena.Default root then
            Some [||]
        else
            match arena.Nodes[root] with
            | Constant _ -> None
            | Symbol symbol -> Some [| arena.Names[symbol] |]
            | _ -> solveExpression arena root

    type private Frame =
        {
            Present: int
            Parent: int
            Taken: int
            Region: bool
            ElseSeen: int
        }

    let private conditional kind =
        kind = TriviaKind.IfDirectiveTrivia
        || kind = TriviaKind.ElifDirectiveTrivia
        || kind = TriviaKind.ElseDirectiveTrivia
        || kind = TriviaKind.EndIfDirectiveTrivia

    type private Scan =
        {
            OpensFromCode: bool
            Closes: bool
            ReopensAfterClose: bool
        }

    type private SpanMode =
        | Fixed of struct (int * int) array
        | PerConfiguration of Scan array

    let internal directiveLines (text: string) : struct (int * int) array =
        let lines = ResizeArray<struct (int * int)>()
        let mutable index = 0
        let mutable inComment = false

        let addDirective hash =
            let mutable probe = hash + 1

            while probe < text.Length && whitespace text[probe] do
                probe <- probe + 1

            let start = probe

            while probe < text.Length && text[probe] >= 'a' && text[probe] <= 'z' do
                probe <- probe + 1

            let boundary = probe >= text.Length || not (identifierPart text[probe])

            if boundary then
                let keyword = text.AsSpan(start, probe - start)

                if keyword.SequenceEqual("if".AsSpan()) then
                    lines.Add(struct (hash, 0))
                elif keyword.SequenceEqual("elif".AsSpan()) then
                    lines.Add(struct (hash, 1))
                elif keyword.SequenceEqual("else".AsSpan()) then
                    lines.Add(struct (hash, 2))
                elif keyword.SequenceEqual("endif".AsSpan()) then
                    lines.Add(struct (hash, 3))

        let span = text.AsSpan()

        while index < text.Length do
            let relEnd = span.Slice(index).IndexOfAny("\r\n\u0085\u2028\u2029".AsSpan())
            let lineEnd = if relEnd < 0 then text.Length else index + relEnd

            if not inComment && span.Slice(index, lineEnd - index).IndexOfAny('#', '/') < 0 then
                index <- lineEnd
            else
                let mutable probe = index
                let mutable prefixing = true
                let mutable hash = -1

                if inComment then
                    let mutable leading = probe

                    while leading < lineEnd && whitespace text[leading] do
                        leading <- leading + 1

                    if leading < lineEnd && text[leading] = '#' then
                        hash <- leading

                    let mutable close = probe
                    let mutable state = 0

                    while state = 0 do
                        if close >= lineEnd then
                            state <- 2
                        elif text[close] = '*' && close + 1 < lineEnd && text[close + 1] = '/' then
                            state <- 1
                        else
                            close <- close + 1

                    if state = 1 then
                        inComment <- false
                        probe <- close + 2
                    else
                        while probe < lineEnd && whitespace text[probe] do
                            probe <- probe + 1

                        prefixing <- false

                while prefixing do
                    if probe < lineEnd && whitespace text[probe] then
                        probe <- probe + 1
                    elif probe + 1 < lineEnd && text[probe] = '/' && text[probe + 1] = '*' then
                        let mutable close = probe + 2
                        let mutable state = 0

                        while state = 0 do
                            if close >= lineEnd then
                                state <- 2
                            elif
                                text[close] = '*' && close + 1 < lineEnd && text[close + 1] = '/'
                            then
                                state <- 1
                            else
                                close <- close + 1

                        if state = 1 then
                            probe <- close + 2
                        else
                            inComment <- true
                            prefixing <- false
                    else
                        prefixing <- false

                if hash >= 0 then
                    addDirective hash

                if probe <> hash && probe < lineEnd && text[probe] = '#' then
                    addDirective probe

                index <- lineEnd

            while index < text.Length && newline text[index] do
                index <- index + 1

        lines.ToArray()

    let private walk
        (source: string)
        (items: Trivia array)
        mode
        (arena: Expressions)
        (needOrdinals: bool)
        branch
        skipped
        state
        =
        let frames = ResizeArray<Frame>()
        let mutable active = 1

        let ordinals =
            if needOrdinals then
                let dict = Dictionary<int, int>()
                let mutable count = -1

                for struct (position, kind) in directiveLines source do
                    if kind < 3 then
                        count <- count + 1
                        dict[position] <- count

                dict
            else
                null

        let mutable ordinal = -1
        let mutable range = 0
        let mutable entered = false
        let mutable hiddenWhen = 0

        let ranges =
            match mode with
            | Fixed ranges -> ranges
            | PerConfiguration _ -> [||]

        let mutable hiddenNow = 0

        let advance (scan: Scan) withCode =
            let fromCode =
                if withCode && scan.OpensFromCode then
                    arena.Conjoin(arena.Negate hiddenNow, active)
                else
                    0

            let fromComment =
                if scan.Closes && not scan.ReopensAfterClose then
                    0
                else
                    hiddenNow

            hiddenNow <- arena.Disjoin(fromCode, fromComment)

        for index = 0 to items.Length - 1 do
            let item = items[index]
            state item.Start active

            let visible =
                match mode with
                | PerConfiguration scans ->
                    advance scans[2 * index] true
                    arena.Negate hiddenNow
                | Fixed _ ->
                    while range < ranges.Length
                          && (let struct (_, finish) = ranges[range] in finish <= item.Start) do
                        range <- range + 1
                        entered <- false

                    if
                        range < ranges.Length
                        && (let struct (start, _) = ranges[range] in start < item.Start)
                    then
                        if not entered then
                            hiddenWhen <- active
                            entered <- true

                        arena.Negate hiddenWhen
                    else
                        1

            let limit = item.Start + item.Length
            let mutable argument = item.Start + 1

            while argument < limit && whitespace source[argument] do
                argument <- argument + 1

            while argument < limit && identifierPart source[argument] do
                argument <- argument + 1

            while argument < limit && whitespace source[argument] do
                argument <- argument + 1

            match item.Kind with
            | TriviaKind.IfDirectiveTrivia ->
                ordinal <-
                    if not (isNull ordinals) then
                        match ordinals.TryGetValue item.Start with
                        | true, known -> known
                        | _ -> ordinal + 1
                    else
                        ordinal + 1

                let condition = expression arena source argument limit
                let next = arena.Conjoin(active, condition)
                skipped (arena.Conjoin(visible, arena.Conjoin(active, arena.Negate condition)))

                frames.Add
                    {
                        Present = visible
                        Parent = active
                        Taken = condition
                        Region = false
                        ElseSeen = 0
                    }

                active <- arena.Conjoin(active, arena.Disjoin(arena.Negate visible, condition))
                branch ordinal (arena.Conjoin(next, visible))
            | TriviaKind.RegionDirectiveTrivia ->
                frames.Add
                    {
                        Present = visible
                        Parent = active
                        Taken = 0
                        Region = true
                        ElseSeen = 0
                    }
            | TriviaKind.ElifDirectiveTrivia
            | TriviaKind.ElseDirectiveTrivia
            | TriviaKind.EndIfDirectiveTrivia
            | TriviaKind.EndRegionDirectiveTrivia ->
                if
                    item.Kind = TriviaKind.ElifDirectiveTrivia
                    || item.Kind = TriviaKind.ElseDirectiveTrivia
                then
                    ordinal <-
                        if not (isNull ordinals) then
                            match ordinals.TryGetValue item.Start with
                            | true, known -> known
                            | _ -> ordinal + 1
                        else
                            ordinal + 1

                let condition =
                    if item.Kind = TriviaKind.ElifDirectiveTrivia then
                        expression arena source argument limit
                    else
                        1

                let mutable remaining = visible
                let mutable top = frames.Count - 1

                while top >= 0 && remaining <> 0 do
                    let frame = frames[top]
                    let matched = arena.Conjoin(remaining, frame.Present)
                    remaining <- arena.Conjoin(remaining, arena.Negate frame.Present)

                    match item.Kind with
                    | TriviaKind.EndRegionDirectiveTrivia when frame.Region ->
                        frames[top] <-
                            { frame with
                                Present = arena.Conjoin(frame.Present, arena.Negate matched)
                            }
                    | TriviaKind.EndIfDirectiveTrivia when not frame.Region ->
                        active <- arena.Choose(matched, frame.Parent, active)

                        frames[top] <-
                            { frame with
                                Present = arena.Conjoin(frame.Present, arena.Negate matched)
                            }
                    | TriviaKind.ElifDirectiveTrivia
                    | TriviaKind.ElseDirectiveTrivia when not frame.Region ->
                        let matched = arena.Conjoin(matched, arena.Negate frame.ElseSeen)

                        let next =
                            arena.Conjoin(
                                frame.Parent,
                                arena.Conjoin(arena.Negate frame.Taken, condition)
                            )

                        skipped (
                            arena.Conjoin(
                                matched,
                                arena.Conjoin(
                                    frame.Parent,
                                    arena.Conjoin(arena.Negate frame.Taken, arena.Negate condition)
                                )
                            )
                        )

                        active <- arena.Choose(matched, next, active)

                        frames[top] <-
                            { frame with
                                Taken =
                                    arena.Disjoin(frame.Taken, arena.Conjoin(matched, condition))
                                ElseSeen =
                                    if item.Kind = TriviaKind.ElseDirectiveTrivia then
                                        arena.Disjoin(frame.ElseSeen, matched)
                                    else
                                        frame.ElseSeen
                            }

                        branch ordinal (arena.Conjoin(next, matched))
                    | _ -> ()

                    if frames[top].Present = 0 then
                        frames.RemoveAt top

                    top <- top - 1
            | TriviaKind.DefineDirectiveTrivia
            | TriviaKind.UndefDirectiveTrivia when active <> 0 ->
                let active = arena.Conjoin(active, visible)
                let struct (name, finish) = identifier source argument limit

                if active <> 0 then
                    let isBoolean =
                        let raw = source.AsSpan(argument, finish - argument)
                        raw.SequenceEqual("true".AsSpan()) || raw.SequenceEqual("false".AsSpan())

                    let effectiveName = if finish = argument || isBoolean then "" else name

                    let defined = item.Kind = TriviaKind.DefineDirectiveTrivia

                    let value =
                        if active = 1 then
                            if defined then 1 else 0
                        else
                            let previous =
                                if effectiveName.Length = 0 then
                                    arena.Assigned ""
                                else
                                    arena.Value effectiveName

                            if defined then
                                arena.Disjoin(previous, active)
                            else
                                arena.Conjoin(previous, arena.Negate active)

                    arena.Set(effectiveName, value)
            | _ -> ()

            match mode with
            | PerConfiguration scans -> advance scans[2 * index + 1] false
            | Fixed _ -> ()

        state source.Length active

    let private comment kind =
        kind = TriviaKind.SingleLineCommentTrivia
        || kind = TriviaKind.MultiLineCommentTrivia
        || kind = TriviaKind.SingleLineDocumentationCommentTrivia
        || kind = TriviaKind.MultiLineDocumentationCommentTrivia

    let private block kind =
        kind = TriviaKind.MultiLineCommentTrivia
        || kind = TriviaKind.MultiLineDocumentationCommentTrivia

    let private plain kind =
        kind = TriviaKind.WhitespaceTrivia
        || kind = TriviaKind.EndOfLineTrivia
        || comment kind

    let private openers = [| '/'; '"'; '\'' |]

    let private opener (source: string) (region: Trivia) =
        region.Kind = TriviaKind.DisabledTextTrivia
        && source.IndexOfAny(openers, region.Start, region.Length) >= 0

    let private escapingWith (source: string) (tree: SyntaxTree) (tokens: TokenBuffer voption) =
        let mutable scratch = tokens
        let mutable index = 0
        let mutable escapes = false

        while not escapes && index < tree.TriviaCount do
            let region = tree.Trivia index

            if opener source region then
                let buffer =
                    match scratch with
                    | ValueSome existing -> existing
                    | ValueNone ->
                        let created = Scratch.EscapingTokens()
                        scratch <- ValueSome created
                        created

                let finish = region.Start + region.Length
                Lexer.lexRange source region.Start finish buffer
                let mutable i = 0

                while not escapes && i < buffer.TriviaCount do
                    let item = buffer.Trivia i

                    if
                        not (plain item.Kind)
                        || (block item.Kind && item.Start + item.Length = finish)
                    then
                        escapes <- true

                    i <- i + 1

                i <- 0

                while not escapes && i < buffer.TokenCount do
                    let token = buffer.Token i

                    if token.Length > 0 && token.End = finish then
                        escapes <- true

                    i <- i + 1

            index <- index + 1

        escapes

    let private interpolated (tree: SyntaxTree) =
        let mutable index = tree.LexerBuffer.TriviaCount
        let mutable found = false

        while not found && index < tree.TriviaCount do
            found <- not (plain (tree.Trivia index).Kind)
            index <- index + 1

        found

    let internal pathDependentWith
        (source: string)
        (tree: SyntaxTree)
        (tokens: TokenBuffer voption)
        =
        if interpolated tree then
            true
        else
            let mutable index = 0
            let mutable found = false

            while not found && index < tree.TriviaCount do
                found <- opener source (tree.Trivia index)
                index <- index + 1

            found && escapingWith source tree tokens

    let internal pathDependent (source: string) (tree: SyntaxTree) =
        pathDependentWith source tree ValueNone

    let private directives (source: string) (tree: SyntaxTree) =
        let classify (item: Trivia) =
            if item.Kind <> TriviaKind.BadDirectiveTrivia then
                item
            else
                let limit = item.Start + item.Length
                let mutable start = item.Start + 1

                while start < limit && whitespace source[start] do
                    start <- start + 1

                let mutable finish = start

                while finish < limit && identifierPart source[finish] do
                    finish <- finish + 1

                let span = source.AsSpan(start, finish - start)

                let kind =
                    if span.SequenceEqual("elif".AsSpan()) then
                        TriviaKind.ElifDirectiveTrivia
                    elif span.SequenceEqual("else".AsSpan()) then
                        TriviaKind.ElseDirectiveTrivia
                    elif span.SequenceEqual("endif".AsSpan()) then
                        TriviaKind.EndIfDirectiveTrivia
                    elif span.SequenceEqual("endregion".AsSpan()) then
                        TriviaKind.EndRegionDirectiveTrivia
                    else
                        item.Kind

                { item with Kind = kind }

        let collected = ResizeArray<Trivia>(16)

        for i = 0 to tree.TriviaCount - 1 do
            let item = classify (tree.Trivia i)

            if
                conditional item.Kind
                || item.Kind = TriviaKind.DefineDirectiveTrivia
                || item.Kind = TriviaKind.UndefDirectiveTrivia
                || item.Kind = TriviaKind.RegionDirectiveTrivia
                || item.Kind = TriviaKind.EndRegionDirectiveTrivia
            then
                collected.Add item

        let items = collected.ToArray()

        let items =
            if tree.TriviaCount = tree.LexerBuffer.TriviaCount then
                items
            else
                items
                |> Array.distinctBy (fun item -> item.Start)
                |> Array.sortBy (fun item -> item.Start)

        if pathDependent source tree then
            let active = source.ToCharArray()

            for item in items do
                if conditional item.Kind then
                    for i = item.Start to item.Start + item.Length - 1 do
                        if not (newline active[i]) then
                            active[i] <- ' '

            let buffer = Scratch.DirectiveTokens()
            let baseBuf = tree.LexerBuffer
            let tokHint = baseBuf.TokenCount + (baseBuf.TokenCount >>> 2) + 64
            let trivHint = baseBuf.TriviaCount + (baseBuf.TriviaCount >>> 2) + 64
            Lexer.lexWithHinted [||] tokHint trivHint (String active) buffer

            let mutable escape = false
            let mutable itemIndex = 0

            for i = 0 to buffer.TokenCount - 1 do
                let token = buffer.Token i

                while itemIndex < items.Length && items[itemIndex].Start <= token.Start do
                    itemIndex <- itemIndex + 1

                if
                    itemIndex < items.Length
                    && token.Length > 0
                    && items[itemIndex].Start < token.End
                then
                    escape <- true

            let fixedRanges () =
                let hidden = ResizeArray<struct (int * int)>()

                for i = 0 to buffer.TriviaCount - 1 do
                    let item = buffer.Trivia i

                    if comment item.Kind then
                        hidden.Add(struct (item.Start, item.Start + item.Length))

                for i = 0 to buffer.TokenCount - 1 do
                    let token = buffer.Token i
                    hidden.Add(struct (token.Start, token.End))

                hidden |> Seq.sortBy (fun struct (start, _) -> start) |> Seq.toArray

            if escape then
                items, Fixed(fixedRanges ())
            else
                let scratch = Scratch.ProbeTokens()

                let codeEnd start finish =
                    if start >= finish then
                        0
                    elif source.AsSpan(start, finish - start).IndexOf('#') < 0 then
                        Lexer.lexRange source start finish scratch
                        let mutable result = 0

                        for i = 0 to scratch.TriviaCount - 1 do
                            let item = scratch.Trivia i

                            if block item.Kind && item.Start + item.Length = finish then
                                let closed =
                                    item.Length >= 4
                                    && source[finish - 2] = '*'
                                    && source[finish - 1] = '/'

                                if not closed then
                                    result <- 1

                        for i = 0 to scratch.TokenCount - 1 do
                            let token = scratch.Token i

                            if token.Length > 0 && token.End = finish then
                                result <- 2

                        result
                    else
                        let probeChars = source.Substring(start, finish - start).ToCharArray()

                        for i = 0 to probeChars.Length - 1 do
                            if probeChars[i] = '#' then
                                let mutable word = i + 1

                                while word < probeChars.Length && whitespace probeChars[word] do
                                    word <- word + 1

                                if
                                    word < probeChars.Length
                                    && probeChars[word] >= 'a'
                                    && probeChars[word] <= 'z'
                                then
                                    probeChars[word] <- '_'

                        let probe = String probeChars
                        Lexer.lexRange probe 0 probe.Length scratch
                        let opaque = ResizeArray<struct (int * int)>()

                        for i = 0 to scratch.TriviaCount - 1 do
                            let item = scratch.Trivia i

                            if comment item.Kind then
                                opaque.Add(struct (item.Start, item.Start + item.Length))

                        for i = 0 to scratch.TokenCount - 1 do
                            let token = scratch.Token i

                            if token.Length > 0 then
                                opaque.Add(struct (token.Start, token.End))

                        let spans = opaque.ToArray()
                        Array.sortInPlaceBy (fun struct (first, _) -> first) spans
                        let mutable spanIndex = 0

                        let covered position =
                            while spanIndex < spans.Length
                                  && (let struct (_, last) = spans[spanIndex] in last <= position) do
                                spanIndex <- spanIndex + 1

                            spanIndex < spans.Length
                            && (let struct (first, _) = spans[spanIndex] in first <= position)

                        let buffer = probe.ToCharArray()
                        let raw = source.AsSpan(start, finish - start)
                        let mutable index = 0

                        while index < buffer.Length do
                            let mutable lead = index

                            while lead < buffer.Length && whitespace raw[lead] do
                                lead <- lead + 1

                            let directive =
                                lead < buffer.Length && raw[lead] = '#' && not (covered lead)

                            while index < buffer.Length && not (newline buffer[index]) do
                                if directive then
                                    buffer[index] <- ' '

                                index <- index + 1

                            if index < buffer.Length then
                                index <- index + 1

                        let text = String buffer
                        let finish = text.Length
                        Lexer.lexRange text 0 finish scratch
                        let mutable result = 0

                        for i = 0 to scratch.TriviaCount - 1 do
                            let item = scratch.Trivia i

                            if block item.Kind && item.Start + item.Length = finish then
                                let closed =
                                    item.Length >= 4
                                    && text[finish - 2] = '*'
                                    && text[finish - 1] = '/'

                                if not closed then
                                    result <- 1

                        for i = 0 to scratch.TokenCount - 1 do
                            let token = scratch.Token i

                            if token.Length > 0 && token.End = finish then
                                result <- 2

                        result

                let scan start finish directiveLine =
                    let fromCode = if directiveLine then 0 else codeEnd start finish

                    let closer =
                        if finish - start >= 2 then
                            source.IndexOf("*/", start, finish - start, StringComparison.Ordinal)
                        else
                            -1

                    let after = if closer < 0 then 0 else codeEnd (closer + 2) finish

                    if fromCode = 2 || after = 2 then
                        escape <- true

                    {
                        OpensFromCode = fromCode = 1
                        Closes = closer >= 0
                        ReopensAfterClose = after = 1
                    }

                let scans = Array.zeroCreate<Scan>(items.Length * 2)
                let mutable previous = 0

                for index = 0 to items.Length - 1 do
                    let item = items[index]
                    scans[2 * index] <- scan previous item.Start false
                    scans[2 * index + 1] <- scan item.Start (item.Start + item.Length) true
                    previous <- item.Start + item.Length

                if escape then
                    items, Fixed(fixedRanges ())
                else
                    items, PerConfiguration scans
        else
            items, Fixed [||]

    let private selectWith
        (source: string)
        (tree: SyntaxTree)
        (avoids: int array)
        (completed: string array array)
        =
        let items, mode = directives source tree

        if
            items
            |> Array.exists (fun item -> item.Kind = TriviaKind.IfDirectiveTrivia)
            |> not
        then
            [||]
        else
            let arena = Expressions()
            let branches = ResizeArray<int>()
            let mutable permitted = 1

            walk
                source
                items
                mode
                arena
                (avoids.Length > 0)
                (fun ordinal root ->
                    branches.Add root

                    if avoids.Length > 0 && Array.contains ordinal avoids then
                        permitted <- arena.Conjoin(permitted, arena.Negate root))
                ignore
                (fun _ _ -> ())

            let result = ResizeArray<string array>()
            let unique = HashSet<string>(StringComparer.Ordinal)
            let covered = HashSet<int>()

            for symbols in completed do
                let defined = HashSet<string>(symbols, StringComparer.Ordinal)
                let values = Array.zeroCreate<bool> arena.Nodes.Count

                for i = 0 to arena.Nodes.Count - 1 do
                    values[i] <-
                        match arena.Nodes[i] with
                        | Constant flag -> flag
                        | Symbol symbol -> defined.Contains arena.Names[symbol]
                        | Not child -> not values[child]
                        | And(left, right) -> values[left] && values[right]
                        | Or(left, right) -> values[left] || values[right]
                        | Equal(left, right) -> values[left] = values[right]

                for branch in branches do
                    if values[branch] then
                        covered.Add branch |> ignore

            for branch in branches do
                match
                    if covered.Contains branch then
                        None
                    else
                        solve arena (arena.Conjoin(branch, permitted))
                with
                | Some symbols when symbols.Length > 0 && unique.Add(String.Join("\000", symbols)) ->
                    result.Add symbols
                | _ -> ()

            result.ToArray()

    let private select (source: string) (tree: SyntaxTree) = selectWith source tree [||] [||]

    let internal conditioned (tree: SyntaxTree) = tree.HasIfDirective

    let internal initialSymbolSets (source: string) (tree: SyntaxTree) =
        if conditioned tree then select source tree else [||]

    let private discoveryNeededWith
        (source: string)
        (tree: SyntaxTree)
        (tokens: TokenBuffer voption)
        =
        if
            not (source.Contains '"')
            && not (source.Contains("/*", StringComparison.Ordinal))
        then
            false
        elif pathDependentWith source tree tokens then
            true
        else
            let mutable lines: struct (int * int) array = null
            let mutable next = 0

            let crosses start finish =
                if
                    finish - start <= 2
                    || not (source.AsSpan(start + 1, finish - start - 1).Contains('#'))
                then
                    false
                else
                    if isNull lines then
                        lines <- directiveLines source

                    while next < lines.Length && (let struct (pos, _) = lines[next] in pos <= start) do
                        next <- next + 1

                    next < lines.Length && (let struct (pos, _) = lines[next] in pos < finish)

            let buffer = tree.LexerBuffer
            let mutable found = false
            let mutable index = 0

            while not found && index < buffer.TokenCount do
                let token = buffer.Token index
                found <- crosses token.Start token.End
                index <- index + 1

            next <- 0
            index <- 0

            while not found && index < buffer.TriviaCount do
                let item = buffer.Trivia index

                if block item.Kind then
                    found <- crosses item.Start (item.Start + item.Length)

                index <- index + 1

            found

    let private discoverSymbolSets
        (source: string)
        (tree: SyntaxTree)
        (selected: string array array)
        : string array array =
        if not (conditioned tree) then
            [||]
        else if
            not (source.Contains '"')
            && not (source.Contains("/*", StringComparison.Ordinal))
        then
            selected
        else
            let result = ResizeArray<string array>(selected)
            let pending = Queue<string array>()
            let unique = HashSet<string>(StringComparer.Ordinal)
            let reached = HashSet<struct (int * bool)>()
            let seenReach = HashSet<struct (int * uint64)>()

            let hashExpr (arena: Expressions) (hashes: ResizeArray<uint64>) (root: int) =
                while hashes.Count < arena.Nodes.Count do
                    let idx = hashes.Count

                    let h =
                        match arena.Nodes[idx] with
                        | Constant false -> 0x9e3779b97f4a7c15UL
                        | Constant true -> 0xc2b2ae3d27d4eb4fUL
                        | Symbol sym ->
                            let name = arena.Names[sym]
                            let mutable hv = 14695981039346656037UL

                            for c in name do
                                hv <- (hv ^^^ uint64 c) * 1099511628211UL

                            (hv ^^^ 1UL) * 1099511628211UL
                        | Not child -> (hashes[child] ^^^ 0x517cc1b727220a95UL) * 1099511628211UL
                        | And(left, right) ->
                            let mutable hv = 0x2545F4914F6CDD1DUL
                            hv <- (hv ^^^ hashes[left]) * 1099511628211UL
                            (hv ^^^ hashes[right]) * 1099511628211UL
                        | Or(left, right) ->
                            let mutable hv = 0x94D049BB133111EBUL
                            hv <- (hv ^^^ hashes[left]) * 1099511628211UL
                            (hv ^^^ hashes[right]) * 1099511628211UL
                        | Equal(left, right) ->
                            let mutable hv = 0xBF58476D1CE4E5B9UL
                            hv <- (hv ^^^ hashes[left]) * 1099511628211UL
                            (hv ^^^ hashes[right]) * 1099511628211UL

                    hashes.Add h

                hashes[root]

            let lines = directiveLines source

            let lexical = Scratch.LexicalTree()
            let mutable baseItems: Trivia array = null

            let enqueue symbols =
                let key = String.Join("\000", Array.sort symbols)

                if unique.Add key then
                    pending.Enqueue symbols

                    if symbols.Length > 0 then
                        result.Add symbols

            unique.Add "" |> ignore
            pending.Enqueue [||]

            for symbols in selected do
                unique.Add(String.Join("\000", Array.sort symbols)) |> ignore
                pending.Enqueue symbols

            for i = 0 to tree.LexerBuffer.TriviaCount - 1 do
                let item = tree.LexerBuffer.Trivia i

                if conditional item.Kind then
                    reached.Add(struct (item.Start, true)) |> ignore

            while pending.Count > 0 do
                let symbols = pending.Dequeue()

                let currentTree =
                    if symbols.Length = 0 && not tree.LexerBuffer.HasSeededSymbols then
                        tree
                    else
                        lexical.Reset()
                        let baseBuf = tree.LexerBuffer
                        let tokHint = baseBuf.TokenCount + (baseBuf.TokenCount >>> 3) + 64
                        let trivHint = baseBuf.TriviaCount + (baseBuf.TriviaCount >>> 3) + 64
                        Lexer.lexWithHinted symbols tokHint trivHint source lexical.LexerBuffer
                        lexical.CopyLexicalTrivia()
                        lexical

                let buffer = currentTree.LexerBuffer
                let crossingStarts = ResizeArray<int>()
                let mutable next = 0

                for i = 0 to buffer.TokenCount - 1 do
                    let token = buffer.Token i
                    let start = token.Start

                    while next < lines.Length && (let struct (pos, _) = lines[next] in pos <= start) do
                        next <- next + 1

                    if
                        next < lines.Length
                        && (let struct (pos, _) = lines[next] in pos < token.End)
                        && (token.Kind = TokenKind.StringLiteralToken
                            || token.Kind = TokenKind.Utf8StringLiteralToken
                            || token.Kind = TokenKind.InterpolatedStringToken
                            || token.Kind = TokenKind.MultiLineRawStringLiteralToken
                            || token.Kind = TokenKind.Utf8MultiLineRawStringLiteralToken)
                    then
                        crossingStarts.Add start

                let mutable nextTrivia = 0

                for i = 0 to buffer.TriviaCount - 1 do
                    let item = buffer.Trivia i

                    if block item.Kind then
                        let start = item.Start
                        let finish = item.Start + item.Length

                        while nextTrivia < lines.Length
                              && (let struct (pos, _) = lines[nextTrivia] in pos <= start) do
                            nextTrivia <- nextTrivia + 1

                        if
                            nextTrivia < lines.Length
                            && (let struct (pos, _) = lines[nextTrivia] in pos < finish)
                        then
                            crossingStarts.Add start

                let crossingBranches =
                    if crossingStarts.Count = 0 then
                        null
                    else
                        crossingStarts.Sort()
                        let branches = HashSet<int>()
                        let stack = ResizeArray<int>()
                        let mutable markedDepth = 0
                        let mutable nextCrossing = 0

                        let markBefore limit =
                            if
                                nextCrossing < crossingStarts.Count
                                && crossingStarts[nextCrossing] < limit
                            then
                                while nextCrossing < crossingStarts.Count
                                      && crossingStarts[nextCrossing] < limit do
                                    nextCrossing <- nextCrossing + 1

                                for j = markedDepth to stack.Count - 1 do
                                    branches.Add stack[j] |> ignore

                                markedDepth <- stack.Count

                        for i = 0 to buffer.TriviaCount - 1 do
                            let item = buffer.Trivia i
                            markBefore item.Start

                            match item.Kind with
                            | TriviaKind.IfDirectiveTrivia -> stack.Add item.Start
                            | TriviaKind.ElifDirectiveTrivia
                            | TriviaKind.ElseDirectiveTrivia when stack.Count > 0 ->
                                stack.RemoveAt(stack.Count - 1)
                                markedDepth <- min markedDepth stack.Count
                                stack.Add item.Start
                            | TriviaKind.EndIfDirectiveTrivia when stack.Count > 0 ->
                                stack.RemoveAt(stack.Count - 1)
                                markedDepth <- min markedDepth stack.Count
                            | _ -> ()

                        markBefore source.Length
                        branches

                let items, mode = directives source currentTree

                let diffStart =
                    if symbols.Length = 0 then
                        baseItems <- items
                        Int32.MaxValue
                    elif isNull baseItems then
                        0
                    else
                        let shared = min items.Length baseItems.Length
                        let mutable k = 0

                        while k < shared
                              && items[k].Start = baseItems[k].Start
                              && items[k].Kind = baseItems[k].Kind do
                            k <- k + 1

                        if k = items.Length && k = baseItems.Length then
                            Int32.MaxValue
                        elif k < items.Length && k < baseItems.Length then
                            min items[k].Start baseItems[k].Start
                        elif k < items.Length then
                            items[k].Start
                        else
                            baseItems[k].Start

                if diffStart < Int32.MaxValue && symbols.Length > 0 then
                    let altArena = Expressions()
                    let altHashes = ResizeArray<uint64>(64)
                    let affected = HashSet<int>()
                    let freshFalse = HashSet<int>()
                    let mutable altPos = 0

                    let altGoal edge root =
                        if edge then
                            let fresh = reached.Add(struct (altPos, true))
                            let condHash = hashExpr altArena altHashes root
                            let changed = seenReach.Add(struct (altPos, condHash))

                            if fresh || changed then
                                affected.Add altPos |> ignore

                                match solve altArena root with
                                | Some extra ->
                                    if fresh then
                                        enqueue extra
                                    else
                                        let key = String.Join("\000", Array.sort (Array.copy extra))

                                        if not (unique.Contains key) then
                                            let targetPos = altPos
                                            let checkTree = SyntaxTree()
                                            let baseBuf = tree.LexerBuffer

                                            let tokHint =
                                                baseBuf.TokenCount + (baseBuf.TokenCount >>> 3) + 64

                                            let trivHint =
                                                baseBuf.TriviaCount
                                                + (baseBuf.TriviaCount >>> 3)
                                                + 64

                                            Lexer.lexWithHinted
                                                extra
                                                tokHint
                                                trivHint
                                                source
                                                checkTree.LexerBuffer

                                            checkTree.CopyLexicalTrivia()

                                            if
                                                not checkTree.LexerBuffer.HasMalformedTrivia
                                                || currentTree.LexerBuffer.HasMalformedTrivia
                                            then
                                                let checkItems, checkMode =
                                                    directives source checkTree

                                                let checkArena = Expressions()

                                                for name in extra do
                                                    checkArena.Set(name, 1)

                                                let mutable checkPos = 0
                                                let mutable verified = false

                                                walk
                                                    source
                                                    checkItems
                                                    checkMode
                                                    checkArena
                                                    false
                                                    (fun _ checkRoot ->
                                                        if
                                                            checkPos = targetPos
                                                            && checkArena.Default checkRoot
                                                        then
                                                            verified <- true)
                                                    (fun _ -> ())
                                                    (fun start _ -> checkPos <- start)

                                                if verified then
                                                    enqueue extra
                                | _ -> ()
                        elif
                            not (isNull crossingBranches)
                            && crossingBranches.Contains altPos
                            && reached.Add(struct (altPos, false))
                        then
                            freshFalse.Add altPos |> ignore

                            match solve altArena root with
                            | Some extra -> enqueue extra
                            | _ -> ()

                    walk
                        source
                        items
                        mode
                        altArena
                        false
                        (fun _ root -> altGoal true root)
                        (altGoal false)
                        (fun start _ -> altPos <- start)

                    if affected.Count > 0 || freshFalse.Count > 0 then
                        let arena = Expressions()

                        for name in symbols do
                            arena.Set(name, 1)

                        let mutable position = 0

                        let goal edge root =
                            if
                                (edge && affected.Contains position)
                                || (not edge && freshFalse.Contains position)
                            then
                                match solve arena root with
                                | Some extra ->
                                    enqueue (Array.append symbols extra |> Array.distinct)
                                | _ -> ()

                        walk
                            source
                            items
                            mode
                            arena
                            false
                            (fun _ root -> goal true root)
                            (goal false)
                            (fun start _ -> position <- start)
                elif symbols.Length = 0 || not (isNull crossingBranches) then
                    let arena = Expressions()

                    for name in symbols do
                        arena.Set(name, 1)

                    let arenaHashes = if symbols.Length = 0 then ResizeArray<uint64>(64) else null
                    let mutable position = 0

                    let goal edge root =
                        if edge && not (isNull arenaHashes) then
                            seenReach.Add(struct (position, hashExpr arena arenaHashes root))
                            |> ignore

                        let freshReach = edge && reached.Add(struct (position, true))

                        if
                            freshReach
                            || (not edge
                                && not (isNull crossingBranches)
                                && crossingBranches.Contains position
                                && reached.Add(struct (position, false)))
                        then
                            match solve arena root with
                            | Some extra -> enqueue (Array.append symbols extra |> Array.distinct)
                            | _ -> ()

                    walk
                        source
                        items
                        mode
                        arena
                        false
                        (fun _ root -> goal true root)
                        (goal false)
                        (fun start _ -> position <- start)

            result.ToArray()

    let internal alternativeSets
        (source: string)
        (tree: SyntaxTree)
        (avoids: int array)
        (completed: string array array)
        : string array array =
        if not (conditioned tree) then
            [||]
        else
            selectWith source tree avoids completed

    let internal independentFixedClassesWith
        (source: string)
        (tree: SyntaxTree)
        (sets: string array array)
        (tokens: TokenBuffer voption)
        =
        let tailClass =
            tree.TokenCount = 5
            && (tree.Token 0).Kind = TokenKind.ClassKeyword
            && (tree.Token 1).Kind = TokenKind.IdentifierToken
            && (tree.Token 2).Kind = TokenKind.OpenBraceToken
            && (tree.Token 3).Kind = TokenKind.CloseBraceToken
            && (tree.Token 4).Kind = TokenKind.EndOfFileToken

        if
            (tree.TokenCount <> 1 && not tailClass)
            || sets.Length < 2
            || sets |> Array.exists (fun set -> set.Length <> 1)
            || source.AsSpan().IndexOfAny('\u0085', '\u2028', '\u2029') >= 0
        then
            false
        else
            let remaining =
                HashSet<string>(sets |> Array.map (fun set -> set[0]), StringComparer.Ordinal)

            let mutable scratch = tokens
            let mutable opened = false
            let mutable body = false
            let mutable eligible = true
            let mutable index = 0
            let mutable lastRegionEnd = 0

            while eligible && index < tree.TriviaCount do
                let item = tree.Trivia index
                let limit = item.Start + item.Length

                match item.Kind with
                | TriviaKind.IfDirectiveTrivia when not opened ->
                    let mutable argument = item.Start + 1

                    while argument < limit && whitespace source[argument] do
                        argument <- argument + 1

                    while argument < limit && identifierPart source[argument] do
                        argument <- argument + 1

                    let keywordEnd = argument

                    while argument < limit && whitespace source[argument] do
                        argument <- argument + 1

                    let struct (name, finish) = identifier source argument limit

                    let mutable rest = finish

                    while rest < limit && (whitespace source[rest] || newline source[rest]) do
                        rest <- rest + 1

                    if
                        argument > keywordEnd
                        && rest = limit
                        && name.Length > 0
                        && (Char.IsLetter name[0] || name[0] = '_')
                        && remaining.Remove name
                    then
                        opened <- true
                        body <- false
                    else
                        eligible <- false
                | TriviaKind.DisabledTextTrivia when opened && not body ->
                    let buffer =
                        match scratch with
                        | ValueSome existing -> existing
                        | ValueNone ->
                            let created = Scratch.EscapingTokens()
                            scratch <- ValueSome created
                            created

                    Lexer.lexRange source item.Start limit buffer

                    let empty =
                        buffer.TokenCount = 5
                        && (buffer.Token 3).Kind = TokenKind.CloseBraceToken
                        && (buffer.Token 4).Kind = TokenKind.EndOfFileToken

                    let stringField =
                        buffer.TokenCount = 10
                        && (buffer.Token 3).Kind = TokenKind.StringKeyword
                        && (buffer.Token 4).Kind = TokenKind.IdentifierToken
                        && (buffer.Token 5).Kind = TokenKind.EqualsToken
                        && (buffer.Token 6).Kind = TokenKind.StringLiteralToken
                        && (buffer.Token 7).Kind = TokenKind.SemicolonToken
                        && (buffer.Token 8).Kind = TokenKind.CloseBraceToken
                        && (buffer.Token 9).Kind = TokenKind.EndOfFileToken
                        && (let literal = buffer.Token 6 in

                            source.AsSpan(literal.Start, literal.Length).IndexOfAny('\r', '\n') < 0)

                    body <-
                        (empty || stringField)
                        && (buffer.Token 0).Kind = TokenKind.ClassKeyword
                        && (buffer.Token 1).Kind = TokenKind.IdentifierToken
                        && (buffer.Token 2).Kind = TokenKind.OpenBraceToken

                    let mutable i = 0

                    while body && i < buffer.TriviaCount do
                        let kind = (buffer.Trivia i).Kind

                        body <-
                            kind = TriviaKind.WhitespaceTrivia || kind = TriviaKind.EndOfLineTrivia

                        i <- i + 1

                    eligible <- body
                | TriviaKind.EndIfDirectiveTrivia when opened && body ->
                    eligible <-
                        source
                            .AsSpan(item.Start, item.Length)
                            .Trim()
                            .SequenceEqual("#endif".AsSpan())

                    opened <- false
                    lastRegionEnd <- limit
                | TriviaKind.SingleLineCommentTrivia when
                    tailClass && not opened && remaining.Count = 0
                    ->
                    eligible <-
                        item.Start >= lastRegionEnd
                        && limit <= (tree.Token 0).Start
                        && not (
                            source
                                .AsSpan(item.Start, item.Length)
                                .Contains("csff-ignore".AsSpan(), StringComparison.Ordinal)
                        )
                | TriviaKind.WhitespaceTrivia
                | TriviaKind.EndOfLineTrivia -> ()
                | _ -> eligible <- false

                index <- index + 1

            eligible
            && not opened
            && remaining.Count = 0
            && (not tailClass || (tree.Token 0).Start >= lastRegionEnd)

    let internal independentFixedClasses
        (source: string)
        (tree: SyntaxTree)
        (sets: string array array)
        (tokens: TokenBuffer)
        =
        independentFixedClassesWith source tree sets (ValueSome tokens)

    let internal symbolSetsWithInitial
        (source: string)
        (tree: SyntaxTree)
        (tokens: TokenBuffer voption)
        : struct (string array array * string array array * bool * bool) =
        let selected = initialSymbolSets source tree
        let independent = independentFixedClassesWith source tree selected tokens

        let discovery =
            conditioned tree
            && (source.Contains '"' || source.Contains("/*", StringComparison.Ordinal))
            && not independent
            && discoveryNeededWith source tree tokens

        let sets =
            if discovery then
                discoverSymbolSets source tree selected
            else
                selected

        struct (selected, sets, independent, discovery)

    let symbolSets (source: string) (tree: SyntaxTree) : string array array =
        let struct (_, sets, _, _) = symbolSetsWithInitial source tree ValueNone
        sets
