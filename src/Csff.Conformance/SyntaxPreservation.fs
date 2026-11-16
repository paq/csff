namespace Csff.Conformance

open System
open System.Diagnostics
open System.Threading
open Csff.Printer

module SyntaxPreservation =
    module Probe =
        let enabled = Environment.GetEnvironmentVariable "CSFF_DECLINES" = "1"

        let note (filePath: string) (symbols: string array) =
            if enabled then
                Console.Error.WriteLine(
                    String.Format("verification-decline symbols={0} {1}", symbols.Length, filePath)
                )

    module Stats =
        let enabled = Environment.GetEnvironmentVariable "CSFF_VERIFY_STATS" = "1"

        let internal elapsed = Array.zeroCreate<int64> 24

        let internal counts = Array.zeroCreate<int64> 24

        let internal histogram = Array.zeroCreate<int64> 65

        let tVerify = 0
        let tLexical = 1
        let tComments = 2
        let tNormalizeDefault = 3
        let tSymbolSets = 4
        let tCombined = 5
        let tLoopDefault = 6
        let tLoopRest = 7
        let tConfigNormalize = 8
        let tConfigEquivalent = 9
        let tConfigDirective = 10
        let tConfigFallback = 11
        let tConfigScreen = 12
        let tSeparators = 13

        let nVerify = 0
        let nLexicallyProven = 1
        let nFellThrough = 2
        let nConfigsRun = 3
        let nDefaultDeclined = 4
        let nLaterDeclinedAlone = 5
        let nLaterViolatedAlone = 6
        let nCombinedTried = 7
        let nCombinedOffered = 8
        let nCombinedProved = 9
        let nConfigDeclined = 10
        let nCombinedRefused = 11
        let nCommentViolation = 12
        let nConfigScreenProven = 13
        let nSeparatorsProven = 14

        let names =
            [|
                "verify total"
                "lexical proof"
                "comment comparison"
                "normalize, default"
                "symbol sets"
                "combined witness"
                "loop, default configuration"
                "loop, later configurations"
                "  of which normalize"
                "  of which equivalence walk"
                "  of which directive comparison"
                "  of which fallback rewrite"
                "  of which lexical screen"
                "separator-only proof"
            |]

        let eventNames =
            [|
                "files verified"
                "settled by the lexical proof"
                "fell through to the loop"
                "later configurations run"
                "default configuration declined"
                "only a later configuration declined"
                "only a later configuration violated"
                "combined witness attempted"
                "combined witness offered"
                "combined witness proved the file"
                "later configurations that declined"
                "combined witness declined, sets rerun"
                "comment violations"
                "configurations the lexical screen proved"
                "settled by the separator-only proof"
                "norm witness=None"
                "norm witness.SortedUsings"
                "norm witness.SortedModifiers"
                "norm witness.ChangedTrailingCommas"
                "norm witness.ReindentedRawStrings"
            |]

        let inline internal mark () =
            if enabled then Stopwatch.GetTimestamp() else 0L

        let inline internal lapse (region: int) (start: int64) =
            if enabled then
                Interlocked.Add(&elapsed[region], Stopwatch.GetTimestamp() - start) |> ignore

        let inline internal event (kind: int) =
            if enabled then
                Interlocked.Increment(&counts[kind]) |> ignore

        let inline internal bump (kind: int) (by: int) =
            if enabled then
                Interlocked.Add(&counts[kind], int64 by) |> ignore

        let inline internal sets (count: int) =
            if enabled then
                let slot = if count > 64 then 64 else count
                Interlocked.Increment(&histogram[slot]) |> ignore

        let report () =
            let frequency = float Stopwatch.Frequency
            let out = Console.Error
            out.WriteLine "verify-stats regions (seconds)"

            for index in 0 .. names.Length - 1 do
                out.WriteLine(
                    String.Format(
                        "verify-stats region {0,-32} {1:F4}",
                        names[index],
                        float elapsed[index] / frequency
                    )
                )

            for index in 0 .. eventNames.Length - 1 do
                out.WriteLine(
                    String.Format(
                        "verify-stats count {0,-38} {1}",
                        eventNames[index],
                        counts[index]
                    )
                )

            for index in 0 .. histogram.Length - 1 do
                if histogram[index] > 0L then
                    out.WriteLine(
                        String.Format("verify-stats sets {0} {1}", index, histogram[index])
                    )

        do
            if enabled then
                AppDomain.CurrentDomain.ProcessExit.Add(fun _ -> report ())

    [<RequireQualifiedAccess>]
    type Verification =
        | Proven
        | Violation of message: string
        | Unprovable of reason: string

    let refusal (verification: Verification) : Result<unit, string> =
        match verification with
        | Verification.Proven -> Ok()
        | Verification.Violation message -> Error message
        | Verification.Unprovable reason -> Error("unprovable: " + reason)

    type Checker(?sharedAfter: Csff.Parser.SyntaxTree, ?sharedOwnedBefore: Csff.Parser.SyntaxTree) =
        let tokens =
            TokenPreservation.Checker(
                ?sharedAfter = sharedAfter,
                ?sharedOwnedBefore = sharedOwnedBefore
            )

        member internal _.ParseWork = tokens.ParseWork

        member internal _.ResetParseWork() = tokens.ResetParseWork()

        member private this.VerifyAfterLexical
            (
                options: PrinterOptions,
                filePath: string,
                source: string,
                formatted: string,
                native: bool,
                sourceTree: Csff.Parser.SyntaxTree,
                witness: TransformationWitness
            ) =
            if false then
                Verification.Proven
            else
                Stats.event Stats.nFellThrough
                let commentStart = Stats.mark ()

                let struct (comments, commentMismatch) =
                    tokens.CommentsPreservedDirect(source, formatted, native, sourceTree)

                Stats.lapse Stats.tComments commentStart

                if not comments then
                    Stats.event Stats.nCommentViolation

                    Verification.Violation(
                        String.Format(
                            "{0}: formatting changed a comment ({1}).",
                            filePath,
                            commentMismatch
                        )
                    )
                else
                    let separatorStart = Stats.mark ()

                    let separatorsProven =
                        native
                        && tokens.SeparatorsOnlyPreservedDirect(source, formatted, witness, options)

                    Stats.lapse Stats.tSeparators separatorStart

                    if separatorsProven then
                        Stats.event Stats.nSeparatorsProven
                        Verification.Proven
                    else
                        this.VerifyAfterSeparators(
                            options,
                            filePath,
                            source,
                            formatted,
                            native,
                            sourceTree,
                            witness
                        )

        member private _.VerifyAfterSeparators
            (
                options: PrinterOptions,
                filePath: string,
                source: string,
                formatted: string,
                native: bool,
                sourceTree: Csff.Parser.SyntaxTree,
                witness: TransformationWitness
            ) =
            if native then
                tokens.PinDefaultConditionalPair(source, formatted, sourceTree)

            try
                let normalizeStart = Stats.mark ()

                let defaultExpected =
                    tokens.NormalizeDirect(
                        options,
                        source,
                        formatted,
                        sourceTree,
                        witness,
                        Array.empty,
                        true
                    )

                Stats.lapse Stats.tNormalizeDefault normalizeStart
                let setsStart = Stats.mark ()

                let selected = tokens.SymbolSets defaultExpected

                Stats.lapse Stats.tSymbolSets setsStart
                Stats.sets selected.Length

                if Stats.enabled && selected.Length = 0 then
                    if
                        not witness.SortedUsings
                        && not witness.SortedModifiers
                        && not witness.ChangedTrailingCommas
                        && not witness.ReindentedRawStrings
                    then
                        Stats.event 15

                    if witness.SortedUsings then
                        Stats.event 16

                    if witness.SortedModifiers then
                        Stats.event 17

                    if witness.ChangedTrailingCommas then
                        Stats.event 18

                    if witness.ReindentedRawStrings then
                        Stats.event 19

                let combined =
                    if selected.Length > 32 then
                        Stats.event Stats.nCombinedTried
                        let combinedStart = Stats.mark ()

                        let offered = tokens.CombinedIndependentSymbols(defaultExpected, formatted)

                        Stats.lapse Stats.tCombined combinedStart

                        if offered.IsSome then
                            Stats.event Stats.nCombinedOffered

                        offered
                    else
                        None

                let mutable violation = None
                let mutable unproven = None
                let provenConfigs = ResizeArray<struct (string array * string)>()

                if native && selected.Length > 0 then
                    tokens.BeginDisabledDeferral true

                let check (configurations: string array array) =
                    for symbols in configurations do
                        if violation.IsNone then
                            let mutable fastEquivalent = false

                            if symbols.Length > 0 then
                                Stats.event Stats.nConfigsRun

                            let mutable expected: string = null

                            if symbols.Length = 0 then
                                fastEquivalent <-
                                    native && tokens.FastEquivalent(defaultExpected, formatted)

                                if fastEquivalent then
                                    provenConfigs.Add(struct (Array.empty, null))
                                else
                                    expected <- tokens.NormalizedFallback defaultExpected
                            else
                                let canSeed =
                                    (let mutable ok = true
                                     let mutable s = 0

                                     while ok && s < symbols.Length do
                                         let sym = symbols[s]

                                         ok <-
                                             sym.Length > 0
                                             && sym <> "true"
                                             && sym <> "false"
                                             && (Char.IsLetter sym[0] || sym[0] = '_')

                                         let mutable c = 1

                                         while ok && c < sym.Length do
                                             let ch = sym[c]
                                             ok <- Char.IsLetterOrDigit ch || ch = '_'
                                             c <- c + 1

                                         s <- s + 1

                                     ok)

                                if canSeed then
                                    let screenStart = Stats.mark ()

                                    let screened =
                                        native
                                        && tokens.LexicallyPreservedPair(
                                            source,
                                            formatted,
                                            symbols = symbols
                                        )

                                    Stats.lapse Stats.tConfigScreen screenStart

                                    if screened then
                                        Stats.event Stats.nConfigScreenProven
                                        fastEquivalent <- true
                                        provenConfigs.Add(struct (symbols, null))
                                    else
                                        let commentStart = Stats.mark ()

                                        let struct (comments, commentMismatch) =
                                            tokens.CommentsPreservedPair(
                                                source,
                                                formatted,
                                                symbols,
                                                native,
                                                true
                                            )

                                        Stats.lapse Stats.tComments commentStart

                                        if not comments then
                                            Stats.event Stats.nCommentViolation
                                            fastEquivalent <- true

                                            violation <-
                                                Some(
                                                    String.Format(
                                                        "{0}: formatting changed a comment ({1}).",
                                                        filePath,
                                                        commentMismatch
                                                    )
                                                )
                                        else
                                            let configNormalizeStart = Stats.mark ()

                                            let selected =
                                                tokens.NormalizeDirect(
                                                    options,
                                                    source,
                                                    formatted,
                                                    Unchecked.defaultof<Csff.Parser.SyntaxTree>,
                                                    witness,
                                                    symbols,
                                                    true
                                                )

                                            Stats.lapse Stats.tConfigNormalize configNormalizeStart

                                            let configEquivalentStart = Stats.mark ()

                                            fastEquivalent <-
                                                native
                                                && (if Object.ReferenceEquals(selected, source) then
                                                        tokens.FastEquivalentUnrewritten(
                                                            selected,
                                                            formatted
                                                        )
                                                    else
                                                        tokens.FastEquivalent(selected, formatted))

                                            Stats.lapse
                                                Stats.tConfigEquivalent
                                                configEquivalentStart

                                            if fastEquivalent then
                                                provenConfigs.Add(struct (symbols, null))

                                            let configFallbackStart = Stats.mark ()

                                            if not fastEquivalent then
                                                expected <- tokens.NormalizedFallback selected

                                            Stats.lapse Stats.tConfigFallback configFallbackStart
                                else
                                    let prefix =
                                        symbols
                                        |> Array.map (fun symbol -> "#define " + symbol + "\n")
                                        |> String.concat ""

                                    let prefixed = prefix + formatted
                                    let prefixedSource = prefix + source

                                    let screenStart = Stats.mark ()

                                    let screened =
                                        native
                                        && tokens.LexicallyPreservedPair(prefixedSource, prefixed)

                                    Stats.lapse Stats.tConfigScreen screenStart

                                    if screened then
                                        Stats.event Stats.nConfigScreenProven
                                        fastEquivalent <- true
                                        provenConfigs.Add(struct (symbols, prefix))
                                    else
                                        tokens.SetDisabledDeferralPrefix prefix.Length

                                        try
                                            let commentStart = Stats.mark ()

                                            let struct (comments, commentMismatch) =
                                                tokens.CommentsPreservedPair(
                                                    prefixedSource,
                                                    prefixed,
                                                    Array.empty,
                                                    native,
                                                    true
                                                )

                                            Stats.lapse Stats.tComments commentStart

                                            if not comments then
                                                Stats.event Stats.nCommentViolation
                                                fastEquivalent <- true

                                                violation <-
                                                    Some(
                                                        String.Format(
                                                            "{0}: formatting changed a comment ({1}).",
                                                            filePath,
                                                            commentMismatch
                                                        )
                                                    )
                                            else
                                                let configNormalizeStart = Stats.mark ()

                                                let selected =
                                                    tokens.NormalizeDirect(
                                                        options,
                                                        prefixedSource,
                                                        prefixed,
                                                        Unchecked.defaultof<Csff.Parser.SyntaxTree>,
                                                        witness,
                                                        Array.empty,
                                                        true
                                                    )

                                                Stats.lapse
                                                    Stats.tConfigNormalize
                                                    configNormalizeStart

                                                if
                                                    not (
                                                        selected.StartsWith(
                                                            prefix,
                                                            StringComparison.Ordinal
                                                        )
                                                    )
                                                then
                                                    invalidOp
                                                        "Syntax verification changed its temporary symbol definitions."

                                                let configEquivalentStart = Stats.mark ()

                                                fastEquivalent <-
                                                    native
                                                    && (if
                                                            Object.ReferenceEquals(
                                                                selected,
                                                                prefixedSource
                                                            )
                                                        then
                                                            tokens.FastEquivalentUnrewritten(
                                                                selected,
                                                                prefixed
                                                            )
                                                        else
                                                            tokens.FastEquivalent(
                                                                selected,
                                                                prefixed
                                                            ))

                                                Stats.lapse
                                                    Stats.tConfigEquivalent
                                                    configEquivalentStart

                                                if fastEquivalent then
                                                    provenConfigs.Add(struct (symbols, prefix))

                                                let configFallbackStart = Stats.mark ()

                                                if not fastEquivalent then
                                                    let rewritten =
                                                        tokens.NormalizedFallback selected

                                                    expected <- rewritten.Substring(prefix.Length)

                                                Stats.lapse
                                                    Stats.tConfigFallback
                                                    configFallbackStart
                                        finally
                                            tokens.SetDisabledDeferralPrefix 0

                            if not fastEquivalent then
                                if symbols.Length > 0 then
                                    Stats.event Stats.nConfigDeclined

                                let configuration =
                                    if symbols.Length = 0 then
                                        "default configuration"
                                    else
                                        "symbols: " + String.Join(", ", symbols)

                                if native && unproven.IsNone then
                                    unproven <-
                                        Some(
                                            String.Format(
                                                "{0}: formatting could not be proven to preserve the C# syntax ({1}); the file is unchanged.",
                                                filePath,
                                                configuration
                                            )
                                        )

                                let directiveStart = Stats.mark ()

                                let directiveLine =
                                    TriviaPreservation.differenceWith symbols expected formatted

                                Stats.lapse Stats.tConfigDirective directiveStart

                                Probe.note filePath symbols

                                if not (isNull directiveLine) then
                                    violation <-
                                        Some(
                                            String.Format(
                                                "{0}: formatting changed a preprocessor directive line ({1}; {2}).",
                                                filePath,
                                                configuration,
                                                directiveLine
                                            )
                                        )

                let defaultStart = Stats.mark ()
                check [| [||] |]
                Stats.lapse Stats.tLoopDefault defaultStart
                let defaultDeclined = unproven.IsSome

                if defaultDeclined then
                    Stats.event Stats.nDefaultDeclined

                let violationBeforeRest = violation.IsSome
                let restStart = Stats.mark ()

                let deferredBeforeRest = tokens.DeferredDisabledSpanCount
                let provenBeforeRest = provenConfigs.Count

                match combined with
                | Some symbols ->
                    check [| symbols |]

                    if violation.IsNone && unproven.IsSome && not defaultDeclined then
                        Stats.event Stats.nCombinedRefused
                        unproven <- None
                        tokens.TruncateDeferredDisabledSpans deferredBeforeRest

                        if provenConfigs.Count > provenBeforeRest then
                            provenConfigs.RemoveRange(
                                provenBeforeRest,
                                provenConfigs.Count - provenBeforeRest
                            )

                        check selected
                    elif violation.IsNone && unproven.IsNone then
                        Stats.event Stats.nCombinedProved
                | None -> check selected

                Stats.lapse Stats.tLoopRest restStart

                if
                    native
                    && violation.IsNone
                    && unproven.IsNone
                    && not (
                        tokens.AllDeferredDisabledSpansProvenBy(
                            options,
                            witness,
                            formatted,
                            provenConfigs
                        )
                    )
                then
                    unproven <-
                        Some(
                            String.Format(
                                "{0}: formatting could not be proven to preserve the C# syntax (default configuration); the file is unchanged.",
                                filePath
                            )
                        )

                if not defaultDeclined && unproven.IsSome then
                    Stats.event Stats.nLaterDeclinedAlone

                if not violationBeforeRest && violation.IsSome then
                    Stats.event Stats.nLaterViolatedAlone

                match violation, unproven with
                | Some message, _ -> Verification.Violation message
                | None, Some reason -> Verification.Unprovable reason
                | None, None -> Verification.Proven
            finally
                tokens.EndDisabledDeferral()

                if native then
                    tokens.ClearPinnedConditionalPair()

        member private this.Verify
            (
                options: PrinterOptions,
                filePath: string,
                source: string,
                formatted: string,
                native: bool,
                sourceTree: Csff.Parser.SyntaxTree,
                witness: TransformationWitness
            ) =
            Stats.event Stats.nVerify
            let lexicalStart = Stats.mark ()

            let lexicallyProven =
                native
                && tokens.LexicallyPreservedDirect(source, formatted, sourceTree, true, witness)

            Stats.lapse Stats.tLexical lexicalStart

            if lexicallyProven then
                Stats.event Stats.nLexicallyProven
                Verification.Proven
            else
                this.VerifyAfterLexical(
                    options,
                    filePath,
                    source,
                    formatted,
                    native,
                    sourceTree,
                    witness
                )

        member this.DecideDirectSpan
            (
                options: PrinterOptions,
                filePath: string,
                source: string,
                formatted: ReadOnlySpan<char>,
                sourceTree: Csff.Parser.SyntaxTree,
                witness: TransformationWitness
            ) =
            let start = Stats.mark ()
            Stats.event Stats.nVerify
            let lexicalStart = Stats.mark ()

            let lexicallyProven =
                tokens.LexicallyPreservedDirectSpan(source, formatted, sourceTree, true, witness)

            Stats.lapse Stats.tLexical lexicalStart

            let decision =
                if lexicallyProven then
                    Stats.event Stats.nLexicallyProven
                    Verification.Proven
                else
                    Stats.event Stats.nFellThrough
                    let mutable cachedFormatted: string = null
                    let commentStart = Stats.mark ()

                    let struct (comments, commentMismatch) =
                        tokens.CommentsPreservedDirectSpan(
                            source,
                            formatted,
                            &cachedFormatted,
                            true,
                            sourceTree
                        )

                    Stats.lapse Stats.tComments commentStart

                    if not comments then
                        Stats.event Stats.nCommentViolation

                        Verification.Violation(
                            String.Format(
                                "{0}: formatting changed a comment ({1}).",
                                filePath,
                                commentMismatch
                            )
                        )
                    else
                        let separatorStart = Stats.mark ()

                        let separatorsProven =
                            tokens.SeparatorsOnlyPreservedDirectSpan(
                                source,
                                formatted,
                                &cachedFormatted,
                                witness,
                                options
                            )

                        Stats.lapse Stats.tSeparators separatorStart

                        if separatorsProven then
                            Stats.event Stats.nSeparatorsProven
                            Verification.Proven
                        else
                            let formattedStr =
                                if isNull cachedFormatted then
                                    let s = String formatted
                                    tokens.BindLexedFormatted s
                                    s
                                else
                                    cachedFormatted

                            this.VerifyAfterSeparators(
                                options,
                                filePath,
                                source,
                                formattedStr,
                                true,
                                sourceTree,
                                witness
                            )

            Stats.lapse Stats.tVerify start
            decision

        member this.DecideDirect
            (
                options: PrinterOptions,
                filePath: string,
                source: string,
                formatted: string,
                sourceTree: Csff.Parser.SyntaxTree,
                witness: TransformationWitness
            ) =
            let start = Stats.mark ()

            let decision =
                this.Verify(options, filePath, source, formatted, true, sourceTree, witness)

            Stats.lapse Stats.tVerify start
            decision

        member this.Decide
            (
                options: PrinterOptions,
                filePath: string,
                source: string,
                formatted: string,
                ?sourceTree: Csff.Parser.SyntaxTree,
                ?witness: TransformationWitness
            ) =
            let parsedTree =
                match sourceTree with
                | Some parsed -> parsed
                | None -> Unchecked.defaultof<Csff.Parser.SyntaxTree>

            let w =
                match witness with
                | Some v -> v
                | None -> TransformationWitness.Searched

            this.DecideDirect(options, filePath, source, formatted, parsedTree, w)

        member this.AdjudicateDecision
            (options: PrinterOptions, filePath: string, source: string, formatted: string)
            =
            this.Verify(
                options,
                filePath,
                source,
                formatted,
                false,
                Unchecked.defaultof<Csff.Parser.SyntaxTree>,
                TransformationWitness.Searched
            )

        member this.Check
            (
                options: PrinterOptions,
                filePath: string,
                source: string,
                formatted: string,
                ?sourceTree: Csff.Parser.SyntaxTree,
                ?witness: TransformationWitness
            ) =
            this.Decide(
                options,
                filePath,
                source,
                formatted,
                ?sourceTree = sourceTree,
                ?witness = witness
            )
            |> refusal

        member this.Adjudicate
            (options: PrinterOptions, filePath: string, source: string, formatted: string)
            =
            this.AdjudicateDecision(options, filePath, source, formatted) |> refusal

        member _.ReleasePooledBuffers() = tokens.ReleasePooledBuffers()
