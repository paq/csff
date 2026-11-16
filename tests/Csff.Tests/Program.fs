module Csff.Tests.Program

open Expecto

[<EntryPoint>]
let main argv =
    if argv.Length > 0 && argv[0] = "--measure-performance" then
        Performance.run argv[1..]
    elif argv.Length > 0 && argv[0] = "--compare-corpus" then
        CorpusComparison.run argv[1..]
    elif argv.Length > 0 && argv[0] = "--shrink" then
        Shrink.run argv[1..]
    elif argv.Length > 0 && argv[0] = "--mutation-coverage" then
        VerifierMutationTests.run argv[1..]
    elif argv.Length > 0 && argv[0] = "--byte-roundtrip" then
        VerifierMutationTests.byteRoundTrip argv[1..]
    elif argv.Length > 0 && argv[0] = "--comment-dump" then
        VerifierMutationTests.commentDump argv[1..]
    elif argv.Length > 0 && argv[0] = "--mutation-sweep" then
        VerifierMutationTests.sweep argv[1..]
    else
        runTestsWithCLIArgs
            [ Summary ]
            argv
            (TestList(
                [
                    LexerTests.tests
                    ConformanceTests.tests
                    FrozenOutputTests.tests
                    TokenPreservationTests.tests
                    ParserTests.tests
                    PrinterTests.tests
                    UnicodeTests.tests
                    Utf8Tests.tests
                    AnonymousMethodTests.tests
                    GeneratedTests.tests
                    YamlTests.tests
                    CliTests.tests
                    ReviewRegressionTests.tests
                    VerifierMutationTests.tests
                    PropertyTests.tests
                    NativeCliTests.tests
                    PackageTests.tests
                    CorpusComparisonTests.tests
                    CorpusGateTests.tests
                ],
                Normal
            ))
