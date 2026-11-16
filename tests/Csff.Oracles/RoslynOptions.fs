namespace Csff.Conformance

open System.Collections.Generic
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

module internal RoslynOptions =

    let value =
        let options =
            CSharpParseOptions(LanguageVersion.Preview, DocumentationMode.Diagnose)

        options.WithFeatures([ KeyValuePair("FileBasedProgram", "true") ])
