module Csff.Tests.Checkout

open System
open System.IO

let findRoot (startDirectory: string) : string =
    let rec walk (directory: DirectoryInfo) =
        if isNull directory then
            invalidOp $"No .git entry above {startDirectory}."

        let entry = Path.Combine(directory.FullName, ".git")

        if File.Exists entry || Directory.Exists entry then
            directory.FullName
        else
            walk directory.Parent

    walk (DirectoryInfo startDirectory)

let root () = findRoot AppContext.BaseDirectory
