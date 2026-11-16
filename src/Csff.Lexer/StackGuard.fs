namespace Csff.Lexer

open System
open System.Runtime.CompilerServices

module StackGuard =
    let Unproven = IntPtr.MaxValue

    let inline private slot (anchor: byref<int>) =
        Unsafe.ByteOffset(&Unsafe.NullRef<int>(), &anchor)

    let inline entry () =
        let mutable here = 0
        slot &here

    let exhausted () = raise (InsufficientExecutionStackException())

    let inline proven (floor: nativeint) =
        let mutable here = 0
        let depth = slot &here

        if depth < floor then
            if not (RuntimeHelpers.TryEnsureSufficientExecutionStack()) then
                exhausted ()

            depth
        else
            floor
