namespace Csff.Lexer

open System
open System.Runtime.CompilerServices
open System.Runtime.InteropServices

module internal Keywords =
    let lengthsByFirstCharacter: uint16 array =
        let table = Array.zeroCreate 128

        let add length (firsts: string) =
            for ch in firsts do
                table[int ch] <- table[int ch] ||| (1us <<< length)

        add 2 "adi"
        add 3 "finort"
        add 4 "bceglntuv"
        add 5 "bcefstuw"
        add 6 "deoprstu"
        add 7 "cdfpv"
        add 8 "acdeiorv"
        add 9 "_inpu"
        add 10 "_s"
        table

    let inline pack2 (c0: char) (c1: char) : uint32 =
        if BitConverter.IsLittleEndian then
            uint32 c0 ||| (uint32 c1 <<< 16)
        else
            (uint32 c0 <<< 16) ||| uint32 c1

    let inline pack4 (c0: char) (c1: char) (c2: char) (c3: char) : uint64 =
        if BitConverter.IsLittleEndian then
            uint64 c0 ||| (uint64 c1 <<< 16) ||| (uint64 c2 <<< 32) ||| (uint64 c3 <<< 48)
        else
            (uint64 c0 <<< 48) ||| (uint64 c1 <<< 32) ||| (uint64 c2 <<< 16) ||| uint64 c3

    let inline load2 (first: byref<char>) (offset: int) : uint32 =
        Unsafe.ReadUnaligned<uint32>(&Unsafe.As<char, byte>(&Unsafe.Add(&first, offset)))

    let inline load4 (first: byref<char>) (offset: int) : uint64 =
        Unsafe.ReadUnaligned<uint64>(&Unsafe.As<char, byte>(&Unsafe.Add(&first, offset)))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    let kind (source: ReadOnlySpan<char>) start length =
        if uint32 start > uint32 source.Length || source.Length - start < length then
            TokenKind.IdentifierToken
        else
            let first = &Unsafe.AsRef(&MemoryMarshal.GetReference source)

            match length with
            | 2 ->
                let w = load2 &first start

                if w = pack2 'i' 'f' then TokenKind.IfKeyword
                elif w = pack2 'i' 'n' then TokenKind.InKeyword
                elif w = pack2 'i' 's' then TokenKind.IsKeyword
                elif w = pack2 'a' 's' then TokenKind.AsKeyword
                elif w = pack2 'd' 'o' then TokenKind.DoKeyword
                else TokenKind.IdentifierToken
            | 3 ->
                match Unsafe.Add(&first, start) with
                | 'f' ->
                    if load2 &first (start + 1) = pack2 'o' 'r' then
                        TokenKind.ForKeyword
                    else
                        TokenKind.IdentifierToken
                | 'i' ->
                    if load2 &first (start + 1) = pack2 'n' 't' then
                        TokenKind.IntKeyword
                    else
                        TokenKind.IdentifierToken
                | 'n' ->
                    if load2 &first (start + 1) = pack2 'e' 'w' then
                        TokenKind.NewKeyword
                    else
                        TokenKind.IdentifierToken
                | 'o' ->
                    if load2 &first (start + 1) = pack2 'u' 't' then
                        TokenKind.OutKeyword
                    else
                        TokenKind.IdentifierToken
                | 'r' ->
                    if load2 &first (start + 1) = pack2 'e' 'f' then
                        TokenKind.RefKeyword
                    else
                        TokenKind.IdentifierToken
                | 't' ->
                    if load2 &first (start + 1) = pack2 'r' 'y' then
                        TokenKind.TryKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | 4 ->
                let w = load4 &first start

                match Unsafe.Add(&first, start) with
                | 'b' ->
                    if w = pack4 'b' 'o' 'o' 'l' then TokenKind.BoolKeyword
                    elif w = pack4 'b' 'y' 't' 'e' then TokenKind.ByteKeyword
                    elif w = pack4 'b' 'a' 's' 'e' then TokenKind.BaseKeyword
                    else TokenKind.IdentifierToken
                | 'c' ->
                    if w = pack4 'c' 'h' 'a' 'r' then TokenKind.CharKeyword
                    elif w = pack4 'c' 'a' 's' 'e' then TokenKind.CaseKeyword
                    else TokenKind.IdentifierToken
                | 'e' ->
                    if w = pack4 'e' 'l' 's' 'e' then TokenKind.ElseKeyword
                    elif w = pack4 'e' 'n' 'u' 'm' then TokenKind.EnumKeyword
                    else TokenKind.IdentifierToken
                | 'g' ->
                    if w = pack4 'g' 'o' 't' 'o' then
                        TokenKind.GotoKeyword
                    else
                        TokenKind.IdentifierToken
                | 'l' ->
                    if w = pack4 'l' 'o' 'n' 'g' then TokenKind.LongKeyword
                    elif w = pack4 'l' 'o' 'c' 'k' then TokenKind.LockKeyword
                    else TokenKind.IdentifierToken
                | 'n' ->
                    if w = pack4 'n' 'u' 'l' 'l' then
                        TokenKind.NullKeyword
                    else
                        TokenKind.IdentifierToken
                | 't' ->
                    if w = pack4 't' 'r' 'u' 'e' then TokenKind.TrueKeyword
                    elif w = pack4 't' 'h' 'i' 's' then TokenKind.ThisKeyword
                    else TokenKind.IdentifierToken
                | 'u' ->
                    if w = pack4 'u' 'i' 'n' 't' then
                        TokenKind.UIntKeyword
                    else
                        TokenKind.IdentifierToken
                | 'v' ->
                    if w = pack4 'v' 'o' 'i' 'd' then
                        TokenKind.VoidKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | 5 ->
                let w = load4 &first (start + 1)

                match Unsafe.Add(&first, start) with
                | 'b' ->
                    if w = pack4 'r' 'e' 'a' 'k' then
                        TokenKind.BreakKeyword
                    else
                        TokenKind.IdentifierToken
                | 'c' ->
                    if w = pack4 'l' 'a' 's' 's' then TokenKind.ClassKeyword
                    elif w = pack4 'o' 'n' 's' 't' then TokenKind.ConstKeyword
                    elif w = pack4 'a' 't' 'c' 'h' then TokenKind.CatchKeyword
                    else TokenKind.IdentifierToken
                | 'e' ->
                    if w = pack4 'v' 'e' 'n' 't' then
                        TokenKind.EventKeyword
                    else
                        TokenKind.IdentifierToken
                | 'f' ->
                    if w = pack4 'a' 'l' 's' 'e' then TokenKind.FalseKeyword
                    elif w = pack4 'l' 'o' 'a' 't' then TokenKind.FloatKeyword
                    elif w = pack4 'i' 'x' 'e' 'd' then TokenKind.FixedKeyword
                    else TokenKind.IdentifierToken
                | 's' ->
                    if w = pack4 'b' 'y' 't' 'e' then TokenKind.SByteKeyword
                    elif w = pack4 'h' 'o' 'r' 't' then TokenKind.ShortKeyword
                    else TokenKind.IdentifierToken
                | 't' ->
                    if w = pack4 'h' 'r' 'o' 'w' then
                        TokenKind.ThrowKeyword
                    else
                        TokenKind.IdentifierToken
                | 'u' ->
                    if w = pack4 's' 'i' 'n' 'g' then TokenKind.UsingKeyword
                    elif w = pack4 'l' 'o' 'n' 'g' then TokenKind.ULongKeyword
                    else TokenKind.IdentifierToken
                | 'w' ->
                    if w = pack4 'h' 'i' 'l' 'e' then
                        TokenKind.WhileKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | 6 ->
                let w = load4 &first (start + 1)
                let last = Unsafe.Add(&first, start + 5)

                match Unsafe.Add(&first, start) with
                | 'd' ->
                    if w = pack4 'o' 'u' 'b' 'l' && last = 'e' then
                        TokenKind.DoubleKeyword
                    else
                        TokenKind.IdentifierToken
                | 'e' ->
                    if w = pack4 'x' 't' 'e' 'r' && last = 'n' then
                        TokenKind.ExternKeyword
                    else
                        TokenKind.IdentifierToken
                | 'o' ->
                    if w = pack4 'b' 'j' 'e' 'c' && last = 't' then
                        TokenKind.ObjectKeyword
                    else
                        TokenKind.IdentifierToken
                | 'p' ->
                    if w = pack4 'u' 'b' 'l' 'i' && last = 'c' then
                        TokenKind.PublicKeyword
                    elif w = pack4 'a' 'r' 'a' 'm' && last = 's' then
                        TokenKind.ParamsKeyword
                    else
                        TokenKind.IdentifierToken
                | 'r' ->
                    if w = pack4 'e' 't' 'u' 'r' && last = 'n' then
                        TokenKind.ReturnKeyword
                    else
                        TokenKind.IdentifierToken
                | 's' ->
                    if w = pack4 't' 'r' 'i' 'n' && last = 'g' then
                        TokenKind.StringKeyword
                    elif w = pack4 't' 'a' 't' 'i' && last = 'c' then
                        TokenKind.StaticKeyword
                    elif w = pack4 't' 'r' 'u' 'c' && last = 't' then
                        TokenKind.StructKeyword
                    elif w = pack4 'w' 'i' 't' 'c' && last = 'h' then
                        TokenKind.SwitchKeyword
                    elif w = pack4 'e' 'a' 'l' 'e' && last = 'd' then
                        TokenKind.SealedKeyword
                    elif w = pack4 'i' 'z' 'e' 'o' && last = 'f' then
                        TokenKind.SizeOfKeyword
                    else
                        TokenKind.IdentifierToken
                | 't' ->
                    if w = pack4 'y' 'p' 'e' 'o' && last = 'f' then
                        TokenKind.TypeOfKeyword
                    else
                        TokenKind.IdentifierToken
                | 'u' ->
                    if w = pack4 's' 'h' 'o' 'r' && last = 't' then
                        TokenKind.UShortKeyword
                    elif w = pack4 'n' 's' 'a' 'f' && last = 'e' then
                        TokenKind.UnsafeKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | 7 ->
                let w = load4 &first (start + 1)
                let tail = load2 &first (start + 5)

                match Unsafe.Add(&first, start) with
                | 'c' ->
                    if w = pack4 'h' 'e' 'c' 'k' && tail = pack2 'e' 'd' then
                        TokenKind.CheckedKeyword
                    else
                        TokenKind.IdentifierToken
                | 'd' ->
                    if w = pack4 'e' 'f' 'a' 'u' && tail = pack2 'l' 't' then
                        TokenKind.DefaultKeyword
                    elif w = pack4 'e' 'c' 'i' 'm' && tail = pack2 'a' 'l' then
                        TokenKind.DecimalKeyword
                    else
                        TokenKind.IdentifierToken
                | 'f' ->
                    if w = pack4 'o' 'r' 'e' 'a' && tail = pack2 'c' 'h' then
                        TokenKind.ForEachKeyword
                    elif w = pack4 'i' 'n' 'a' 'l' && tail = pack2 'l' 'y' then
                        TokenKind.FinallyKeyword
                    else
                        TokenKind.IdentifierToken
                | 'p' ->
                    if w = pack4 'r' 'i' 'v' 'a' && tail = pack2 't' 'e' then
                        TokenKind.PrivateKeyword
                    else
                        TokenKind.IdentifierToken
                | 'v' ->
                    if w = pack4 'i' 'r' 't' 'u' && tail = pack2 'a' 'l' then
                        TokenKind.VirtualKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | 8 ->
                let lo = load4 &first start
                let hi = load4 &first (start + 4)

                match Unsafe.Add(&first, start) with
                | 'a' ->
                    if lo = pack4 'a' 'b' 's' 't' && hi = pack4 'r' 'a' 'c' 't' then
                        TokenKind.AbstractKeyword
                    else
                        TokenKind.IdentifierToken
                | 'c' ->
                    if lo = pack4 'c' 'o' 'n' 't' && hi = pack4 'i' 'n' 'u' 'e' then
                        TokenKind.ContinueKeyword
                    else
                        TokenKind.IdentifierToken
                | 'd' ->
                    if lo = pack4 'd' 'e' 'l' 'e' && hi = pack4 'g' 'a' 't' 'e' then
                        TokenKind.DelegateKeyword
                    else
                        TokenKind.IdentifierToken
                | 'e' ->
                    if lo = pack4 'e' 'x' 'p' 'l' && hi = pack4 'i' 'c' 'i' 't' then
                        TokenKind.ExplicitKeyword
                    else
                        TokenKind.IdentifierToken
                | 'i' ->
                    if lo = pack4 'i' 'n' 't' 'e' && hi = pack4 'r' 'n' 'a' 'l' then
                        TokenKind.InternalKeyword
                    elif lo = pack4 'i' 'm' 'p' 'l' && hi = pack4 'i' 'c' 'i' 't' then
                        TokenKind.ImplicitKeyword
                    else
                        TokenKind.IdentifierToken
                | 'o' ->
                    if lo = pack4 'o' 'v' 'e' 'r' && hi = pack4 'r' 'i' 'd' 'e' then
                        TokenKind.OverrideKeyword
                    elif lo = pack4 'o' 'p' 'e' 'r' && hi = pack4 'a' 't' 'o' 'r' then
                        TokenKind.OperatorKeyword
                    else
                        TokenKind.IdentifierToken
                | 'r' ->
                    if lo = pack4 'r' 'e' 'a' 'd' && hi = pack4 'o' 'n' 'l' 'y' then
                        TokenKind.ReadOnlyKeyword
                    else
                        TokenKind.IdentifierToken
                | 'v' ->
                    if lo = pack4 'v' 'o' 'l' 'a' && hi = pack4 't' 'i' 'l' 'e' then
                        TokenKind.VolatileKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | 9 ->
                let lo = load4 &first (start + 1)
                let hi = load4 &first (start + 5)

                match Unsafe.Add(&first, start) with
                | '_' ->
                    if lo = pack4 '_' 'a' 'r' 'g' && hi = pack4 'l' 'i' 's' 't' then
                        TokenKind.ArgListKeyword
                    elif lo = pack4 '_' 'm' 'a' 'k' && hi = pack4 'e' 'r' 'e' 'f' then
                        TokenKind.MakeRefKeyword
                    elif lo = pack4 '_' 'r' 'e' 'f' && hi = pack4 't' 'y' 'p' 'e' then
                        TokenKind.RefTypeKeyword
                    else
                        TokenKind.IdentifierToken
                | 'i' ->
                    if lo = pack4 'n' 't' 'e' 'r' && hi = pack4 'f' 'a' 'c' 'e' then
                        TokenKind.InterfaceKeyword
                    else
                        TokenKind.IdentifierToken
                | 'n' ->
                    if lo = pack4 'a' 'm' 'e' 's' && hi = pack4 'p' 'a' 'c' 'e' then
                        TokenKind.NamespaceKeyword
                    else
                        TokenKind.IdentifierToken
                | 'p' ->
                    if lo = pack4 'r' 'o' 't' 'e' && hi = pack4 'c' 't' 'e' 'd' then
                        TokenKind.ProtectedKeyword
                    else
                        TokenKind.IdentifierToken
                | 'u' ->
                    if lo = pack4 'n' 'c' 'h' 'e' && hi = pack4 'c' 'k' 'e' 'd' then
                        TokenKind.UncheckedKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | 10 ->
                let lo = load4 &first (start + 2)
                let hi = load4 &first (start + 6)

                match Unsafe.Add(&first, start) with
                | '_' ->
                    if
                        Unsafe.Add(&first, start + 1) = '_'
                        && lo = pack4 'r' 'e' 'f' 'v'
                        && hi = pack4 'a' 'l' 'u' 'e'
                    then
                        TokenKind.RefValueKeyword
                    else
                        TokenKind.IdentifierToken
                | 's' ->
                    if
                        Unsafe.Add(&first, start + 1) = 't'
                        && lo = pack4 'a' 'c' 'k' 'a'
                        && hi = pack4 'l' 'l' 'o' 'c'
                    then
                        TokenKind.StackAllocKeyword
                    else
                        TokenKind.IdentifierToken
                | _ -> TokenKind.IdentifierToken
            | _ -> TokenKind.IdentifierToken
