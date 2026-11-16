namespace Csff.Printer

open System
open System.Collections
open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Runtime.InteropServices

[<Struct; IsReadOnly; NoEquality; NoComparison>]
type internal IntSlice =
    val internal items: int array
    val internal start: int
    val internal count: int

    new(items, start, count) =
        {
            items = items
            start = start
            count = count
        }

    new(memory: ReadOnlyMemory<int>) =
        let success, segment = MemoryMarshal.TryGetArray memory

        if not success then
            invalidArg (nameof memory) "Child ranges must borrow array storage."

        IntSlice(segment.Array, segment.Offset, segment.Count)

    member this.Length
        with [<MethodImpl(MethodImplOptions.AggressiveInlining)>] get () = this.count

    member this.Item
        with [<MethodImpl(MethodImplOptions.AggressiveInlining)>] get index =
            if uint index >= uint this.count then
                raise (IndexOutOfRangeException())

            this.items[this.start + index]

    member this.ToArray() =
        this.items.AsSpan(this.start, this.count).ToArray()

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.SliceRange(start: int, finish: int) =
        let start = max 0 start
        let finish = min (this.count - 1) finish
        IntSlice(this.items, this.start + min start this.count, max 0 (finish - start + 1))

    [<MethodImpl(MethodImplOptions.AggressiveInlining)>]
    member this.SliceFrom(start: int) =
        let start = max 0 start
        let offset = min start this.count
        IntSlice(this.items, this.start + offset, this.count - offset)

    member inline this.GetSlice(first: int option, last: int option) =
        this.SliceRange(
            (match first with
             | Some v -> v
             | None -> 0),
            (match last with
             | Some v -> v
             | None -> Int32.MaxValue)
        )

module internal Slice =
    let inline ofArray (items: int array) = IntSlice(items, 0, items.Length)

    let inline exists predicate (items: IntSlice) =
        let mutable i = 0
        let mutable found = false

        while i < items.Length && not found do
            found <- predicate items[i]
            i <- i + 1

        found

    let inline forall predicate (items: IntSlice) =
        let mutable i = 0
        let mutable valid = true

        while i < items.Length && valid do
            valid <- predicate items[i]
            i <- i + 1

        valid

    let inline contains (value: int) (items: IntSlice) =
        let mutable i = 0
        let mutable found = false

        while i < items.Length && not found do
            found <- items[i] = value
            i <- i + 1

        found

    let inline item index (items: IntSlice) = items[index]
    let inline length (items: IntSlice) = items.Length
    let inline last (items: IntSlice) = items[items.Length - 1]

    let inline tryFindIndex predicate (items: IntSlice) =
        let mutable i = 0

        while i < items.Length && not (predicate items[i]) do
            i <- i + 1

        if i < items.Length then ValueSome i else ValueNone

    let inline findIndex predicate (items: IntSlice) =
        let mutable i = 0

        while i < items.Length && not (predicate items[i]) do
            i <- i + 1

        if i < items.Length then i else raise (KeyNotFoundException())

    let inline findIndexBack predicate (items: IntSlice) =
        let mutable i = items.Length - 1

        while i >= 0 && not (predicate items[i]) do
            i <- i - 1

        if i >= 0 then i else raise (KeyNotFoundException())

    let inline tryFind predicate (items: IntSlice) =
        let mutable i = 0

        while i < items.Length && not (predicate items[i]) do
            i <- i + 1

        if i < items.Length then ValueSome items[i] else ValueNone

    let inline find predicate (items: IntSlice) =
        let mutable i = 0

        while i < items.Length && not (predicate items[i]) do
            i <- i + 1

        if i < items.Length then items[i] else raise (KeyNotFoundException())

    let inline filter predicate (items: IntSlice) =
        let mutable count = 0

        for i = 0 to items.Length - 1 do
            if predicate items[i] then
                count <- count + 1

        if count = items.Length then
            items
        else
            let result = Array.zeroCreate<int> count
            let mutable next = 0

            for i = 0 to items.Length - 1 do
                if predicate items[i] then
                    result[next] <- items[i]
                    next <- next + 1

            ofArray result

    let inline takeWhile predicate (items: IntSlice) =
        let mutable i = 0

        while i < items.Length && predicate items[i] do
            i <- i + 1

        items.SliceRange(0, i - 1)

    let inline mapi mapper (items: IntSlice) =
        let result = Array.zeroCreate items.Length

        for i = 0 to items.Length - 1 do
            result[i] <- mapper i items[i]

        result

    let inline sortBy (projection: int -> int) (items: IntSlice) =
        let mutable ordered = true
        let mutable previous = Int32.MinValue
        let mutable i = 0

        while i < items.Length && ordered do
            let rank = projection items[i]
            ordered <- previous <= rank
            previous <- rank
            i <- i + 1

        if ordered then
            items
        else
            let result = items.ToArray()

            for i = 1 to result.Length - 1 do
                let value = result[i]
                let rank = projection value
                let mutable j = i

                while j > 0 && projection result[j - 1] > rank do
                    result[j] <- result[j - 1]
                    j <- j - 1

                result[j] <- value

            ofArray result
