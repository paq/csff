// Copyright notice of the kind that heads most files.
// Licensed under the MIT license.

/*
 * A block comment that documents the file as a whole and spans
 * several lines, with   irregular   spacing inside it.
 */

using System; // trailing comment on a using
using System.Collections.Generic; /* and a block one */

namespace Sample.Commented // namespace comment
{
    /// <summary>
    /// A type whose members are mostly documentation and comments.
    /// </summary>
    /// <remarks>
    /// <para>Paragraphs, <c>code</c>, and <see cref="Dictionary{TKey, TValue}"/> references.</para>
    /// </remarks>
    public class Cache<TKey, TValue> // trailing on the type
        where TKey : notnull
    {
        // A field comment.
        private readonly Dictionary<TKey, TValue> items = new(); // trailing on the field

        /* A block comment before a field */ private int hits;
        private int misses; /* a block comment after a field */



        /// <summary>Looks up a value.</summary>
        /// <param name="key">The key.</param>
        /// <param name="value">The value, when found.</param>
        /// <returns>Whether the key was found.</returns>
        public bool TryGet(TKey key, out TValue value) // trailing on a signature
        {
            // first line of a comment run
            // second line of a comment run
            if (items.TryGetValue(key, out value!)) // found
            {
                hits++; // count it
                return true;
            }
            /* not found */ misses++;
            return false; // done
        }

        /// <summary>Stores a value.</summary>
        public void Set(TKey key, /* inline parameter comment */ TValue value)
        {
            items[key] = value;     // overwrite


            // a comment after blank lines
        }

        public int Count => items.Count; // expression-bodied with a comment

        /// <summary>Statistics.</summary>
        public (int Hits, int Misses) Statistics() =>
            // a comment inside an expression body
            (hits, misses);

        public void Clear()
        {
            items.Clear();
            // hits = 0; (commented-out code)
            // misses = 0;
            /*
            if (verbose)
            {
                Console.WriteLine("cleared");
            }
            */
        }

        public IEnumerable<TKey> Keys()
        {
            foreach (var key in items.Keys) // iterate
            {
                // yield each
                yield return key;
            } // end foreach
        } // end Keys

        public int Sum(Func<TValue, int> selector)
        {
            var total = 0;
            foreach (var value in items.Values)
                total += selector(value); // accumulate
            return total /* the sum */;
        }

        public void Call() => Consume(1, // first
            2, // second
            /* third */ 3);

        private static void Consume(int a, int b, int c) { } // empty body
    } // end class

    // A comment between types.

    /// <summary>An enum with commented members.</summary>
    public enum Mode
    {
        /// <summary>The first.</summary>
        First, // one
        // a comment before a member
        Second, /* two */
        Third // three
    }
} // end namespace
// trailing file comment
