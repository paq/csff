using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;

namespace Sample.Reports
{
    public sealed class ReportWriter
    {
        private readonly CultureInfo culture = CultureInfo.InvariantCulture;

        public string Header(string title, DateTime generated, int rows) => $"=== {title.ToUpperInvariant()} === generated {generated:yyyy-MM-dd HH:mm:ss} ({rows} {(rows == 1 ? "row" : "rows")}) by {Environment.UserName} on {Environment.MachineName} ===";

        public string Row(string name, decimal amount, double ratio, int? rank) {
            return $"{name,-24}|{amount,12:N2}|{ratio,8:P1}|{(rank is { } r ? $"#{r:D3}" : "  -  "),6}|{(amount >= 1000m ? "large" : amount >= 100m ? "medium" : "small"),-6}|{string.Join(",", name.Where(char.IsUpper).Select(c => $"{c}"))}";
        }

        public string Json(IReadOnlyDictionary<string, object?> fields) => $"{{{string.Join(", ", fields.Select(pair => $"\"{pair.Key}\": {(pair.Value switch { null => "null", string text => $"\"{text.Replace("\"", "\\\"")}\"", bool flag => flag ? "true" : "false", IFormattable number => number.ToString(null, culture), var other => $"\"{other}\"" })}"))}}}";

        public string Raw(string table, IEnumerable<string> columns, int limit) {
            var sql = $"""
                SELECT {string.Join(", ", columns.Select(column => $"[{column}]"))}
                FROM [{table}]
                WHERE [Deleted] = 0 AND [Created] > '{DateTime.UtcNow.AddDays(-30):yyyy-MM-dd}'
                ORDER BY [{columns.First()}]
                OFFSET 0 ROWS FETCH NEXT {limit} ROWS ONLY
                """;
            return sql;
        }

        public string RawWithBraces(string name, int value) => $$"""
            {
              "name": "{{name}}",
              "value": {{value}},
              "nested": { "doubled": {{value * 2}}, "label": "{{(value > 10 ? "big" : "small")}}" }
            }
            """;

        public IEnumerable<string> Lines(IEnumerable<(string Name, decimal Amount, double Ratio)> items)
        {
            int index = 0;
            foreach (var (name, amount, ratio) in items) {
                index++;
                yield return $"{index,4}. {name} — {amount.ToString("C", culture)} ({ratio:0.00%}){(index % 10 == 0 ? Environment.NewLine + new string('-', 40) : string.Empty)}";
            }
            yield return $"{index} items, verbatim path: {@"C:\reports\" + DateTime.Today.ToString("yyyyMMdd")}, escaped: {"tab\there"}, multiline: {$@"first
second {index}"}";
        }

        public string Nested(int depth) => depth <= 0 ? "leaf" : $"({depth}: {$"[{Nested(depth - 1)}]"} {(depth % 2 == 0 ? $"even {depth / 2}" : $"odd {$"{depth * 3 + 1}"}")})";

        public FormattableString Formattable(string user, int attempts, TimeSpan elapsed) => $"user {user} failed {attempts} time{(attempts == 1 ? "" : "s")} in {elapsed.TotalMilliseconds:F1} ms";
    }
}
