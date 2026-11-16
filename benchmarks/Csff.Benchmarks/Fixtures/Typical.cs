using System;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Sample.Orders
{
    public enum OrderState { Draft, Submitted, Shipped, Cancelled }

    public sealed record OrderLine(string Sku, int Quantity, decimal UnitPrice) {
        public decimal Total => Quantity * UnitPrice;
    }

    public interface IOrderRepository {
        Task<Order?> FindAsync(Guid id, CancellationToken cancellationToken);
        Task SaveAsync(Order order, CancellationToken cancellationToken);
    }

    public class Order
    {
        private readonly List<OrderLine> lines = new List<OrderLine>();
        public Guid Id { get; } = Guid.NewGuid();
        public OrderState State { get; private set; }
        public string Customer { get; set; } = "";
        public IReadOnlyList<OrderLine> Lines => lines;

        public decimal Total { get { return lines.Sum(line => line.Total); } }

        public void Add(string sku, int quantity, decimal unitPrice) {
            if (State != OrderState.Draft) throw new InvalidOperationException("Only a draft order can change.");
            if (quantity <= 0) { throw new ArgumentOutOfRangeException(nameof(quantity), quantity, "Quantity must be positive."); }
            var existing = lines.FindIndex(line => string.Equals(line.Sku, sku, StringComparison.Ordinal));
            if (existing >= 0) lines[existing] = lines[existing] with { Quantity = lines[existing].Quantity + quantity };
            else lines.Add(new OrderLine(sku, quantity, unitPrice));
        }

        public void Submit()
        {
            switch (State) {
                case OrderState.Draft when lines.Count > 0: State = OrderState.Submitted; break;
                case OrderState.Draft: throw new InvalidOperationException("An empty order cannot be submitted.");
                default: throw new InvalidOperationException($"Cannot submit an order that is {State}.");
            }
        }
    }

    public sealed class OrderService
    {
        private readonly IOrderRepository repository;
        private readonly Func<DateTimeOffset> clock;

        public OrderService(IOrderRepository repository, Func<DateTimeOffset>? clock = null) { this.repository = repository ?? throw new ArgumentNullException(nameof(repository)); this.clock = clock ?? (() => DateTimeOffset.UtcNow); }

        public async Task<decimal> SubmitAsync(Guid id, CancellationToken cancellationToken = default)
        {
            var order = await repository.FindAsync(id, cancellationToken).ConfigureAwait(false) ?? throw new KeyNotFoundException($"No order {id}.");
            order.Submit();
            await repository.SaveAsync(order, cancellationToken).ConfigureAwait(false);
            return order.Total;
        }

        public static IEnumerable<(string Sku, int Quantity)> Summarize(IEnumerable<Order> orders) =>
            orders.Where(order => order.State == OrderState.Submitted || order.State == OrderState.Shipped).SelectMany(order => order.Lines).GroupBy(line => line.Sku).Select(group => (group.Key, group.Sum(line => line.Quantity))).OrderByDescending(pair => pair.Item2).ThenBy(pair => pair.Key, StringComparer.Ordinal);

        public string Describe(Order order)
        {
            var now = clock();
            return order.State switch { OrderState.Draft => "draft", OrderState.Submitted => $"submitted, {order.Lines.Count} lines", OrderState.Shipped => "shipped " + now.ToString("u"), _ => "cancelled" };
        }

        private static bool TryParseQuantity(string? text, out int quantity)
        {
            quantity = 0;
            if (string.IsNullOrWhiteSpace(text)) return false;
            foreach (var c in text) { if (c < '0' || c > '9') return false; quantity = checked(quantity * 10 + (c - '0')); }
            return true;
        }
    }

    internal static class OrderExtensions
    {
        public static bool IsOpen(this Order order) => order.State is OrderState.Draft or OrderState.Submitted;

        public static Dictionary<string, decimal> TotalsByCustomer(this IEnumerable<Order> orders)
        {
            var totals = new Dictionary<string, decimal>(StringComparer.OrdinalIgnoreCase);
            foreach (var order in orders) {
                totals.TryGetValue(order.Customer, out var running);
                totals[order.Customer] = running + order.Total;
            }
            return totals;
        }

        public static T[] Page<T>(this IReadOnlyList<T> items, int page, int size) where T : notnull
        {
            if (page < 0 || size <= 0) return Array.Empty<T>();
            var start = page * size; var count = Math.Max(0, Math.Min(size, items.Count - start));
            var result = new T[count];
            for (int i = 0; i < count; i++) result[i] = items[start + i];
            return result;
        }
    }
}
