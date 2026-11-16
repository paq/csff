#define TRACE_IO
using System;
using System.IO;
#if NET8_0_OR_GREATER
using System.Buffers;
#endif
#if WINDOWS
using System.Runtime.InteropServices;
#endif

namespace Sample.Platform
{
    #region Configuration
    public static class Paths {
#if WINDOWS
        public const char Separator = '\\';
        public static string Home => Environment.GetFolderPath(Environment.SpecialFolder.UserProfile);
#elif OSX
        public const char Separator = '/';
        public static string Home => Environment.GetEnvironmentVariable("HOME") ?? "/Users";
#else
        public const char Separator = '/';
        public static string Home => Environment.GetEnvironmentVariable("HOME") ?? "/home";
#endif

        public static string Combine(string left, string right) {
            if (left.Length == 0) return right;
#if WINDOWS
            if (left[left.Length - 1] == '\\' || left[left.Length - 1] == '/') return left + right;
#else
            if (left[left.Length - 1] == '/') return left + right;
#endif
            return left + Separator + right;
        }
    }
    #endregion

    public sealed class FileCopier
    {
        private readonly int bufferSize;

        public FileCopier(int bufferSize = 81920) { this.bufferSize = bufferSize; }

        public long Copy(Stream source, Stream destination)
        {
            long total = 0;
#if NET8_0_OR_GREATER
            var buffer = ArrayPool<byte>.Shared.Rent(bufferSize);
            try {
#else
            var buffer = new byte[bufferSize];
            {
#endif
                int read;
                while ((read = source.Read(buffer, 0, buffer.Length)) > 0) {
                    destination.Write(buffer, 0, read);
                    total += read;
#if TRACE_IO && DEBUG
                    Console.Error.WriteLine($"copied {read} bytes, {total} so far");
#endif
                }
            }
#if NET8_0_OR_GREATER
            finally { ArrayPool<byte>.Shared.Return(buffer); }
#endif
            return total;
        }

#if WINDOWS
        [DllImport("kernel32.dll", SetLastError = true)]
        private static extern bool FlushFileBuffers(IntPtr handle);

        public static void Flush(FileStream stream) { if (!FlushFileBuffers(stream.SafeFileHandle.DangerousGetHandle())) throw new IOException("flush failed"); }
#else
        public static void Flush(FileStream stream) { stream.Flush(true); }
#endif

        #region Diagnostics
#if DEBUG
        public override string ToString() => $"FileCopier(debug, {bufferSize})";
#elif TRACE_IO
        public override string ToString() => $"FileCopier(trace, {bufferSize})";
#else
        public override string ToString() => "FileCopier";
#endif
        #endregion
    }

#if FEATURE_ASYNC
    public static class AsyncCopy
    {
        public static async System.Threading.Tasks.Task<long> CopyAsync(Stream source, Stream destination) { await source.CopyToAsync(destination); return destination.Length; }
    }
#endif

    public enum Platform {
        Unknown,
#if WINDOWS
        Windows,
#endif
#if OSX
        MacOS,
#endif
        Linux
    }
}
