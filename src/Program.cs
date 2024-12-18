using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Reflection.Metadata;
using System.Text;
using AsmResolver.DotNet;
using AsmResolver.DotNet.Builder;
using AsmResolver.DotNet.Code.Cil;
using AsmResolver.IO;
using AsmResolver.PE;
using AsmResolver.PE.DotNet.Builder;
using AsmResolver.PE.DotNet.Cil;
using AsmResolver.PE.File;
using ManifestResource = AsmResolver.DotNet.ManifestResource;
using MethodDefinition = AsmResolver.DotNet.MethodDefinition;
using TypeDefinition = AsmResolver.DotNet.TypeDefinition;

namespace SecureByteJITunpacker
{

    internal class Program
    {
        private static List<Tuple<string, byte[]>> TokenAndBody = new List<Tuple<string, byte[]>>();

        private static AsmResolver.DotNet.ModuleDefinition moduleDefinition;

        private static byte[] JITData;

        private static void Main(string[] args)
        {
            if (args.Length == 0)
            {
                Console.WriteLine("Usage: SecureByteJITunpacker.exe <file to unpack>");
                return;
            }
            Program.moduleDefinition = AsmResolver.DotNet.ModuleDefinition.FromFile(args[0]);
            Program.AnalyzeCctor();
            Program.DecryptJITDataAndRestoreMethods();
            int method_count = Program.TokenAndBody.Select((Tuple<string, byte[]> tuple) => tuple.Item1).Count<string>();
            LogInfo(string.Format("Decrypted {0} methods!\n", method_count));
            IPEImage image = new ManagedPEImageBuilder().CreateImage(Program.moduleDefinition).ConstructedImage;
            PEFile pefile = new ManagedPEFileBuilder().CreateFile(image);
            string output = args[0].Insert(args[0].Length - 4, "_decrypted");
            pefile.Write(output);
            Console.ReadKey();
        }

        private static void DecryptJITDataAndRestoreMethods()
        {
            BinaryReader binaryReader = new BinaryReader(new MemoryStream(Program.JITData));
            int num = binaryReader.ReadInt32();
            for (int i = 0; i < num; i++)
            {
                IMetadataMember methods = Program.moduleDefinition.LookupMember(binaryReader.ReadInt32());
                byte[] decryptedData = Convert.FromBase64String(binaryReader.ReadString());
                Program.TokenAndBody.Add(Tuple.Create<string, byte[]>(methods.MetadataToken.ToString(), decryptedData));
            }
            foreach (TypeDefinition typeDefinition in Program.moduleDefinition.GetAllTypes())
            {
                using (IEnumerator<AsmResolver.DotNet.MethodDefinition> enumerator2 = typeDefinition.Methods.GetEnumerator())
                {
                    while (enumerator2.MoveNext())
                    {
                        AsmResolver.DotNet.MethodDefinition m = enumerator2.Current;
                        if (m.HasMethodBody)
                        {
                            if (Program.TokenAndBody.Select((Tuple<string, byte[]> tuple) => tuple.Item1).Contains(m.MetadataToken.ToString()))
                            {
                                BinaryStreamReader reader = new BinaryStreamReader(Program.TokenAndBody.FirstOrDefault((Tuple<string, byte[]> tuple) => tuple.Item1 == m.MetadataToken.ToString()).Item2);
                                IList<CilInstruction> instrs = new CilDisassembler(in reader, new PhysicalCilOperandResolver(Program.moduleDefinition, m.CilMethodBody)).ReadInstructions();
                                m.CilMethodBody.Instructions.Clear();
                                m.CilMethodBody.Instructions.AddRange(instrs);
                            }
                        }
                    }
                }
            }
        }
        static void LogInfo(string message)
        {
            Console.ResetColor();
            Console.Write("\n[");
            Console.ForegroundColor = ConsoleColor.Cyan;
            Console.Write("i");
            Console.ResetColor();
            Console.Write($"] {message}");
        }
        static void LogGreen(string message)
        {
            Console.ResetColor();
            Console.Write("\n[");
            Console.ForegroundColor = ConsoleColor.Green;
            Console.Write("s");
            Console.ResetColor();
            Console.Write($"] {message}");
        }
        private static void AnalyzeCctor()
        {
            MethodDefinition cctor = Program.moduleDefinition.GetModuleConstructor();

            LogInfo("Analyzing cctor...");

            var firstCall = cctor.CilMethodBody.Instructions.FirstOrDefault(instr => instr.OpCode == CilOpCodes.Call);
            if (firstCall == null || firstCall.Operand is not IMethodDescriptor calledMethod)
            {
                Console.WriteLine("No call instruction found in cctor.");
                return;
            }

            LogInfo($"First call in .cctor: {calledMethod.FullName}");

            if (calledMethod is MethodDefinition methodDefinition && methodDefinition.CilMethodBody != null)
            {
                var ldstrInstruction = methodDefinition.CilMethodBody.Instructions.FirstOrDefault(instr => instr.OpCode == CilOpCodes.Ldstr);
                LogGreen($"Found JIT data resource (base64): {(string)ldstrInstruction.Operand}");
                LogInfo("Decompressing...");
                byte[] compressedBytes = Program.moduleDefinition.Resources.First((ManifestResource q) => q.Name == Convert.FromBase64String((string)ldstrInstruction.Operand)).GetData();
                Program.JITData = QuickLZ.DecompressBytes(compressedBytes, 2);

                foreach (var instruction in methodDefinition.CilMethodBody.Instructions.Where(instr => instr.OpCode == CilOpCodes.Ldstr))
                {
                    if (instruction.Operand is string str && str.Length == 5)
                    {
                        var resource = Program.moduleDefinition.Resources.FirstOrDefault(r => r.Name == str);
                        if (resource != null)
                        {
                            LogGreen($"Found JIT dll resource: {resource.Name}, removing it.");
                            Program.moduleDefinition.Resources.Remove(resource);
                        }
                        else
                        {
                            Console.WriteLine($"Resource '{str}' not found in the module.");
                        }
                    }
                }
            }
            LogInfo("Removing the first Call instruction from cctor...");
            cctor.CilMethodBody.Instructions.Remove(firstCall);
        }
    }
    
    public static class QuickLZ
    {
        public const int QLZ_VERSION_MAJOR = 1;
        public const int QLZ_VERSION_MINOR = 5;
        public const int QLZ_VERSION_REVISION = 0;
        public const int QLZ_STREAMING_BUFFER = 0;
        public const int QLZ_MEMORY_SAFE = 0;
        private const int HASH_VALUES = 4096;
        private const int UNCONDITIONAL_MATCHLEN = 6;
        private const int UNCOMPRESSED_END = 4;
        private const int CWORD_LEN = 4;
        public static byte[] DecompressBytes(byte[] source, int rnd)
        {
            int level;
            byte[] add = new byte[] { (byte)rnd };
            byte[] concat = source.Concat(add).ToArray();
            source = concat;
            int size = SizeDecompressed(source);
            int src = HeaderLen(source);
            int dst = 0;
            uint cword_val = 1;
            byte[] destination = new byte[size];
            int[] hashtable = new int[4096];
            byte[] hash_counter = new byte[4096];
            int last_matchstart = size - UNCONDITIONAL_MATCHLEN - UNCOMPRESSED_END - 1;
            int last_hashed = -1;
            int hash;
            uint fetch = 0;

            level = (source[0] >> 2) & 0x3;

            if (level != 1 && level != 3)
                throw new ArgumentException("C# version only supports level 1 and 3");

            if ((source[0] & 1) != 1)
            {
                byte[] d2 = new byte[size];
                System.Array.Copy(source, HeaderLen(source), d2, 0, size);
                return d2;
            }

            for (; ; )
            {
                if (cword_val == 1)
                {
                    cword_val = (uint)(source[src] | (source[src + 1] << 8) | (source[src + 2] << 16) | (source[src + 3] << 24));
                    src += 4;
                    if (dst <= last_matchstart)
                    {
                        if (level == 1)
                            fetch = (uint)(source[src] | (source[src + 1] << 8) | (source[src + 2] << 16));
                        else
                            fetch = (uint)(source[src] | (source[src + 1] << 8) | (source[src + 2] << 16) | (source[src + 3] << 24));
                    }
                }

                if ((cword_val & 1) == 1)
                {
                    uint matchlen;
                    uint offset2;

                    cword_val = cword_val >> 1;

                    if (level == 1)
                    {
                        hash = ((int)fetch >> 4) & 0xfff;
                        offset2 = (uint)hashtable[hash];

                        if ((fetch & 0xf) != 0)
                        {
                            matchlen = (fetch & 0xf) + 2;
                            src += 2;
                        }
                        else
                        {
                            matchlen = source[src + 2];
                            src += 3;
                        }
                    }
                    else
                    {
                        uint offset;
                        if ((fetch & 3) == 0)
                        {
                            offset = (fetch & 0xff) >> 2;
                            matchlen = 3;
                            src++;
                        }
                        else if ((fetch & 2) == 0)
                        {
                            offset = (fetch & 0xffff) >> 2;
                            matchlen = 3;
                            src += 2;
                        }
                        else if ((fetch & 1) == 0)
                        {
                            offset = (fetch & 0xffff) >> 6;
                            matchlen = ((fetch >> 2) & 15) + 3;
                            src += 2;
                        }
                        else if ((fetch & 127) != 3)
                        {
                            offset = (fetch >> 7) & 0x1ffff;
                            matchlen = ((fetch >> 2) & 0x1f) + 2;
                            src += 3;
                        }
                        else
                        {
                            offset = (fetch >> 15);
                            matchlen = ((fetch >> 7) & 255) + 3;
                            src += 4;
                        }
                        offset2 = (uint)(dst - offset);
                    }

                    destination[dst + 0] = destination[offset2 + 0];
                    destination[dst + 1] = destination[offset2 + 1];
                    destination[dst + 2] = destination[offset2 + 2];

                    for (int i = 3; i < matchlen; i += 1)
                    {
                        destination[dst + i] = destination[offset2 + i];
                    }

                    dst += (int)matchlen;

                    if (level == 1)
                    {
                        fetch = (uint)(destination[last_hashed + 1] | (destination[last_hashed + 2] << 8) | (destination[last_hashed + 3] << 16));
                        while (last_hashed < dst - matchlen)
                        {
                            last_hashed++;
                            hash = (int)(((fetch >> 12) ^ fetch) & (HASH_VALUES - 1));
                            hashtable[hash] = last_hashed;
                            hash_counter[hash] = 1;
                            fetch = (uint)(fetch >> 8 & 0xffff | destination[last_hashed + 3] << 16);
                        }
                        fetch = (uint)(source[src] | (source[src + 1] << 8) | (source[src + 2] << 16));
                    }
                    else
                    {
                        fetch = (uint)(source[src] | (source[src + 1] << 8) | (source[src + 2] << 16) | (source[src + 3] << 24));
                    }
                    last_hashed = dst - 1;
                }
                else
                {
                    if (dst <= last_matchstart)
                    {
                        destination[dst] = source[src];
                        dst += 1;
                        src += 1;
                        cword_val = cword_val >> 1;

                        if (level == 1)
                        {
                            while (last_hashed < dst - 3)
                            {
                                last_hashed++;
                                int fetch2 = destination[last_hashed] | (destination[last_hashed + 1] << 8) | (destination[last_hashed + 2] << 16);
                                hash = ((fetch2 >> 12) ^ fetch2) & (HASH_VALUES - 1);
                                hashtable[hash] = last_hashed;
                                hash_counter[hash] = 1;
                            }
                            fetch = (uint)(fetch >> 8 & 0xffff | source[src + 2] << 16);
                        }
                        else
                        {
                            fetch = (uint)(fetch >> 8 & 0xffff | source[src + 2] << 16 | source[src + 3] << 24);
                        }
                    }
                    else
                    {
                        while (dst <= size - 1)
                        {
                            if (cword_val == 1)
                            {
                                src += CWORD_LEN;
                                cword_val = 0x80000000;
                            }

                            destination[dst] = source[src];
                            dst++;
                            src++;
                            cword_val = cword_val >> 1;
                        }
                        return destination;
                    }
                }
            }
        }
        public static int HeaderLen(byte[] source)
        {
            return ((source[0] & 2) == 2) ? 9 : 3;
        }
        public static int SizeDecompressed(byte[] source)
        {
            if (HeaderLen(source) == 9)
                return source[5] | (source[6] << 8) | (source[7] << 16) | (source[8] << 24);

            return source[2];
        }
    }
}