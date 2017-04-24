// Copyright (C) 2017 Microsoft Research
// Author: Christoph M. Wintersteiger (cwinter)

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.IO.Compression;
using System.Runtime.Serialization;
using System.Runtime.Serialization.Formatters.Binary;
using System.Text.RegularExpressions;

namespace fabc_make
{
    public static class FStar
    {
        public static readonly string OutFilesPkg = "outfiles.tar.gz";
        private static object CSVLock = new object();


        internal static void AddFilesToZip(string home, string d, string ptrn, ZipArchive zip)
        {
            home = home.TrimEnd('\\').TrimEnd('/');
            d = d.TrimEnd('\\').TrimEnd('/');

            foreach (string f in Directory.EnumerateFiles(Path.Combine(home, d), ptrn, SearchOption.AllDirectories))
            {
                string entryName = (f.StartsWith(home)) ? f.Substring(home.Length + 1) :
                                   (f.StartsWith(d)) ? f.Substring(d.Length + 1) :
                                                          Path.GetFileName(f);
                // Console.WriteLine("  " + f + " [" + entryName + "]");
                zip.CreateEntryFromFile(f, entryName.Replace(@"\", "/"), CompressionLevel.Optimal);
            }
        }

        public static string MakePackage(string home, string z3, string[] contents)
        {
            if (!Directory.Exists(home))
                throw new DirectoryNotFoundException("Could not find F* at " + home);

            if (!File.Exists(z3))
                throw new FileNotFoundException("Could not find Z3 at " + z3);

            string filename = Path.GetTempFileName();

            using (FileStream zstr = new FileStream(filename, FileMode.Create))
            using (ZipArchive zip = new ZipArchive(zstr, ZipArchiveMode.Create))
            {
                foreach (string dirptrn in contents)
                {
                    string[] dirptrns = dirptrn.Split('|');
                    string dir = dirptrns[0];
                    string ptrn = dirptrns[1];
                    // Console.WriteLine("> " + ptrn + " in " + dir);
                    AddFilesToZip(home, dir, ptrn, zip);
                }

                zip.CreateEntryFromFile(z3, Path.GetFileName(z3), CompressionLevel.Optimal);
            }

            return filename;
        }

        public class Task
        {
            public string Filepath = null;

            // 1073741824
            public static string RLIMIT10 = " --z3rlimit 10 "; // 10
            public string LIMITS = " --z3rlimit 20 "; // 20
            public string OPTS = " --z3cliopt -st ";
            public string HINTS = "--hint_info ";
            public string FUEL = " $LIMITS--max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 0 ";
            public List<string> TaskFiles = new List<string>();
            public string[] OutFileExtensions = { }; // { "hints", "proofs.smt2" };

            public string cmd;
            public Task(string c) { this.cmd = c; }
            public string CommandLine()
            {
                string t = "chmod +x bin/fstar.exe ; chmod +x z3 ; " + cmd;
                t = t.Replace("\t", " ");
                t = t.Replace("$FUEL", FUEL);
                t = t.Replace("$LIMITS", LIMITS).Replace("$RLIMIT10", RLIMIT10);
                t = t.Replace("$OPTS", OPTS).Replace("$HINTS", HINTS);
                return ("time (" + t + ")") + Postprocess();
            }

            public string Postprocess()
            {
                if (OutFileExtensions.Length > 0)
                {
                    string pp = " ; rm -f tmp.tar tmp.tar.gz " + OutFilesPkg + " ; ";
                    foreach (string ext in OutFileExtensions)
                        pp += @"(find . -name '*." + ext + @"' | sed 's|./||' | tar cf tmp.tar -T - ) ; ";
                    pp += "gzip tmp.tar; mv tmp.tar.gz " + OutFilesPkg;
                    return pp;
                }
                else
                    return "";
            }
        };

        [Serializable]
        public class TaskResult : ISerializable
        {
            public string Id = "";
            public string Filepath = null;
            public int ExitCode = 0;
            public double CPUTime = 0.0, WCTime = 0.0, WaitTime = 0.0;
            public Exception Exception = null;
            public MemoryStream StdOut = new MemoryStream();
            public MemoryStream StdErr = new MemoryStream();
            public MemoryStream Info = new MemoryStream();
            // public MemoryStream OutFileStream = new MemoryStream();
            public string OutFileTemp = null;

            internal double? _real_time = null, _user_time = null, _sys_time = null;
            uint? _num_errors = null;

            public TaskResult() { }


            internal static Regex _RealTimeRegex = new Regex(@"^real\t(\d+)m(\d+)\.(\d+)s$");
            internal static Regex _UserTimeRegex = new Regex(@"^user\t(\d+)m(\d+)\.(\d+)s$");
            internal static Regex _SysTimeRegex = new Regex(@"^sys\t(\d+)m(\d+)\.(\d+)s$");

            public double? RealTime
            {
                get
                {
                    if (!_real_time.HasValue)
                    {
                        StdErr.Seek(0, SeekOrigin.Begin);
                        StreamReader sr = new StreamReader(StdErr);
                        while (!sr.EndOfStream)
                        {
                            Match m = _RealTimeRegex.Match(sr.ReadLine());
                            if (m.Success)
                            {
                                double min = Convert.ToDouble(m.Groups[1].Value);
                                double sec = Convert.ToDouble(m.Groups[2].Value);
                                double thou = Convert.ToDouble(m.Groups[3].Value);
                                _real_time = (min * 60.0) + sec + (thou / 1000.0);
                                break;
                            }
                        }
                        StdErr.Seek(0, SeekOrigin.Begin);
                    }
                    return _real_time;
                }
            }
            public double? UserTime
            {
                get
                {
                    if (!_user_time.HasValue)
                    {
                        StdErr.Seek(0, SeekOrigin.Begin);
                        StreamReader sr = new StreamReader(StdErr);
                        while (!sr.EndOfStream)
                        {
                            Match m = _UserTimeRegex.Match(sr.ReadLine());
                            if (m.Success)
                            {
                                double min = Convert.ToDouble(m.Groups[1].Value);
                                double sec = Convert.ToDouble(m.Groups[2].Value);
                                double thou = Convert.ToDouble(m.Groups[3].Value);
                                _user_time = (min * 60.0) + sec + (thou / 1000.0);
                                break;
                            }
                        }
                        StdErr.Seek(0, SeekOrigin.Begin);
                    }
                    return _user_time;
                }
            }
            public double? SysTime
            {
                get
                {
                    if (!_sys_time.HasValue)
                    {
                        StdErr.Seek(0, SeekOrigin.Begin);
                        StreamReader sr = new StreamReader(StdErr);
                        while (!sr.EndOfStream)
                        {
                            Match m = _SysTimeRegex.Match(sr.ReadLine());
                            if (m.Success)
                            {
                                double min = Convert.ToDouble(m.Groups[1].Value);
                                double sec = Convert.ToDouble(m.Groups[2].Value);
                                double thou = Convert.ToDouble(m.Groups[3].Value);
                                _sys_time = (min * 60.0) + sec + (thou / 1000.0);
                                break;
                            }
                        }
                        StdErr.Seek(0, SeekOrigin.Begin);
                    }
                    return _sys_time;
                }
            }


            internal static Regex _NumErrorsRegex1 = new Regex(@"^1 error was reported \(see above\)$");
            internal static Regex _NumErrorsRegexN = new Regex(@"^(\d+) errors were reported \(see above\)$");

            public uint? NumErrors
            {
                get
                {
                    if (!_num_errors.HasValue)
                    {
                        StdErr.Seek(0, SeekOrigin.Begin);
                        StreamReader sr = new StreamReader(StdErr);
                        while (!sr.EndOfStream)
                        {
                            string line = sr.ReadLine();
                            Match m = _NumErrorsRegex1.Match(line);
                            if (m.Success)
                                _num_errors = 1;
                            else
                            {
                                m = _NumErrorsRegexN.Match(line);
                                if (m.Success)
                                    _num_errors = Convert.ToUInt32(m.Groups[1].Value);
                            }
                        }
                        StdErr.Seek(0, SeekOrigin.Begin);
                    }
                    return _num_errors;
                }
            }

            public void SaveTo(string directory, string csv = null)
            {
                string fp = Filepath == null ? Id : Filepath;
                string dir = Path.Combine(directory, Path.GetDirectoryName(fp));
                string lPth = Path.Combine(dir, Path.GetFileName(fp));
                if (!Directory.Exists(dir)) Directory.CreateDirectory(dir);

                int i = 0;
                string pre = lPth;
                while (File.Exists(lPth + ".resobj"))
                    lPth = pre + "-" + (++i).ToString();

                using (FileStream fs = new FileStream(lPth + ".out", FileMode.Create))
                    StdOut.CopyTo(fs);
                using (FileStream fs = new FileStream(lPth + ".err", FileMode.Create))
                    StdErr.CopyTo(fs);
                using (FileStream fs = new FileStream(lPth + ".data", FileMode.Create))
                    Info.CopyTo(fs);
                using (FileStream fs = new FileStream(lPth + ".resobj", FileMode.Create))
                    (new BinaryFormatter()).Serialize(fs, this);

                if (OutFileTemp != null)
                    File.Move(OutFileTemp, (lPth + "." + FStar.OutFilesPkg));
                OutFileTemp = null;

                SaveCSVRowTo(Path.Combine(directory, csv));
            }

            public string CSVRow
            {
                get
                {
                    string tid = this.Filepath == null ? Id : this.Filepath;
                    string format = "{0}, {1:D}, {2:F5}, {3:F5}, {4:F5}, {5}, {6}, {7}, {8}, {9}";
                    string row = String.Format(format, tid, ExitCode, CPUTime, WCTime,
                                               RealTime, UserTime, SysTime,
                                               WaitTime,
                                               NumErrors.HasValue ? NumErrors.Value : 0,
                                               (Exception != null) ? "\"" + Exception.Message + "\"" : "");
                    return row;
                }
            }

            public static string CSVHeader { get { return "Id, ExitCode, CPU time [sec], WallClock time [sec], Real time [sec], User time [sec], Sys time [sec], Wait time [sec], # Errors, Exception"; } }

            public void SaveCSVRowTo(string filepath)
            {
                if (filepath == null)
                    return;
                else
                    lock (CSVLock)
                    {
                        string row = CSVRow;
                        bool newFile = !File.Exists(filepath);
                        using (FileStream fs = new FileStream(filepath, FileMode.Append, FileAccess.Write))
                        using (StreamWriter csvw = new StreamWriter(fs))
                        {
                            if (newFile)
                                csvw.WriteLine(CSVHeader);
                            csvw.WriteLine(row);
                        }
                    }
            }

            public static TaskResult FromFile(string filepath)
            {
                try
                {
                    using (Stream strm = new FileStream(filepath, FileMode.Open, FileAccess.Read))
                        return (FStar.TaskResult)(new BinaryFormatter()).Deserialize(strm);
                }
                catch (Exception ex)
                {
                    Console.WriteLine("Error deserializing '" + filepath + "': " + ex.Message);
                    return null;
                }
            }

            #region Serialization

            public void GetObjectData(SerializationInfo info, StreamingContext context)
            {
                StdOut.Seek(0, SeekOrigin.Begin);
                StdErr.Seek(0, SeekOrigin.Begin);
                Info.Seek(0, SeekOrigin.Begin);

                info.AddValue("Id", Id, typeof(string));
                info.AddValue("Filepath", Filepath, typeof(string));
                info.AddValue("ExitCode", ExitCode, typeof(int));
                info.AddValue("CPUTime", CPUTime, typeof(double));
                info.AddValue("WCTime", WCTime, typeof(double));
                info.AddValue("WaitTime", WCTime, typeof(double));
                info.AddValue("Exception", Exception, typeof(Exception));
                info.AddValue("StdOut", StdOut, typeof(MemoryStream));
                info.AddValue("StdErr", StdErr, typeof(MemoryStream));
                info.AddValue("Info", Info, typeof(MemoryStream));
            }

            public TaskResult(SerializationInfo info, StreamingContext context)
            {
                Id = (string)info.GetValue("Id", typeof(string));
                Filepath = (string)info.GetValue("Filepath", typeof(string));
                ExitCode = (int)info.GetValue("ExitCode", typeof(int));
                CPUTime = (double)info.GetValue("CPUTime", typeof(double));
                WCTime = (double)info.GetValue("WCTime", typeof(double));
                WaitTime = (double)info.GetValue("WaitTime", typeof(double));
                Exception = (Exception)info.GetValue("Exception", typeof(Exception));
                StdOut = (MemoryStream)info.GetValue("StdOut", typeof(MemoryStream));
                StdErr = (MemoryStream)info.GetValue("StdErr", typeof(MemoryStream));
                Info = (MemoryStream)info.GetValue("Info", typeof(MemoryStream));

                StdOut.Seek(0, SeekOrigin.Begin);
                StdErr.Seek(0, SeekOrigin.Begin);
                Info.Seek(0, SeekOrigin.Begin);
            }
            #endregion
        }
    }

}
