// Copyright (C) 2017 Microsoft Research
// Author: Christoph M. Wintersteiger (cwinter)

using System;
using System.IO;
using System.Collections.Generic;

namespace fabc_make
{
    internal class Arguments
    {
        public string Command = null;

        public string JobId = null;

        public string Package = null;
        public string PackageBlobId = null;
        public List<string> PackageContents = new List<string>();
        public string[] FStarArguments = null;

        public string BatchIDFile = null;
        public string Directory = null;
        public string HintDirectory = null;
        public bool HintCollection = false;
        public bool SaveResultFiles = true;
        public string JobDisplayName = null;

        internal static Arguments Get(string[] args)
        {
            if (args.Length < 1)
                return null;

            Arguments result = new Arguments();
            result.Command = args[0].ToLower();

            switch (result.Command)
            {
                case "create":
                case "add":
                case "await":
                case "list":
                case "delete":
                    break;
                default:
                    Console.WriteLine("Unknown command '" + result.Command + "'.");
                    return null;
            }


            for (int i = 1; i < args.Length && result != null; i++)
            {
                switch (args[i])
                {
                    case "-b": result.PackageBlobId = args[++i]; break;
                    case "-j": result.JobId = args[++i]; break;
                    case "-i": result.BatchIDFile = args[++i]; break;
                    case "-d": result.Directory = args[++i]; break;
                    case "-h": result.HintDirectory = args[++i]; break;
                    case "-hc": result.HintCollection = true; break;
                    case "-ns": result.SaveResultFiles = false; break;
                    case "-name": result.JobDisplayName = args[i++]; break;
                    case "--":
                        result.FStarArguments = new string[args.Length - i - 1];
                        for (int j = i + 1; j < args.Length; j++)
                            result.FStarArguments[j - i - 1] = args[j];
                        i = args.Length;
                        break;
                    default:
                        Console.WriteLine("Unknown option: {0}", args[i]);
                        return null;
                }
            }

            if (result.BatchIDFile != null && File.Exists(result.BatchIDFile))
            {
                using (StreamReader sr = new StreamReader(result.BatchIDFile))
                {
                    result.PackageBlobId = sr.ReadLine();
                    result.JobId = sr.ReadLine();
                }
            }

            switch (result.Command)
            {
                case "delete":
                    if (result.JobId == null)
                    {
                        Console.WriteLine("{0} requires -j or -i", result.Command);
                        return null;
                    }
                    break;
                default: break;
            }

            return result;
        }

        internal static string Usage =
            @"Usage: fabc.exe <command> <arguments>

             Options:
               -b <id>        package blob id
               -j             job id
               -i <path>      Batch IDs file
               -d <path>      directory within package
               -ns            don't save result files
               -h <path>      path to *.hints files
               -hc            collect *.hints files

             Commands:
               add
               create
               await
               list
               delete";
    }
}
