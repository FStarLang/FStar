// Copyright (C) 2017 Microsoft Research
// Author: Christoph M. Wintersteiger (cwinter)

using System;
using System.Collections.Generic;
using System.IO;
using System.IO.Compression;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

using Microsoft.Azure.Batch;
using Microsoft.Azure.Batch.Auth;
using Microsoft.Azure.Batch.Common;

using Microsoft.WindowsAzure.Storage;
using Microsoft.WindowsAzure.Storage.Blob;
using Microsoft.WindowsAzure.Storage.Auth;

namespace z3batch
{
    class Program
    {
        private static string StorageAccountName = null;
        private static string StorageAccountAccessKey = null;
        private static string TasksBlobContainer = null;

        private static string BatchAccountName = null;
        private static string BatchAccessKey = null;
        private static string BatchUri = null;
        private static string PoolID = null;

        private static string JobIDPrefix = null;
        private static TimeSpan TaskRetentionTime = new TimeSpan(48, 00, 00);
        private static TimeSpan TaskMaxWallClockTime = new TimeSpan(12, 00, 00);
        private static int TaskMaxRetryCount = 1;
        private static string JobDisplayName = "MyJob";
        private static string PkgLocalName = null;

        private static int MaxParallelDownloads = 16;

        private static string FStarHome = null;
        private static string Z3 = null;

        public static StorageCredentials SACredentials = null;
        public static CloudStorageAccount SA = null;
        public static CloudBlobClient CBC = null;

        private static BatchClient bc;

        private static CancellationTokenSource source = new CancellationTokenSource();
        private static CancellationToken token = source.Token;

        private static string Z3Options = "auto_config=false model=true smt.relevancy=2";

        static void GetConfig(string filename)
        {
            using (StreamReader sr = new StreamReader(filename))
            {
                do
                {
                    string line = sr.ReadLine();
                    if (line.TrimStart()[0] == '#')
                        continue;
                    string[] tokens = line.Split(new char[] { '=' }, 2);
                    string option = tokens[0];
                    string value = tokens[1];
                    switch (option)
                    {
                        case "StorageAccountName": StorageAccountName = value; break;
                        case "StorageAccountAccessKey": StorageAccountAccessKey = value; break;
                        case "TasksBlobContainer": TasksBlobContainer = value; break;
                        case "BatchAccountName": BatchAccountName = value; break;
                        case "BatchAccessKey": BatchAccessKey = value; break;
                        case "BatchUri": BatchUri = value; break;
                        case "PoolID": PoolID = value; break;
                        case "JobIDPrefix": JobIDPrefix = value; break;
                        case "PkgLocalName": PkgLocalName = value; break;
                        case "TaskRetentionTime": TaskRetentionTime = TimeSpan.Parse(value); break;
                        case "TaskMaxWallClockTime": TaskMaxWallClockTime = TimeSpan.Parse(value); break;
                        case "TaskMaxRetryCount": TaskMaxRetryCount = Convert.ToInt32(value); break;
                        case "JobDisplayName": JobDisplayName = value; break;
                        case "MaxParallelDownloads": MaxParallelDownloads = Convert.ToInt32(value); break;
                        case "FStarHome": FStarHome = value; break;
                        case "Z3": Z3 = value; break;
                        case "PackageBlobContainer": /* not used */; break;
                        case "CSVFilename": /* not used */; break;
                        default:
                            Console.WriteLine("Warning: unknown configuration setting '" + option + "'.");
                            break;
                    }
                }
                while (!sr.EndOfStream);
            }

            SACredentials = new StorageCredentials(StorageAccountName, StorageAccountAccessKey);
            SA = new CloudStorageAccount(SACredentials, true);
            CBC = SA.CreateCloudBlobClient();
        }

        static CloudPool GetOrCreatePool()
        {
            try { return bc.PoolOperations.GetPool(PoolID); }
            catch (BatchException) { }

            CloudPool r = bc.PoolOperations.CreatePool(PoolID,
                virtualMachineSize: "Standard_D1",
                virtualMachineConfiguration: new VirtualMachineConfiguration(
                    new ImageReference("UbuntuServer", "Canonical", "16.04.0-LTS", version: "latest"),
                    "batch.node.ubuntu 16.04"));

            r.AutoScaleEnabled = true;
            r.AutoScaleFormula =
                @"$averageActiveTaskCount = avg($ActiveTasks.GetSample(TimeInterval_Minute * 5, 50));
                  $TargetDedicated = min(max(8, $averageActiveTaskCount / 4), 128);
                  $NodeDeallocationOption=retaineddata;";
            r.AutoScaleEvaluationInterval = new TimeSpan(0, 5, 0); // 5 min is the minimal legal value?

            r.StartTask = new StartTask()
            {
                WaitForSuccess = true,
                MaxTaskRetryCount = 1,
                CommandLine = "apt-get install -y unzip mono-runtime libmono-system-numerics4.0-cil libmono-system-runtime-serialization4.0-cil",
                UserIdentity = new UserIdentity(new AutoUserSpecification(elevationLevel: ElevationLevel.Admin))
            };
            r.Commit();

            return bc.PoolOperations.GetPool(PoolID);
        }

        static void DumpTo(List<string> query, string[] labels, string filename)
        {
            using (StreamWriter sw = new StreamWriter(filename, false))
            {
                foreach (string l in query)
                    sw.Write(l + "\n");

                sw.Write("(prove-labels");
                foreach (string l in labels)
                    sw.Write(" " + l);
                sw.Write(")\n");
                sw.Write("(exit)\n");
                sw.Flush();
            }
        }

        static string UploadQuery(List<string> query, string [] labels)
        {
            if (!File.Exists(Z3))
                throw new FileNotFoundException("Could not find Z3 at " + Z3);

            CloudBlobContainer container = CBC.GetContainerReference(TasksBlobContainer);
            container.CreateIfNotExists(BlobContainerPublicAccessType.Blob);

            string blobId;
            do
            {
                blobId = Guid.NewGuid().ToString();
            }
            while (container.GetBlockBlobReference(blobId).Exists());


            string zipfn = Path.Combine(Path.GetTempPath(), Path.GetTempFileName());
            string qryfn = Path.Combine(Path.GetTempPath(), Path.GetTempFileName());

            using (FileStream zstr = new FileStream(zipfn, FileMode.Create))
            using (ZipArchive zip = new ZipArchive(zstr, ZipArchiveMode.Create))
            {
                DumpTo(query, labels, qryfn);
                zip.CreateEntryFromFile(Z3, Path.GetFileName(Z3), CompressionLevel.Optimal);
                zip.CreateEntryFromFile(qryfn, "query.smt2", CompressionLevel.Optimal);
            }

            container.GetBlockBlobReference(blobId).UploadFromByteArray(new byte[] { }, 0, 0);
            ICloudBlob blob = container.GetBlobReferenceFromServer(blobId);
            blob.UploadFromFile(zipfn);

            try { File.Delete(qryfn); } catch { }
            try { File.Delete(zipfn); } catch { }

            return blobId;
        }

        static CloudJob CreateJob(string displayName)
        {
            string _jID = "";

            try
            {
                do { _jID = JobIDPrefix + Guid.NewGuid().ToString(); }
                while (bc.JobOperations.GetJob(_jID) != null);
            }
            catch (BatchException ex) when (ex.RequestInformation.BatchError.Code == "JobNotFound") { }

            PoolInformation pi = new PoolInformation();
            pi.PoolId = PoolID;
            CloudJob j = bc.JobOperations.CreateJob(_jID, pi);
            j.OnAllTasksComplete = OnAllTasksComplete.NoAction;
            j.OnTaskFailure = OnTaskFailure.NoAction;
            j.Constraints = new JobConstraints(new TimeSpan(24, 0, 0), 5);
            if (displayName != null) j.DisplayName = displayName;
            j.Commit();
            return bc.JobOperations.GetJob(j.Id);
        }

        static async Task AddTasks(CloudJob job, string queryBlobId, string[] labels)
        {
            string BlobUri = "https://" + StorageAccountName + ".blob.core.windows.net/" + TasksBlobContainer + "/" + queryBlobId;

            foreach (string label in labels)
            {
                string taskId = label;
                string cmdline = "bash -c \"(unzip -uq " + PkgLocalName + ") ; chmod +x z3 ; " +
                                 "sed -i \\\"s/^(prove-labels\\(.*\\) " + label + "\\(.*\\)$/(check-sat\\1\\2/\\\" query.smt2 ; " +
                                 "z3 -smt2 -file:query.smt2 " + Z3Options + "\"";
                CloudTask tsk = new CloudTask(taskId, cmdline);
                tsk.ResourceFiles = new List<ResourceFile>() {
                    new ResourceFile(BlobUri, PkgLocalName)
                };
                tsk.Constraints = new TaskConstraints(TaskMaxWallClockTime, TaskRetentionTime, TaskMaxRetryCount);

                retry:
                try { await job.AddTaskAsync(tsk); }
                catch (TaskCanceledException) { goto retry; }

                retry2:
                try { await job.CommitChangesAsync(); }
                catch (TaskCanceledException) { goto retry2; }
            }
        }

        static List<string> proven = new List<string>();
        static List<string> errors = new List<string>();
        static int Await(CloudJob job)
        {
            bool done = false;
            int exitCode = 0;
            object ecLock = new object();

            while (!done)
            {
                List<Task> tasks = new List<Task>();
                ODATADetailLevel taskDetail = new ODATADetailLevel("state eq 'completed'", "id,state,displayName,executionInfo", null);

                IPagedEnumerable<CloudTask> tsklst = job.ListTasks(taskDetail);
                foreach (CloudTask ct in tsklst)
                {
                    tasks.Add(Task.Run(async () =>
                    {
                        MemoryStream stdout = new MemoryStream();
                        MemoryStream stderr = new MemoryStream();
                        ct.GetNodeFile("stdout.txt").CopyToStream(stdout);
                        ct.GetNodeFile("stderr.txt").CopyToStream(stderr);

                        int taskExitCode = ct.ExecutionInformation.ExitCode.Value;
                        lock (ecLock)
                        {
                            if (stderr.Length != 0)
                            {
                                Console.Write(ct.Id + ": Error: ");
                                stderr.CopyTo(Console.OpenStandardError());
                                Console.WriteLine();
                            }
                            else if (taskExitCode != 0)
                            {
                                Console.WriteLine(ct.Id + ": Unexpected exit code from task (" + taskExitCode + "); output: ");
                                stdout.Seek(0, SeekOrigin.Begin);
                                stderr.Seek(0, SeekOrigin.Begin);
                                stdout.CopyTo(Console.OpenStandardOutput());
                                stderr.CopyTo(Console.OpenStandardError());
                            }
                            else if (stdout.Length == 0)
                            {
                                Console.WriteLine(ct.Id + ": Error: no output from task.");
                            }
                            else
                            {
                                stdout.Seek(0, SeekOrigin.Begin);
                                string output = new string(Encoding.ASCII.GetChars(stdout.ToArray()));
                                output = output.Trim(' ', '\n', '\r');
                                if (output == "unsat")
                                    proven.Add(ct.Id);
                                else if (output == "sat" || output == "unknown")
                                    errors.Add(ct.Id);
                                else
                                {
                                    Console.WriteLine(ct.Id + ": Unexpected output from task: ");
                                    Console.WriteLine(output);
                                }
                            }

                            exitCode = taskExitCode > exitCode ? taskExitCode : exitCode;
                        }

                        await ct.DeleteAsync();
                    }));


                    if (tasks.Count >= MaxParallelDownloads)
                    {
                        try
                        {
                            int inx = Task.WaitAny(tasks.ToArray(), token);
                            tasks.RemoveAt(inx);
                        }
                        catch (OperationCanceledException) { /* OK */ }
                    }
                }

                Task.WaitAll(tasks.ToArray());

                taskDetail = new ODATADetailLevel(null, "id", null);
                IPagedEnumerable<CloudTask> pe = job.ListTasks(taskDetail);
                done = !pe.GetEnumerator().MoveNext();
            }

            return exitCode;
        }

        static int DetailErrors(List<string> query, string[] labels)
        {
            // DumpTo(query, labels, "detail_errors.smt2");

            BatchSharedKeyCredentials batchCreds =
                new BatchSharedKeyCredentials(BatchUri, BatchAccountName, BatchAccessKey);
            bc = BatchClient.Open(batchCreds);

            GetOrCreatePool();
            string queryBlobId = UploadQuery(query, labels);
            CloudJob job = CreateJob("FStar detail errors");
            AddTasks(job, queryBlobId, labels).Wait();
            int exitCode = Await(job);

            Console.Write("OK\n");

            foreach (string pl in proven)
                Console.Write(" " + pl);
            Console.Write("\n");

            foreach (string el in errors)
                Console.Write(" " + el);
            Console.Write("\n");

            job.Delete();
            CloudBlobContainer container = CBC.GetContainerReference(TasksBlobContainer);
            container.GetBlobReference(queryBlobId).Delete();

            return exitCode;
        }

        static int Main(string[] args)
        {
            int exitCode = 0;

            try
            {
                Stream stream = args.Length > 0 ? new FileStream(args[0], FileMode.Open) :
                                                  Console.OpenStandardInput();
                StreamReader streamRdr = new StreamReader(stream);
                string prove_labels_cmd = "(prove-labels ";
                string config_file = ".fstar-secrets";
                GetConfig(Path.Combine(System.Environment.GetEnvironmentVariable("HOME"), config_file));

                Console.CancelKeyPress += delegate
                {
                    Console.WriteLine();
                    Console.WriteLine("Interrupted.");
                    source.Cancel();
                };

                List<string> lines = new List<string>();
                string line = streamRdr.ReadLine();
                while (line != null)
                {
                    if (line.TrimStart(' ').StartsWith(prove_labels_cmd))
                    {
                        string lbl_str = line.TrimStart(' ').TrimEnd(' ').
                                            Substring(prove_labels_cmd.Length,
                                                      line.Length - prove_labels_cmd.Length - 1);
                        string[] labels = lbl_str.Split(' ');
                        exitCode = DetailErrors(lines, labels);
                        Console.WriteLine("Done!");
                        lines = new List<string>();
                    }
                    else if (line.Length == 6 && line == "(exit)")
                    {
                        return 0;
                    }
                    else
                    {
                        lines.Add(line);
                    }

                    line = streamRdr.ReadLine();
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine("Caught exception: " + ex.Message);
                Console.WriteLine("Stack trace: " + ex.StackTrace);
            }

            return exitCode;
        }
    }
}
