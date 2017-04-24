// Copyright (C) 2017 Microsoft Research
// Author: Christoph M. Wintersteiger (cwinter)

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

using Microsoft.Azure.Batch;
using Microsoft.Azure.Batch.Auth;
using Microsoft.Azure.Batch.Common;

using Microsoft.WindowsAzure.Storage;
using Microsoft.WindowsAzure.Storage.Blob;
using Microsoft.WindowsAzure.Storage.Auth;

namespace fabc_make
{
    class Program
    {
        private static string StorageAccountName = null;
        private static string StorageAccountAccessKey = null;
        private static string PackageBlobContainer = null;

        private static string BatchAccountName = null;
        private static string BatchAccessKey = null;
        private static string BatchUri = null;
        private static string PoolID = null;

        private static string JobIDPrefix = null;
        private static string PkgLocalName = "pkg.zip";
        private static TimeSpan PkgUpdateTimeout = new TimeSpan(0, 1, 0);
        private static TimeSpan TaskRetentionTime = new TimeSpan(48, 00, 00);
        private static TimeSpan TaskMaxWallClockTime = new TimeSpan(12, 00, 00);
        private static int TaskMaxRetryCount = 1;
        private static string CSVFilename = "results.csv";
        private static string JobDisplayName = "MyJob";

        private static int MaxParallelDownloads = 16;

        private static string FStarHome = null;
        private static string Z3 = null;

        public static StorageCredentials SACredentials = null;
        public static CloudStorageAccount SA = null;
        public static CloudBlobClient CBC = null;

        private static BatchClient bc;
        private static int NumTasks = 1;

        private static CancellationTokenSource source = new CancellationTokenSource();
        private static CancellationToken token = source.Token;

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
                    //Console.WriteLine("{0}={1}", option, value);
                    switch (option)
                    {
                        case "StorageAccountName": StorageAccountName = value; break;
                        case "StorageAccountAccessKey": StorageAccountAccessKey = value; break;
                        case "PackageBlobContainer": PackageBlobContainer = value; break;
                        case "TasksBlobContainer": /* not used for now */; break;
                        case "BatchAccountName": BatchAccountName = value; break;
                        case "BatchAccessKey": BatchAccessKey = value; break;
                        case "BatchUri": BatchUri = value; break;
                        case "PoolID": PoolID = value; break;
                        case "JobIDPrefix": JobIDPrefix = value; break;
                        case "PkgLocalName": PkgLocalName = value; break;
                        case "PkgUpdateTimeout": PkgUpdateTimeout = TimeSpan.Parse(value); break;
                        case "TaskRetentionTime": TaskRetentionTime = TimeSpan.Parse(value); break;
                        case "TaskMaxWallClockTime": TaskMaxWallClockTime = TimeSpan.Parse(value); break;
                        case "TaskMaxRetryCount": TaskMaxRetryCount = Convert.ToInt32(value); break;
                        case "CSVFilename": CSVFilename = value; break;
                        case "JobDisplayName": JobDisplayName = value; break;
                        case "MaxParallelDownloads": MaxParallelDownloads = Convert.ToInt32(value); break;
                        case "FStarHome": FStarHome = value; break;
                        case "Z3": Z3 = value; break;
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
                CommandLine = "sudo apt-get install -y unzip mono-runtime libmono-system-numerics4.0-cil libmono-system-runtime-serialization4.0-cil libgomp1",
                UserIdentity = new UserIdentity(new AutoUserSpecification(elevationLevel: ElevationLevel.Admin))
            };
            r.Commit();

            return bc.PoolOperations.GetPool(PoolID);
        }

        static void UpdatePackageIfNewer(Arguments myargs)
        {
            if (!File.Exists(myargs.Package))
                throw new Exception("File missing: " + myargs.Package);

            CloudBlobContainer container = CBC.GetContainerReference(PackageBlobContainer);
            container.CreateIfNotExists(BlobContainerPublicAccessType.Blob);

            string prefix = myargs.PackageBlobId == null ? "" : myargs.PackageBlobId;
            do
            {
                myargs.PackageBlobId = prefix + Guid.NewGuid().ToString();
            }
            while (container.GetBlockBlobReference(myargs.PackageBlobId).Exists());

            container.GetBlockBlobReference(myargs.PackageBlobId).UploadFromByteArray(new byte[] { }, 0, 0);
            ICloudBlob blob = container.GetBlobReferenceFromServer(myargs.PackageBlobId);

            blob.FetchAttributes();
            if (blob.Properties.Length == 0 ||
                !blob.Properties.LastModified.HasValue ||
                 blob.Properties.LastModified.Value < File.GetLastWriteTime(myargs.Package))
            {
                if (myargs.BatchIDFile != null)
                {
                    double sz = new FileInfo(myargs.Package).Length / 1024.0 / 1024.0;
                    Console.WriteLine("Uploading package ({0} MiB) ...", sz.ToString("F"));
                }
                
                blob.UploadFromFile(myargs.Package, null, 
                    new BlobRequestOptions() { MaximumExecutionTime=PkgUpdateTimeout }, 
                    null);
            }
        }

        

        static void DeletePackageBlob(Arguments myargs)
        {
            if (myargs.PackageBlobId == null)
                return;

            CloudBlobContainer container = CBC.GetContainerReference(PackageBlobContainer);

            if (!container.Exists())
                return;

            ICloudBlob blob = container.GetBlobReferenceFromServer(myargs.PackageBlobId);
            blob.Delete();
            Console.WriteLine("Package blob deleted.");
        }

        public static CloudJob MkJob(string displayName, bool showInfo)
        {
            string jID = "";

            try
            {
                do { jID = JobIDPrefix + Guid.NewGuid().ToString(); }
                while (bc.JobOperations.GetJob(jID) != null);
            }
            catch (BatchException ex) when (ex.RequestInformation.BatchError.Code == "JobNotFound") { }

            if (showInfo)
                Console.WriteLine("Creating job '{0}' ...", jID);

            PoolInformation pi = new PoolInformation();
            pi.PoolId = PoolID;
            CloudJob j = bc.JobOperations.CreateJob(jID, pi);
            j.OnAllTasksComplete = OnAllTasksComplete.NoAction;
            j.OnTaskFailure = OnTaskFailure.NoAction;
            j.Constraints = new JobConstraints(new TimeSpan(24, 0, 0), 5);
            if (displayName != null) j.DisplayName = displayName;
            j.Commit();
            return bc.JobOperations.GetJob(j.Id);
        }

        public static string GetJobDirectoryName(string jobId, string displayName)
        {
            if (displayName == null)
                return jobId;

            string sane = displayName;
            try
            {
                sane = sane.Replace(':', '_');
                return sane + " (" + jobId + ")";
            }
            catch
            {
                Console.WriteLine("Warning: could not create directory `" + sane + "'");
                return jobId;
            }
        }

        public static async Task<FStar.TaskResult> Collect(CloudJob j, CloudTask tsk)
        {
            ODATADetailLevel detail = new ODATADetailLevel(null, "id,displayName,state,commandLine,executionInfo,nodeInfo,stats,resourceFiles", "stats");
            do
            {
                try { await tsk.RefreshAsync(detail); } catch (TaskCanceledException) { }
            }
            while (tsk.Statistics == null);

            FStar.TaskResult tr = new FStar.TaskResult();
            tr.Id = tsk.Id;
            tr.Filepath = tsk.DisplayName;
            tr.ExitCode = tsk.ExecutionInformation.ExitCode.HasValue ? tsk.ExecutionInformation.ExitCode.Value : -1;
            tr.CPUTime = (tsk.Statistics.UserCpuTime + tsk.Statistics.KernelCpuTime).TotalSeconds;
            tr.WCTime = tsk.Statistics.WallClockTime.TotalSeconds;
            tr.WaitTime = tsk.Statistics.WaitTime.TotalSeconds;
            tr.Exception =
                tsk.ExecutionInformation.SchedulingError != null ?
                    new Exception(tsk.ExecutionInformation.SchedulingError.Message) : null;

            try { tsk.GetNodeFile("stdout.txt").CopyToStream(tr.StdOut); }
            catch (Exception ex) { (new StreamWriter(tr.StdOut)).WriteLine("Could not read stdout.txt: " + ex.Message); }
            tr.StdOut.Flush();

            try { tsk.GetNodeFile("stderr.txt").CopyToStream(tr.StdErr); }
            catch (Exception ex) { (new StreamWriter(tr.StdErr)).WriteLine("Could not read stderr.txt: " + ex.Message); }
            tr.StdErr.Flush();

            try
            {
                NodeFile nf = tsk.GetNodeFile("wd/" + FStar.OutFilesPkg);
                string tmpfn = Path.GetTempFileName();
                using (FileStream fs = new FileStream(tmpfn, FileMode.Create, FileAccess.Write))
                    nf.CopyToStream(fs);
                tr.OutFileTemp = tmpfn;
            }
            catch (FileNotFoundException) { /* OK */ }
            catch (BatchException ex)
                when (ex.RequestInformation.HttpStatusCode == System.Net.HttpStatusCode.NotFound)
            { /* OK */}
            catch (Exception ex) { Console.WriteLine("Exception: " + ex.Message); }

            StreamWriter sw = new StreamWriter(tr.Info);
            sw.WriteLine(String.Format("[ Result of: {0} ]", tsk.CommandLine));
            sw.WriteLine(String.Format("[ Node: {0} ]", tsk.ComputeNodeInformation.ComputeNodeId));
            sw.WriteLine(String.Format("[ ExitCode: {0} ]", tr.ExitCode));
            sw.WriteLine(String.Format("[ Timing: start@{0} end@{1} diff={2} cpu={3} wc={4} sec. ]",
                            tsk.ExecutionInformation.StartTime.Value.ToLongTimeString(),
                            tsk.ExecutionInformation.EndTime.Value.ToLongTimeString(),
                            (tsk.ExecutionInformation.EndTime.Value - tsk.ExecutionInformation.StartTime.Value).TotalSeconds,
                            tr.CPUTime,
                            tr.WCTime
                            ));
            sw.WriteLine(String.Format("[ WaitTime: {0} sec. ]", tr.WaitTime));
            sw.Flush();

            tr.StdOut.Seek(0, SeekOrigin.Begin);
            tr.StdErr.Seek(0, SeekOrigin.Begin);
            tr.Info.Seek(0, SeekOrigin.Begin);

            return tr;
        }

        public static async Task<CloudTask> Submit(CloudJob j, FStar.Task t, Arguments myargs)
        {
            string PkgBlobUri = "https://" + StorageAccountName + ".blob.core.windows.net/" + PackageBlobContainer + "/" + myargs.PackageBlobId;

            string taskId = "T" + (NumTasks++).ToString("D6");
            string cmdline = "bash -c \"(unzip -uq " + PkgLocalName + ") ; " + t.CommandLine() + "\"";
            CloudTask tsk = new CloudTask(taskId, cmdline);
            tsk.ResourceFiles = new List<ResourceFile>() {
                new ResourceFile(PkgBlobUri, PkgLocalName)
            };
            tsk.Constraints = new TaskConstraints(TaskMaxWallClockTime, TaskRetentionTime, TaskMaxRetryCount);

            if (t.Filepath != null)
                tsk.DisplayName = t.Filepath;

            retry:
            try { await j.AddTaskAsync(tsk); }
            catch (TaskCanceledException) { goto retry; }

            retry2:
            try { await j.CommitChangesAsync(); }
            catch (TaskCanceledException) { goto retry2; }

            return null;
        }

        static bool InitPackage(Arguments myargs)
        {
            if (myargs.BatchIDFile != null)
                Console.WriteLine("Creating package ...");

            string np = FStar.MakePackage(FStarHome, Z3, myargs.PackageContents);

            if (myargs.Package == null)
                myargs.Package = np;
            else
                File.Move(np, myargs.Package);

            UpdatePackageIfNewer(myargs);

            try { File.Delete(myargs.Package); } catch { }

            return true;
        }

        static void ListJobs(Arguments myargs)
        {
            ODATADetailLevel jobDetail;
            if (myargs.JobId == null)
                jobDetail = new ODATADetailLevel("startswith(id,'" + JobIDPrefix + "')", "id,displayName", null);
            else
                jobDetail = new ODATADetailLevel("id eq '" + myargs.JobId + "'", "id,displayName", null);
            IPagedEnumerable<CloudJob> jobs = bc.JobOperations.ListJobs(jobDetail);

            Console.WriteLine("{0,-50}==={1,-50}=|=================|", new string('=', 50), new string('=', 50));
            Console.WriteLine("{0,-50} | {1,-50} |  C / R / A / P  |", "Id", "DisplayName");
            Console.WriteLine("{0,-50}---{1,-50}-|-----------------|", new string('-', 50), new string('-', 50));

            int g_completed = 0, g_running = 0, g_active = 0, g_preparing = 0;

            foreach (CloudJob j in jobs)
            {
                if (!j.Id.StartsWith(JobIDPrefix))
                    continue;

                ODATADetailLevel taskDetail = new ODATADetailLevel("state eq 'Completed'", "id,state", null);
                int completed = j.ListTasks(taskDetail).Count();
                taskDetail = new ODATADetailLevel("state eq 'Running'", "id,state", null);
                int running = j.ListTasks(taskDetail).Count();
                taskDetail = new ODATADetailLevel("state eq 'Active'", "id,state", null);
                int active = j.ListTasks(taskDetail).Count();
                taskDetail = new ODATADetailLevel("state eq 'Preparing'", "id,state", null);
                int preparing = j.ListTasks(taskDetail).Count();
                g_completed += completed;
                g_running += running;
                g_active += active;
                g_preparing += preparing;

                string id = j.Id.Length > 50 ? j.Id.Substring(0, 49) + "*" : j.Id;
                string dn = j.DisplayName != null ? (j.DisplayName.Length < 50 ? j.DisplayName : j.DisplayName.Substring(0, 50)) : "";
                Console.WriteLine(String.Format("{0,-50} | {1,-50} | {2,3}/{3,3}/{4,3}/{5,3} |", id, dn, completed, running, active, preparing));
            }
            Console.WriteLine(new string('=', 50) + "===" + new string('=', 50) + "=|=================|");

            Console.WriteLine();
            CloudPool pool = GetOrCreatePool();
            Console.WriteLine("Pool: " + PoolID + " (" + pool.ListComputeNodes().Count() + " nodes, " + pool.AllocationState + ")");
            Console.WriteLine("Tasks: {0} completed, {1} running, {2} active, {3} preparing, {4} total.",
                              g_completed, g_running, g_active, g_preparing,
                              g_completed + g_running + g_active + g_preparing);
        }

        static async Task DeleteJob(string jobId)
        {
            ODATADetailLevel taskDetail = new ODATADetailLevel(null, "id,resourceFiles", null);

            CloudJob job = await bc.JobOperations.GetJobAsync(jobId);
            IPagedEnumerable<CloudTask> tasks = job.ListTasks(taskDetail);
            List<string> blob_uris = new List<string>();

            foreach (CloudTask tsk in tasks)
                foreach (ResourceFile rf in tsk.ResourceFiles)
                    if (!blob_uris.Contains(rf.BlobSource))
                        blob_uris.Add(rf.BlobSource);

            foreach (string uri in blob_uris)
            {
                try
                {
                    ICloudBlob blob = CBC.GetBlobReferenceFromServer(new Uri(uri));
                    await blob.DeleteAsync();
                }
                catch { /* OK */ }
            }

            await job.DeleteAsync();
        }

        static void Delete(Arguments myargs)
        {
            Debug.Assert(myargs.JobId != null);
            DeleteJob(myargs.JobId).Wait();
        }


        static int Create(Arguments myargs)
        {
            CloudJob j;

            if (myargs.JobId != null)
            {
                j = bc.JobOperations.GetJob(myargs.JobId);
                if (j.State != JobState.Enabling &&
                    j.State != JobState.Completed &&
                    j.State != JobState.Active)
                    throw new Exception("Job with id '" + myargs.JobId + "' in non-reusable state.");
            }


            myargs.PackageContents =
                new List<string>() {
                    @"bin|*.exe",
                    @"ulib|*.fst",
                    @"ulib|*.fsti",
                    @"examples|*.fst",
                    @"examples|*.fsti",
                    @"ucontrib|*.fst",
                    @"ucontrib|*.fsti",
                    @"doc|*.fst",
                    @"doc|*.fsti"
                };

            // myargs.PackageContents.Add(@"bin|*.dll");

            if (myargs.HintDirectory != null)
                myargs.PackageContents.Add(myargs.HintDirectory + "|*.hints");


            if (!InitPackage(myargs))
                return 1;

            j = MkJob(JobDisplayName, myargs.BatchIDFile != null);

            if (myargs.BatchIDFile != null)
            {
                using (StreamWriter sw = new StreamWriter(myargs.BatchIDFile))
                {                    
                    sw.WriteLine(myargs.PackageBlobId);
                    sw.WriteLine(j.Id);
                }
            }
            else
            {
                Console.WriteLine(myargs.PackageBlobId);
                Console.WriteLine(j.Id);
            }

            return 0;
        }


        static int Add(Arguments myargs)
        {
            if (myargs.JobId == null)
                throw new Exception("add requires job id (-j or -i).");

            CloudJob j = bc.JobOperations.GetJob(myargs.JobId);

            string d = myargs.Directory.Replace(@"\", " / ");
            string sd = myargs.Directory != null ? ("cd " + d) : "";
            FStar.Task t = new FStar.Task("H=`pwd` ; " + sd + " ; " +
                                          String.Join(" ", myargs.FStarArguments));

            if (myargs.HintCollection)
                t.OutFileExtensions = new string[] { "hints" };

            string PkgBlobUri = "https://" + StorageAccountName + ".blob.core.windows.net/" + PackageBlobContainer + "/" + myargs.PackageBlobId;
            string taskId;
            ODATADetailLevel taskDetail;

            do
            {
                taskId = Guid.NewGuid().ToString();
                taskDetail = new ODATADetailLevel("id eq '" + taskId + "'", "id", null);
            }
            while (j.ListTasks(taskDetail).Count() != 0);

            string cmdline = "bash -c \"(unzip -uq " + PkgLocalName + ") ; " + t.CommandLine() + "\"";
            cmdline = cmdline.Replace("%HOME%", "$H");
            CloudTask tsk = new CloudTask(taskId, cmdline);
            tsk.ResourceFiles = new List<ResourceFile>() {
                new ResourceFile(PkgBlobUri, PkgLocalName)
            };
            tsk.Constraints = new TaskConstraints(TaskMaxWallClockTime, TaskRetentionTime, TaskMaxRetryCount);
            tsk.DisplayName = d + "/" + myargs.FStarArguments.Last();

            retry:
            try { j.AddTask(tsk); }
            catch (TaskCanceledException) { goto retry; }

            retry2:
            try { j.CommitChanges(); }
            catch (TaskCanceledException) { goto retry2; }

            return 0;
        }

        static int Await(Arguments myargs)
        {
            if (myargs.JobId == null)
            {
                ODATADetailLevel jobDetail;
                if (myargs.JobId == null)
                    jobDetail = new ODATADetailLevel("startswith(id,'" + JobIDPrefix + "')", "id,displayName", null);
                else
                    jobDetail = new ODATADetailLevel("id eq '" + myargs.JobId + "'", "id,displayName", null);
                IPagedEnumerable<CloudJob> jobs = bc.JobOperations.ListJobs(jobDetail);

                foreach (CloudJob j in jobs)
                {
                    if (!j.Id.StartsWith(JobIDPrefix))
                        continue;

                    int r = Await(j.Id, myargs.SaveResultFiles);

                    if (r != 0)
                        return r;
                }

                return 0;
            }
            else
                return Await(myargs.JobId, myargs.SaveResultFiles);
        }

        static int Await(string jobId, bool saveResultFiles)
        {
            CloudJob j = bc.JobOperations.GetJob(jobId);

            string resultFileDir = null;
            if (saveResultFiles)
            {
                resultFileDir = GetJobDirectoryName(j.Id, j.DisplayName);
                if (!Directory.Exists(resultFileDir))
                    Directory.CreateDirectory(resultFileDir);
            }

            bool done = false;
            int exitCode = 0;
            object ecLock = new object();

            while (!done)
            {
                List<Task> tasks = new List<Task>();
                ODATADetailLevel taskDetail = new ODATADetailLevel("state eq 'completed'", "id,state,displayName", null);

                IPagedEnumerable<CloudTask> tsklst = j.ListTasks(taskDetail);
                foreach (CloudTask ct in tsklst)
                {
                    tasks.Add(Task.Run(async () =>
                    {
                        FStar.TaskResult tr = await Collect(j, ct);

                        if (tr != null && resultFileDir != null)
                            tr.SaveTo(resultFileDir, CSVFilename);

                        lock (ecLock)
                        {
                            if (tr.ExitCode != 0)
                                exitCode = tr.ExitCode;

                            Console.WriteLine(ct.CommandLine);
                            tr.StdOut.Seek(0, SeekOrigin.Begin);
                            tr.StdErr.Seek(0, SeekOrigin.Begin);
                            tr.StdOut.CopyTo(Console.OpenStandardOutput());

                            using (StreamReader sr = new StreamReader(tr.StdErr))
                            {
                                string s = sr.ReadToEnd();
                                string [] lines = s.Split('\n');
                                for (int i = 0; i < lines.Length - 4; i++) // `time' outputs 4 lines
                                    Console.WriteLine(lines[i]);      
                            }

                            if (tr.ExitCode != 0)
                                Console.WriteLine("Command failed with exit code " + tr.ExitCode.ToString());
                        }

                        await ct.DeleteAsync();
                    }));


                    if (tasks.Count() >= MaxParallelDownloads)
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
                done = j.ListTasks(taskDetail).Count() == 0;
            }

            DeleteJob(j.Id).Wait();

            return exitCode;
        }

        static int Main(string[] args)
        {
            int exitCode = 1;

            Arguments myargs = Arguments.Get(args);

            if (myargs == null)
            {
                Console.WriteLine(Arguments.Usage);
            }
            else
            {
                try
                {
                    string config_file = ".fstar-secrets";
                    GetConfig(Path.Combine(System.Environment.GetEnvironmentVariable("HOME"), config_file));

                    Console.CancelKeyPress += delegate
                    {
                        Console.WriteLine();
                        Console.WriteLine("Interrupted.");
                        source.Cancel();
                    };

                    BatchSharedKeyCredentials batchCreds =
                        new BatchSharedKeyCredentials(BatchUri, BatchAccountName, BatchAccessKey);
                    bc = BatchClient.Open(batchCreds);
                    GetOrCreatePool();

                    switch (myargs.Command)
                    {
                        case "create":
                            exitCode = Create(myargs);
                            break;
                        case "add":
                            exitCode = Add(myargs);
                            break;
                        case "await":
                            exitCode = Await(myargs);
                            break;
                        case "list":
                            ListJobs(myargs);
                            exitCode = 0;
                            break;
                        case "delete":
                            Delete(myargs);
                            exitCode = 0;
                            break;
                        default:
                            Console.WriteLine("Unknown command: " + myargs.Command);
                            exitCode = 1;
                            break;
                    }
                }
                catch (AggregateException ex)
                {
                    Console.WriteLine("Unhandled aggregate exception: ");
                    foreach (Exception iex in ex.InnerExceptions)
                    {
                        Console.WriteLine("Unhandled exception: " + iex.Message);
                        Console.WriteLine(iex.StackTrace);
                    }
                }
                catch (Exception ex)
                {
                    Console.WriteLine("Unhandled exception: " + ex.ToString());
                }
                finally
                {
                    if (bc != null)
                        bc.Close();
                }                
            }

            // Console.WriteLine("Exit code: " + exitCode.ToString());
            return exitCode;
        }
    }
}
