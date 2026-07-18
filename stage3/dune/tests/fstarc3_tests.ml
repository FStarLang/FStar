let x =
      (* On Unix, if we write to a pipe that tries to send something
         to a process that died, we receive a SIGPIPE signal which
         by default will terminate F*, and we won't get an exception
         or anything. So, block them, and instead rely on OCaml exceptions
         to detect this. *)
      if Fstarcompiler.FStarC_Platform.unix then
        ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigpipe]);

      (* Kill all lingering Z3 subprocesses if we are being killed with
         a SIGTERM. This is what VS Code sends when a file is closed. *)
      if Fstarcompiler.FStarC_Platform.unix then (
        let hdlr (s:int) =
          Fstarcompiler.FStarC_Util.kill_all ();
          exit 130
        in
        let _ = Sys.signal Sys.sigterm (Sys.Signal_handle hdlr) in
        ()
      );

      (* Enable memtrace, only if the environment variable MEMTRACE is set. *)
      Memtrace.trace_if_requested ();

      (* Record a backtrace on exceptions, for --trace_error. *)
      Printexc.record_backtrace true;

      (* Tweak garbage collector parameters. *)
      Gc.set { (Gc.get()) with Gc.minor_heap_size = 1048576; Gc.major_heap_increment = 4194304; Gc.space_overhead = 150; };

      FStarC_Tests_Test.main ()
