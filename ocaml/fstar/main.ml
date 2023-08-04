let x =
      (* If we write to a pipe that tries to send something to a
         process that died, we receive a SIGPIPE signal which
         by defaults will terminate F*, and we won't get an exception
         or anything. So, block them, and instead rely on OCaml exceptions
         to detect this. *)
      if FStar_Platform.system = Posix then
        ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigpipe]);

      Printexc.record_backtrace true;
      Gc.set { (Gc.get()) with Gc.minor_heap_size = 1048576; Gc.major_heap_increment = 4194304; Gc.space_overhead = 150; };
      FStar_Main.main ()
