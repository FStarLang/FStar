let x =
      Printexc.record_backtrace true;
      Gc.set { (Gc.get()) with Gc.minor_heap_size = 1048576; Gc.major_heap_increment = 4194304; Gc.space_overhead = 150; };
      print_string FStar_Options.fstar_bin_directory;
      FStar_Main.main ()
