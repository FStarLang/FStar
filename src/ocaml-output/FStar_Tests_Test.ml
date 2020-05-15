open Prims
let main : 'uuuuuu6 'uuuuuu7 . 'uuuuuu6 -> 'uuuuuu7 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___3_20  ->
          match () with
          | () ->
              (FStar_Main.setup_hooks ();
               (let uu____23 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____23 (fun uu____24  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____27 = FStar_Tests_Unif.run_all ()  in
                if uu____27 then () else FStar_All.exit Prims.int_one);
               FStar_All.exit Prims.int_zero)) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____45 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____45 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____53 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____53 msg);
          FStar_All.exit Prims.int_one))
  