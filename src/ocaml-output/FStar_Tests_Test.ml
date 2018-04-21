open Prims
let main : 'Auu____7 'Auu____8 . 'Auu____7 -> 'Auu____8 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (let uu____21 = FStar_Tests_Pars.init ()  in
        FStar_All.pipe_right uu____21 (fun a249  -> ()));
       FStar_Tests_Norm.run_all ();
       FStar_Tests_Unif.run_all ();
       FStar_All.exit (Prims.lift_native_int (0))
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____33 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____33 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____36 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____36 msg);
          FStar_All.exit (Prims.lift_native_int (1))))
  