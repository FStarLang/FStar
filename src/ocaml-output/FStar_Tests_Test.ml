open Prims
let main : 'Auu____7 'Auu____8 . 'Auu____7 -> 'Auu____8 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___472_20  ->
          match () with
          | () ->
              (FStar_Main.setup_hooks ();
               (let uu____23 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____23 (fun a239  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____26 = FStar_Tests_Unif.run_all ()  in
                if uu____26 then () else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____37 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____37 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____40 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____40 msg);
          FStar_All.exit (Prims.parse_int "1")))
  