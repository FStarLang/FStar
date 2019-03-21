open Prims
let main : 'Auu____79350 'Auu____79351 . 'Auu____79350 -> 'Auu____79351 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_79363  ->
          match () with
          | () ->
              ((let uu____79365 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____79365 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____79368 = FStar_Tests_Unif.run_all ()  in
                if uu____79368
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____79386 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____79386 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____79394 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____79394 msg);
          FStar_All.exit (Prims.parse_int "1")))
  