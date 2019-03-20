open Prims
let main : 'Auu____79330 'Auu____79331 . 'Auu____79330 -> 'Auu____79331 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_79343  ->
          match () with
          | () ->
              ((let uu____79345 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____79345 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____79348 = FStar_Tests_Unif.run_all ()  in
                if uu____79348
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____79366 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____79366 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____79374 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____79374 msg);
          FStar_All.exit (Prims.parse_int "1")))
  