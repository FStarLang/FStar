open Prims
let main : 'Auu____79442 'Auu____79443 . 'Auu____79442 -> 'Auu____79443 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_79455  ->
          match () with
          | () ->
              ((let uu____79457 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____79457 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____79460 = FStar_Tests_Unif.run_all ()  in
                if uu____79460
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____79478 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____79478 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____79486 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____79486 msg);
          FStar_All.exit (Prims.parse_int "1")))
  