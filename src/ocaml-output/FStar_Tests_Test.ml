open Prims
let main : 'Auu____84554 'Auu____84555 . 'Auu____84554 -> 'Auu____84555 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_84567  ->
          match () with
          | () ->
              ((let uu____84569 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____84569 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____84572 = FStar_Tests_Unif.run_all ()  in
                if uu____84572
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____84590 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____84590 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____84598 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____84598 msg);
          FStar_All.exit (Prims.parse_int "1")))
  