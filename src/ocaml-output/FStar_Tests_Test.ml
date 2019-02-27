open Prims
let main : 'Auu____84641 'Auu____84642 . 'Auu____84641 -> 'Auu____84642 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_84654  ->
          match () with
          | () ->
              ((let uu____84656 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____84656 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____84659 = FStar_Tests_Unif.run_all ()  in
                if uu____84659
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____84677 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____84677 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____84685 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____84685 msg);
          FStar_All.exit (Prims.parse_int "1")))
  