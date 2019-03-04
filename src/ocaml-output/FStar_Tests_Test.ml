open Prims
let main : 'Auu____84651 'Auu____84652 . 'Auu____84651 -> 'Auu____84652 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_84664  ->
          match () with
          | () ->
              ((let uu____84666 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____84666 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____84669 = FStar_Tests_Unif.run_all ()  in
                if uu____84669
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____84687 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____84687 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____84695 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____84695 msg);
          FStar_All.exit (Prims.parse_int "1")))
  