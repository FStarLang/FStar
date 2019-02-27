open Prims
let main : 'Auu____84582 'Auu____84583 . 'Auu____84582 -> 'Auu____84583 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_84595  ->
          match () with
          | () ->
              ((let uu____84597 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____84597 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____84600 = FStar_Tests_Unif.run_all ()  in
                if uu____84600
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____84618 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____84618 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____84626 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____84626 msg);
          FStar_All.exit (Prims.parse_int "1")))
  