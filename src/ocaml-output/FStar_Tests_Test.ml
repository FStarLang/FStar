open Prims
let main : 'Auu____80246 'Auu____80247 . 'Auu____80246 -> 'Auu____80247 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_80259  ->
          match () with
          | () ->
              ((let uu____80261 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____80261 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____80264 = FStar_Tests_Unif.run_all ()  in
                if uu____80264
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____80282 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____80282 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____80290 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____80290 msg);
          FStar_All.exit (Prims.parse_int "1")))
  