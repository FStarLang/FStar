open Prims
let main : 'Auu____84674 'Auu____84675 . 'Auu____84674 -> 'Auu____84675 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___745_84687  ->
          match () with
          | () ->
              ((let uu____84689 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____84689 (fun a1  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____84692 = FStar_Tests_Unif.run_all ()  in
                if uu____84692
                then ()
                else FStar_All.exit (Prims.parse_int "1"));
               FStar_All.exit (Prims.parse_int "0"))) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____84710 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____84710 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____84718 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____84718 msg);
          FStar_All.exit (Prims.parse_int "1")))
  