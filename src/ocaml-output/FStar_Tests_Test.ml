open Prims
let main : 'Auu____6 'Auu____7 . 'Auu____6 -> 'Auu____7 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (fun uu___3_19  ->
          match () with
          | () ->
              ((let uu____21 = FStar_Tests_Pars.init ()  in
                FStar_All.pipe_right uu____21 (fun uu____22  -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu____25 = FStar_Tests_Unif.run_all ()  in
                if uu____25 then () else FStar_All.exit Prims.int_one);
               FStar_All.exit Prims.int_zero)) ()
     with
     | FStar_Errors.Error (err,msg,r) when
         let uu____43 = FStar_Options.trace_error ()  in
         FStar_All.pipe_left Prims.op_Negation uu____43 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____51 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____51 msg);
          FStar_All.exit Prims.int_one))
  