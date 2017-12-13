open Prims
let main: 'Auu____4 'Auu____5 . 'Auu____5 -> 'Auu____4 =
  fun argv  ->
    FStar_Util.print_string "Initializing ...\n";
    (try
       (let uu____17 = FStar_Tests_Pars.init () in
        FStar_All.pipe_right uu____17 FStar_Pervasives.ignore);
       FStar_Tests_Norm.run_all ();
       FStar_Tests_Unif.run_all ();
       FStar_All.exit (Prims.parse_int "0")
     with
     | FStar_Errors.Error (msg,r) when
         let uu____27 = FStar_Options.trace_error () in
         FStar_All.pipe_left Prims.op_Negation uu____27 ->
         (if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____30 = FStar_Range.string_of_range r in
             FStar_Util.print2 "%s: %s\n" uu____30 msg);
          FStar_All.exit (Prims.parse_int "1")))