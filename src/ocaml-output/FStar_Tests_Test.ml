open Prims
let main : 'Auu____7 'Auu____8 . 'Auu____7 -> 'Auu____8 =
  fun argv  ->
    let uu____14 = FStar_Util.print_string "Initializing ...\n"  in
    try
      let uu____20 =
        let uu____21 = FStar_Tests_Pars.init ()  in
        FStar_All.pipe_right uu____21 (fun a256  -> (Obj.magic ()) a256)  in
      let uu____22 = FStar_Tests_Norm.run_all ()  in
      let uu____23 = FStar_Tests_Unif.run_all ()  in
      FStar_All.exit (Prims.parse_int "0")
    with
    | FStar_Errors.Error (err,msg,r) when
        let uu____33 = FStar_Options.trace_error ()  in
        FStar_All.pipe_left Prims.op_Negation uu____33 ->
        let uu____34 =
          if r = FStar_Range.dummyRange
          then FStar_Util.print_string msg
          else
            (let uu____36 = FStar_Range.string_of_range r  in
             FStar_Util.print2 "%s: %s\n" uu____36 msg)
           in
        FStar_All.exit (Prims.parse_int "1")
  