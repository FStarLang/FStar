open Prims
let main : 'uuuuu 'uuuuu1 . 'uuuuu -> 'uuuuu1 =
  fun argv ->
    FStar_Compiler_Util.print_string "Initializing ...\n";
    (try
       (fun uu___1 ->
          match () with
          | () ->
              (FStar_Main.setup_hooks ();
               (let uu___4 = FStar_Tests_Pars.init () in
                FStar_Compiler_Effect.op_Bar_Greater uu___4
                  (fun uu___5 -> ()));
               FStar_Tests_Norm.run_all ();
               (let uu___6 = FStar_Tests_Unif.run_all () in
                if uu___6
                then ()
                else FStar_Compiler_Effect.exit Prims.int_one);
               FStar_Compiler_Effect.exit Prims.int_zero)) ()
     with
     | FStar_Errors.Error (err, msg, r, _ctx) when
         let uu___2 = FStar_Options.trace_error () in
         FStar_Compiler_Effect.op_Less_Bar Prims.op_Negation uu___2 ->
         (if r = FStar_Compiler_Range.dummyRange
          then FStar_Compiler_Util.print_string msg
          else
            (let uu___4 = FStar_Compiler_Range.string_of_range r in
             FStar_Compiler_Util.print2 "%s: %s\n" uu___4 msg);
          FStar_Compiler_Effect.exit Prims.int_one))