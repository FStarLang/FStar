open Prims
let main : 'uuuuu 'uuuuu1 . 'uuuuu -> 'uuuuu1 =
  fun argv ->
    FStar_Compiler_Util.print_string "Initializing tests...\n";
    (try
       (fun uu___1 ->
          match () with
          | () ->
              let uu___2 = FStar_Options.parse_cmd_line () in
              (match uu___2 with
               | (res, fs) ->
                   (match res with
                    | FStar_Getopt.Help ->
                        (FStar_Compiler_Util.print_string
                           "F* unit tests. This binary can take the same options as F*, but not all of them are meaningful.";
                         FStar_Compiler_Effect.exit Prims.int_zero)
                    | FStar_Getopt.Error msg ->
                        (FStar_Compiler_Util.print_error msg;
                         FStar_Compiler_Effect.exit Prims.int_one)
                    | FStar_Getopt.Empty ->
                        (FStar_Main.setup_hooks ();
                         (let uu___5 = FStar_Tests_Pars.init () in
                          FStar_Compiler_Effect.op_Bar_Greater uu___5
                            (fun uu___6 -> ()));
                         FStar_Tests_Norm.run_all ();
                         (let uu___7 = FStar_Tests_Unif.run_all () in
                          if uu___7
                          then ()
                          else FStar_Compiler_Effect.exit Prims.int_one);
                         FStar_Compiler_Effect.exit Prims.int_zero)
                    | FStar_Getopt.Success ->
                        (FStar_Main.setup_hooks ();
                         (let uu___5 = FStar_Tests_Pars.init () in
                          FStar_Compiler_Effect.op_Bar_Greater uu___5
                            (fun uu___6 -> ()));
                         FStar_Tests_Norm.run_all ();
                         (let uu___7 = FStar_Tests_Unif.run_all () in
                          if uu___7
                          then ()
                          else FStar_Compiler_Effect.exit Prims.int_one);
                         FStar_Compiler_Effect.exit Prims.int_zero)))) ()
     with
     | FStar_Errors.Error (err, msg, r, _ctx) when
         let uu___2 = FStar_Options.trace_error () in
         FStar_Compiler_Effect.op_Less_Bar Prims.op_Negation uu___2 ->
         (if r = FStar_Compiler_Range_Type.dummyRange
          then FStar_Compiler_Util.print_string msg
          else
            (let uu___4 = FStar_Compiler_Range_Ops.string_of_range r in
             FStar_Compiler_Util.print2 "%s: %s\n" uu___4 msg);
          FStar_Compiler_Effect.exit Prims.int_one)
     | FStar_Errors.Err (raw_error, s, ls) when
         let uu___2 = FStar_Options.trace_error () in
         FStar_Compiler_Effect.op_Less_Bar Prims.op_Negation uu___2 ->
         (FStar_Compiler_Util.print2 "%s : [%s]\n" s
            (FStar_String.concat "; " ls);
          FStar_Compiler_Effect.exit Prims.int_one)
     | e ->
         ((let uu___3 = FStar_Compiler_Util.message_of_exn e in
           let uu___4 = FStar_Compiler_Util.trace_of_exn e in
           FStar_Compiler_Util.print2_error "Error\n%s\n%s\n" uu___3 uu___4);
          FStar_Compiler_Effect.exit Prims.int_one))