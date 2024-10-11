open Prims
let main : 'uuuuu 'uuuuu1 . 'uuuuu -> 'uuuuu1 =
  fun argv ->
    FStarC_Compiler_Util.print_string "Initializing tests...\n";
    (try
       (fun uu___1 ->
          match () with
          | () ->
              let uu___2 = FStarC_Options.parse_cmd_line () in
              (match uu___2 with
               | (res, fs) ->
                   (match res with
                    | FStarC_Getopt.Help ->
                        (FStarC_Compiler_Util.print_string
                           "F* unit tests. This binary can take the same options as F*, but not all of them are meaningful.";
                         FStarC_Compiler_Effect.exit Prims.int_zero)
                    | FStarC_Getopt.Error msg ->
                        (FStarC_Compiler_Util.print_error msg;
                         FStarC_Compiler_Effect.exit Prims.int_one)
                    | FStarC_Getopt.Empty ->
                        (FStarC_Main.setup_hooks ();
                         (let uu___5 = FStarC_Tests_Pars.init () in ());
                         FStarC_Tests_Pars.parse_incremental_decls ();
                         FStarC_Tests_Pars.parse_incremental_decls_use_lang
                           ();
                         FStarC_Tests_Norm.run_all ();
                         (let uu___9 = FStarC_Tests_Unif.run_all () in
                          if uu___9
                          then ()
                          else FStarC_Compiler_Effect.exit Prims.int_one);
                         FStarC_Tests_Data.run_all ();
                         (let uu___11 = FStarC_Errors.report_all () in ());
                         (let nerrs = FStarC_Errors.get_err_count () in
                          if nerrs > Prims.int_zero
                          then FStarC_Compiler_Effect.exit Prims.int_one
                          else ();
                          FStarC_Compiler_Effect.exit Prims.int_zero))
                    | FStarC_Getopt.Success ->
                        (FStarC_Main.setup_hooks ();
                         (let uu___5 = FStarC_Tests_Pars.init () in ());
                         FStarC_Tests_Pars.parse_incremental_decls ();
                         FStarC_Tests_Pars.parse_incremental_decls_use_lang
                           ();
                         FStarC_Tests_Norm.run_all ();
                         (let uu___9 = FStarC_Tests_Unif.run_all () in
                          if uu___9
                          then ()
                          else FStarC_Compiler_Effect.exit Prims.int_one);
                         FStarC_Tests_Data.run_all ();
                         (let uu___11 = FStarC_Errors.report_all () in ());
                         (let nerrs = FStarC_Errors.get_err_count () in
                          if nerrs > Prims.int_zero
                          then FStarC_Compiler_Effect.exit Prims.int_one
                          else ();
                          FStarC_Compiler_Effect.exit Prims.int_zero))))) ()
     with
     | FStarC_Errors.Error (err, msg, r, _ctx) when
         let uu___2 = FStarC_Options.trace_error () in
         Prims.op_Negation uu___2 ->
         (if r = FStarC_Compiler_Range_Type.dummyRange
          then
            (let uu___3 = FStarC_Errors_Msg.rendermsg msg in
             FStarC_Compiler_Util.print_string uu___3)
          else
            (let uu___4 = FStarC_Compiler_Range_Ops.string_of_range r in
             let uu___5 = FStarC_Errors_Msg.rendermsg msg in
             FStarC_Compiler_Util.print2 "%s: %s\n" uu___4 uu___5);
          FStarC_Compiler_Effect.exit Prims.int_one)
     | e ->
         ((let uu___3 = FStarC_Compiler_Util.message_of_exn e in
           let uu___4 = FStarC_Compiler_Util.trace_of_exn e in
           FStarC_Compiler_Util.print2_error "Error\n%s\n%s\n" uu___3 uu___4);
          FStarC_Compiler_Effect.exit Prims.int_one))