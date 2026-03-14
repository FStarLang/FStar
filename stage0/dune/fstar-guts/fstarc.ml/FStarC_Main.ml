open Prims
let cleanup (uu___ : unit) : unit= FStarC_Util.kill_all ()
let print_stats (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang FStarC_Stats.ever_enabled in
  if uu___1
  then
    let uu___2 = FStarC_Stats.print_all () in
    FStarC_Format.print1_error "Stats:\n%s\n" uu___2
  else ()
let process_args (uu___ : unit) :
  (FStarC_Getopt.parse_cmdline_res * Prims.string Prims.list)=
  FStarC_Options.parse_cmd_line ()
let finished_message (fmods : (Prims.bool * FStarC_Ident.lident) Prims.list)
  (errs : Prims.int) : unit=
  let print_to =
    if errs > Prims.int_zero
    then FStarC_Format.print_error
    else FStarC_Format.print_string in
  let uu___ =
    let uu___1 = FStarC_Options.silent () in Prims.op_Negation uu___1 in
  if uu___
  then
    (FStarC_List.iter
       (fun uu___2 ->
          match uu___2 with
          | (iface, name) ->
              let tag = if iface then "i'face (or impl+i'face)" else "module" in
              let uu___3 =
                let uu___4 = FStarC_Ident.string_of_lid name in
                FStarC_Options.should_print_message uu___4 in
              if uu___3
              then
                let uu___4 =
                  let uu___5 = FStarC_Ident.string_of_lid name in
                  FStarC_Format.fmt2 "Verified %s: %s\n" tag uu___5 in
                print_to uu___4
              else ()) fmods;
     if errs > Prims.int_zero
     then
       (if errs = Prims.int_one
        then FStarC_Format.print_error "1 error was reported (see above)\n"
        else
          (let uu___3 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int errs in
           FStarC_Format.print1_error "%s errors were reported (see above)\n"
             uu___3))
     else
       (let uu___3 =
          FStarC_Format.colorize_bold
            "All verification conditions discharged successfully" in
        FStarC_Format.print1 "%s\n" uu___3))
  else ()
let report_errors (fmods : (Prims.bool * FStarC_Ident.lident) Prims.list) :
  unit=
  (let uu___1 = FStarC_Errors.report_all () in ());
  (let nerrs = FStarC_Errors.get_err_count () in
   if nerrs > Prims.int_zero
   then
     (finished_message fmods nerrs;
      print_stats ();
      cleanup ();
      FStarC_Effect.exit Prims.int_one)
   else ())
let load_native_tactics (uu___ : unit) : unit=
  let modules_to_load =
    let uu___1 = FStarC_Options.load () in
    FStarC_List.map FStarC_Ident.lid_of_str uu___1 in
  let cmxs_to_load =
    let uu___1 = FStarC_Options.load_cmxs () in
    FStarC_List.map FStarC_Ident.lid_of_str uu___1 in
  let ml_module_name m = FStarC_Extraction_ML_Util.ml_module_name_of_lid m in
  let ml_file m = let uu___1 = ml_module_name m in Prims.strcat uu___1 ".ml" in
  let cmxs_file m =
    let cmxs = let uu___1 = ml_module_name m in Prims.strcat uu___1 ".cmxs" in
    let uu___1 = FStarC_Find.find_file_odir cmxs in
    match uu___1 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None ->
        if FStarC_List.contains m cmxs_to_load
        then
          let uu___2 = FStarC_Format.fmt1 "Could not find %s to load" cmxs in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_FailToCompileNativeTactic ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2)
        else
          (let uu___3 =
             let uu___4 = ml_file m in FStarC_Find.find_file_odir uu___4 in
           match uu___3 with
           | FStar_Pervasives_Native.None ->
               let uu___4 =
                 let uu___5 =
                   FStarC_Errors_Msg.text "Failed to compile native tactic." in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       let uu___9 = ml_file m in
                       FStarC_Format.fmt1 "Extracted module %s not found."
                         uu___9 in
                     FStarC_Errors_Msg.text uu___8 in
                   [uu___7] in
                 uu___5 :: uu___6 in
               FStarC_Errors.raise_error0
                 FStarC_Errors_Codes.Fatal_FailToCompileNativeTactic ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                 (Obj.magic uu___4)
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStarC_Filepath.dirname ml in
               ((let uu___5 = let uu___6 = ml_module_name m in [uu___6] in
                 FStarC_Plugins.compile_modules dir uu___5);
                (let uu___5 = FStarC_Find.find_file_odir cmxs in
                 match uu___5 with
                 | FStar_Pervasives_Native.None ->
                     let uu___6 =
                       let uu___7 =
                         FStarC_Errors_Msg.text
                           "Failed to compile native tactic." in
                       let uu___8 =
                         let uu___9 =
                           let uu___10 =
                             FStarC_Format.fmt1
                               "Compilation seemingly succeeded, but compiled object %s not found."
                               cmxs in
                           FStarC_Errors_Msg.text uu___10 in
                         [uu___9] in
                       uu___7 :: uu___8 in
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_FailToCompileNativeTactic ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___6)
                 | FStar_Pervasives_Native.Some f -> f))) in
  let cmxs_files =
    FStarC_List.map cmxs_file
      (FStarC_List.op_At modules_to_load cmxs_to_load) in
  FStarC_Plugins.load_plugins cmxs_files;
  (let uu___3 = FStarC_Options.use_native_tactics () in
   FStarC_Option.iter FStarC_Plugins.load_plugins_dir uu___3)
let fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let set_error_trap (uu___ : unit) : unit=
  let h = FStarC_Util.get_sigint_handler () in
  let h' s =
    FStarC_Util.kill_all ();
    FStarC_Debug.enable ();
    FStarC_Options.set_option "error_contexts" (FStarC_Options.Bool true);
    (let uu___5 =
       let uu___6 = FStarC_Errors_Msg.text "GOT SIGINT! Exiting" in [uu___6] in
     FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
       FStarC_Range_Type.dummyRange ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic uu___5));
    print_stats ();
    FStarC_Effect.exit Prims.int_one in
  let uu___1 = FStarC_Util.sigint_handler_f h' in
  FStarC_Util.set_sigint_handler uu___1
let print_help_for (o : Prims.string) : unit=
  let uu___ = FStarC_Options.help_for_option o in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      FStarC_Format.print_string
        "Use `--help` to see all available options.\n"
  | FStar_Pervasives_Native.Some doc ->
      let uu___1 = FStarC_Errors_Msg.renderdoc doc in
      FStarC_Format.print_error uu___1
let go_normal (uu___ : unit) : unit=
  let uu___1 = process_args () in
  match uu___1 with
  | (res, filenames0) ->
      ((let uu___3 =
          ((let uu___4 = FStarC_Options.output_to () in
            FStar_Pervasives_Native.uu___is_Some uu___4) &&
             (let uu___4 =
                let uu___5 = FStarC_Options.dep () in
                FStar_Pervasives_Native.uu___is_Some uu___5 in
              Prims.op_Negation uu___4))
            && ((FStarC_List.length filenames0) > Prims.int_one) in
        if uu___3
        then
          let uu___4 =
            let uu___5 =
              FStarC_Errors_Msg.text
                "When using -o, you can only provide a single file in the\n        command line (except for dependency analysis)." in
            [uu___5] in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic uu___4)
        else ());
       (let chopsuf suf s =
          if FStarC_Util.ends_with s suf
          then
            let uu___3 =
              FStarC_String.substring s Prims.int_zero
                ((FStarC_String.length s) - (FStarC_String.length suf)) in
            FStar_Pervasives_Native.Some uu___3
          else FStar_Pervasives_Native.None in
        let op_Bar_Bar_Bar x y =
          match x with | FStar_Pervasives_Native.None -> y | uu___3 -> x in
        let checked_of f =
          let uu___3 = chopsuf ".checked" f in
          let uu___4 = chopsuf ".checked.lax" f in
          op_Bar_Bar_Bar uu___3 uu___4 in
        let filenames =
          FStarC_List.map
            (fun f ->
               if Prims.op_Negation (FStarC_Filepath.file_exists f)
               then f
               else
                 (let uu___4 = checked_of f in
                  match uu___4 with
                  | FStar_Pervasives_Native.Some f' ->
                      ((let uu___6 = FStarC_Debug.any () in
                        if uu___6
                        then
                          FStarC_Format.print1
                            "Rewriting argument file %s to its source file\n"
                            f
                        else ());
                       (let uu___6 =
                          let uu___7 = FStarC_Filepath.basename f' in
                          FStarC_Find.find_file uu___7 in
                        match uu___6 with
                        | FStar_Pervasives_Native.Some r -> r
                        | FStar_Pervasives_Native.None ->
                            let uu___7 =
                              failwith "Couldn't find source for file" in
                            Prims.strcat uu___7 (Prims.strcat f' "!\n")))
                  | FStar_Pervasives_Native.None -> f)) filenames0 in
        (let uu___4 = FStarC_Debug.high () in
         if uu___4
         then
           let uu___5 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
               filenames0 in
           let uu___6 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
               filenames in
           FStarC_Format.print2 "Rewrote\n%s\ninto\n%s\n\n" uu___5 uu___6
         else ());
        (let uu___5 = FStarC_Find.get_odir () in
         FStarC_Option.iter (FStarC_Util.mkdir false true) uu___5);
        (let uu___6 = FStarC_Find.get_cache_dir () in
         FStarC_Option.iter (FStarC_Util.mkdir false true) uu___6);
        (let check_no_filenames opt =
           if Prims.uu___is_Cons filenames
           then
             (FStarC_Format.print1_error
                "error: No filenames should be passed with option %s\n" opt;
              FStarC_Effect.exit Prims.int_one)
           else () in
         (let uu___7 = FStarC_Options.trace_error () in
          if uu___7 then set_error_trap () else ());
         if FStarC_Options.help ()
         then
           (FStarC_Options.display_usage ();
            FStarC_Effect.exit Prims.int_zero)
         else
           (match res with
            | FStarC_Getopt.Empty ->
                ((let uu___8 = FStarC_Effect.op_Bang FStarC_Options._version in
                  FStarC_Format.print1 "F* version %s\n" uu___8);
                 FStarC_Format.print1 "Usage: %s [options] file.fst\n"
                   FStarC_Util.argv0;
                 FStarC_Format.print_string
                   "Use `--help` to see all available options.\n";
                 FStarC_Effect.exit Prims.int_one)
            | FStarC_Getopt.Error (msg, opt) ->
                (FStarC_Format.print_error (Prims.strcat "error: " msg);
                 print_help_for opt;
                 FStarC_Effect.exit Prims.int_one)
            | FStarC_Getopt.Success when
                FStarC_Options.print_cache_version () ->
                ((let uu___8 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      FStarC_CheckedFiles.cache_version_number in
                  FStarC_Format.print1 "F* cache version number: %s\n" uu___8);
                 FStarC_Effect.exit Prims.int_zero)
            | FStarC_Getopt.Success when
                let uu___7 = FStarC_Options.dep () in
                uu___7 <> FStar_Pervasives_Native.None ->
                (load_native_tactics ();
                 (let uu___8 =
                    FStarC_Parser_Dep.collect filenames
                      FStarC_CheckedFiles.load_parsing_data_from_cache in
                  match uu___8 with
                  | (uu___9, deps) ->
                      (FStarC_Parser_Dep.print deps; report_errors [])))
            | FStarC_Getopt.Success when
                (FStarC_Options.print ()) ||
                  (FStarC_Options.print_in_place ())
                ->
                let printing_mode =
                  let uu___7 = FStarC_Options.print () in
                  if uu___7
                  then FStarC_Prettyprint.FromTempToStdout
                  else FStarC_Prettyprint.FromTempToFile in
                FStarC_Prettyprint.generate printing_mode filenames
            | FStarC_Getopt.Success when
                let uu___7 = FStarC_Options.read_checked_file () in
                FStar_Pervasives_Native.uu___is_Some uu___7 ->
                let path =
                  let uu___7 = FStarC_Options.read_checked_file () in
                  FStar_Pervasives_Native.__proj__Some__item__v uu___7 in
                let env =
                  let uu___7 = FStarC_Parser_Dep.empty_deps filenames in
                  FStarC_Universal.init_env uu___7 in
                let res1 = FStarC_CheckedFiles.load_tc_result path in
                (match res1 with
                 | FStar_Pervasives_Native.None ->
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           FStarC_Errors_Msg.text
                             "Could not read checked file:" in
                         FStar_Pprint.op_Hat_Slash_Hat uu___9
                           (FStar_Pprint.doc_of_string path) in
                       [uu___8] in
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_ModuleOrFileNotFound ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___7)
                 | FStar_Pervasives_Native.Some (deps, tcr) ->
                     ((let uu___8 =
                         FStarC_Class_Show.show
                           (FStarC_Class_Show.show_list
                              (FStarC_Class_Show.show_tuple2
                                 FStarC_Class_Show.showable_string
                                 FStarC_Class_Show.showable_string)) deps in
                       FStarC_Format.print1 "Deps: %s\n" uu___8);
                      (let uu___9 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_DsEnv.showable_mii
                           tcr.FStarC_CheckedFiles.mii in
                       FStarC_Format.print1 "Inclusion info: %s\n" uu___9);
                      (let uu___10 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_modul
                           tcr.FStarC_CheckedFiles.checked_module in
                       FStarC_Format.print1 "Checked module: %s\n" uu___10);
                      (let uu___11 =
                         FStarC_Class_Show.show
                           (FStarC_Class_Show.show_list
                              FStarC_SMTEncoding_Term.showable_decls_elt)
                           (FStar_Pervasives_Native.fst
                              tcr.FStarC_CheckedFiles.smt_decls) in
                       FStarC_Format.print1 "SMT decls: %s\n" uu___11);
                      (let uu___11 =
                         FStarC_Class_Show.show
                           (FStarC_Class_Show.show_list
                              FStarC_SMTEncoding_Env.showable_fvar_binding)
                           (FStar_Pervasives_Native.snd
                              tcr.FStarC_CheckedFiles.smt_decls) in
                       FStarC_Format.print1 "SMT fvars: %s\n" uu___11)))
            | FStarC_Getopt.Success when
                let uu___7 = FStarC_Options.read_krml_file () in
                FStar_Pervasives_Native.uu___is_Some uu___7 ->
                let path =
                  let uu___7 = FStarC_Options.read_krml_file () in
                  FStar_Pervasives_Native.__proj__Some__item__v uu___7 in
                let uu___7 = FStarC_Util.load_value_from_file path in
                (match uu___7 with
                 | FStar_Pervasives_Native.None ->
                     let uu___8 =
                       let uu___9 =
                         let uu___10 =
                           FStarC_Errors_Msg.text "Could not read krml file:" in
                         FStar_Pprint.op_Hat_Slash_Hat uu___10
                           (FStar_Pprint.doc_of_string path) in
                       [uu___9] in
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_ModuleOrFileNotFound ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___8)
                 | FStar_Pervasives_Native.Some (version, files) ->
                     ((let uu___9 =
                         FStarC_Class_Show.show
                           FStarC_Class_Show.showable_int version in
                       FStarC_Format.print1 "Karamel format version: %s\n"
                         uu___9);
                      FStarC_List.iter
                        (fun uu___9 ->
                           match uu___9 with
                           | (name, decls) ->
                               (FStarC_Format.print1 "%s:\n" name;
                                FStarC_List.iter
                                  (fun d ->
                                     let uu___11 =
                                       FStarC_Class_Show.show
                                         FStarC_Extraction_Krml.showable_decl
                                         d in
                                     FStarC_Format.print1 "%s\n\n" uu___11)
                                  decls)) files))
            | FStarC_Getopt.Success when FStarC_Options.list_plugins () ->
                (load_native_tactics ();
                 (let ps = FStarC_TypeChecker_Cfg.list_plugins () in
                  let ts = FStarC_Tactics_Interpreter.native_tactics_steps () in
                  (let uu___9 =
                     let uu___10 =
                       FStarC_List.map
                         (fun p ->
                            let uu___11 =
                              FStarC_Class_Show.show
                                FStarC_Ident.showable_lident
                                p.FStarC_TypeChecker_Primops_Base.name in
                            Prims.strcat "  " uu___11) ps in
                     FStarC_String.concat "\n" uu___10 in
                   FStarC_Format.print1 "Registered plugins:\n%s\n" uu___9);
                  (let uu___10 =
                     let uu___11 =
                       FStarC_List.map
                         (fun p ->
                            let uu___12 =
                              FStarC_Class_Show.show
                                FStarC_Ident.showable_lident
                                p.FStarC_TypeChecker_Primops_Base.name in
                            Prims.strcat "  " uu___12) ts in
                     FStarC_String.concat "\n" uu___11 in
                   FStarC_Format.print1 "Registered tactic plugins:\n%s\n"
                     uu___10)))
            | FStarC_Getopt.Success when
                let uu___7 = FStarC_Options.expand_include () in
                FStar_Pervasives_Native.uu___is_Some uu___7 ->
                let uu___7 = FStarC_Options.expand_include () in
                (match uu___7 with
                 | FStar_Pervasives_Native.Some d ->
                     let ds = FStarC_Find.expand_include_d d in
                     (FStarC_List.iter
                        (fun s ->
                           let uu___9 =
                             let uu___10 = FStarC_Filepath.canonicalize s in
                             Prims.strcat uu___10 "\n" in
                           FStarC_Format.print_string uu___9) ds;
                      FStarC_Effect.exit Prims.int_zero))
            | FStarC_Getopt.Success when FStarC_Options.locate () ->
                (check_no_filenames "--locate";
                 (let uu___9 = FStarC_Find.locate () in
                  FStarC_Format.print1 "%s\n" uu___9);
                 FStarC_Effect.exit Prims.int_zero)
            | FStarC_Getopt.Success when FStarC_Options.locate_lib () ->
                (check_no_filenames "--locate_lib";
                 (let uu___8 = FStarC_Find.locate_lib () in
                  match uu___8 with
                  | FStar_Pervasives_Native.None ->
                      (FStarC_Format.print_error
                         "No library found (is --no_default_includes set?)\n";
                       FStarC_Effect.exit Prims.int_one)
                  | FStar_Pervasives_Native.Some s ->
                      (FStarC_Format.print1 "%s\n" s;
                       FStarC_Effect.exit Prims.int_zero)))
            | FStarC_Getopt.Success when FStarC_Options.locate_ocaml () ->
                (check_no_filenames "--locate_ocaml";
                 (let uu___9 = FStarC_Find.locate_ocaml () in
                  FStarC_Format.print1 "%s\n" uu___9);
                 FStarC_Effect.exit Prims.int_zero)
            | FStarC_Getopt.Success when
                let uu___7 = FStarC_Options.locate_file () in
                FStar_Pervasives_Native.uu___is_Some uu___7 ->
                (check_no_filenames "--locate_file";
                 (let f =
                    let uu___8 = FStarC_Options.locate_file () in
                    FStar_Pervasives_Native.__proj__Some__item__v uu___8 in
                  let uu___8 = FStarC_Find.find_file f in
                  match uu___8 with
                  | FStar_Pervasives_Native.None ->
                      (FStarC_Format.print1_error
                         "File %s was not found in include path.\n" f;
                       FStarC_Effect.exit Prims.int_one)
                  | FStar_Pervasives_Native.Some fn ->
                      ((let uu___10 = FStarC_Filepath.normalize_file_path fn in
                        FStarC_Format.print1 "%s\n" uu___10);
                       FStarC_Effect.exit Prims.int_zero)))
            | FStarC_Getopt.Success when
                let uu___7 = FStarC_Options.locate_z3 () in
                FStar_Pervasives_Native.uu___is_Some uu___7 ->
                (check_no_filenames "--locate_z3";
                 (let v =
                    let uu___8 = FStarC_Options.locate_z3 () in
                    FStar_Pervasives_Native.__proj__Some__item__v uu___8 in
                  let uu___8 = FStarC_Find_Z3.locate_z3 v in
                  match uu___8 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu___10 =
                          let uu___11 =
                            let uu___12 =
                              let uu___13 =
                                FStarC_Format.fmt1
                                  "Z3 version '%s' was not found." v in
                              FStarC_Errors_Msg.text uu___13 in
                            [uu___12] in
                          let uu___12 =
                            FStarC_Find_Z3.z3_install_suggestion v in
                          FStarC_List.op_At uu___11 uu___12 in
                        FStarC_Errors.log_issue0
                          FStarC_Errors_Codes.Error_Z3InvocationError ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_list_doc)
                          (Obj.magic uu___10));
                       report_errors [];
                       FStarC_Effect.exit Prims.int_one)
                  | FStar_Pervasives_Native.Some fn ->
                      (FStarC_Format.print1 "%s\n" fn;
                       FStarC_Effect.exit Prims.int_zero)))
            | FStarC_Getopt.Success when FStarC_Options.dump_ast () ->
                (FStarC_List.iter
                   (fun fn ->
                      let uu___8 = FStarC_Parser_Driver.parse_file fn in
                      match uu___8 with
                      | (ast, uu___9) ->
                          let uu___10 =
                            let uu___11 =
                              FStarC_Class_PP.pp
                                FStarC_Parser_AST.pretty_modul ast in
                            FStar_Pprint.render uu___11 in
                          FStarC_Format.print2 "Parsed %s:\n%s\n\n" fn
                            uu___10) filenames;
                 FStarC_Effect.exit Prims.int_zero)
            | FStarC_Getopt.Success ->
                (FStarC_Effect.op_Colon_Equals fstar_files
                   (FStar_Pervasives_Native.Some filenames);
                 (let uu___9 = FStarC_Debug.any () in
                  if uu___9
                  then
                    ((let uu___11 =
                        FStarC_Effect.op_Bang FStarC_Options._version in
                      let uu___12 =
                        FStarC_Effect.op_Bang FStarC_Options._commit in
                      let uu___13 = FStarC_Platform_Base.kernel () in
                      FStarC_Format.print3 "- F* version %s -- %s (on %s)\n"
                        uu___11 uu___12 uu___13);
                     FStarC_Format.print1 "- Executable: %s\n"
                       FStarC_Util.exec_name;
                     (let uu___13 =
                        let uu___14 = FStarC_Find.lib_root () in
                        FStarC_Option.dflt "<none>" uu___14 in
                      FStarC_Format.print1 "- Library root: %s\n" uu___13);
                     (let uu___14 =
                        let uu___15 = FStarC_Find.full_include_path () in
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.show_list
                             FStarC_Class_Show.showable_string) uu___15 in
                      FStarC_Format.print1 "- Full include path: %s\n"
                        uu___14);
                     FStarC_Format.print_string "\n")
                  else ());
                 FStarC_Syntax_Unionfind.set_ro ();
                 load_native_tactics ();
                 (let uu___11 = FStarC_Options.interactive () in
                  if uu___11
                  then
                    (FStarC_Syntax_Unionfind.set_rw ();
                     (match filenames with
                      | [] ->
                          (FStarC_Errors.log_issue0
                             FStarC_Errors_Codes.Error_MissingFileName ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_string)
                             (Obj.magic
                                "--ide: Name of current file missing in command line invocation\n");
                           FStarC_Effect.exit Prims.int_one)
                      | uu___13::uu___14::uu___15 ->
                          (FStarC_Errors.log_issue0
                             FStarC_Errors_Codes.Error_TooManyFiles ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_string)
                             (Obj.magic
                                "--ide: Too many files in command line invocation\n");
                           FStarC_Effect.exit Prims.int_one)
                      | filename::[] ->
                          FStarC_Interactive_Ide.interactive_mode filename))
                  else
                    (if Prims.uu___is_Nil filenames
                     then
                       FStarC_Errors.raise_error0
                         FStarC_Errors_Codes.Error_MissingFileName ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic "No file provided")
                     else ();
                     (let uu___14 =
                        let uu___15 = FStarC_Parser_Dep.fly_deps_enabled () in
                        if uu___15
                        then
                          match filenames with
                          | fn::[] ->
                              let m =
                                FStarC_Parser_Dep.lowercase_module_name fn in
                              (FStarC_Options.add_verify_module m;
                               (let default_flydeps uu___17 =
                                  let deps =
                                    FStarC_Parser_Dep.empty_deps [fn] in
                                  let filenames1 =
                                    let uu___18 =
                                      FStarC_Parser_Dep.is_implementation fn in
                                    if uu___18
                                    then
                                      let uu___19 =
                                        FStarC_Parser_Dep.interface_of deps m in
                                      match uu___19 with
                                      | FStar_Pervasives_Native.None -> [fn]
                                      | FStar_Pervasives_Native.Some iface ->
                                          [iface; fn]
                                    else [fn] in
                                  (filenames1, deps, true) in
                                let uu___17 = FStarC_Options.force () in
                                if uu___17
                                then default_flydeps ()
                                else
                                  (let uu___19 =
                                     FStarC_CheckedFiles.scan_deps_and_check_cache_validity
                                       fn in
                                   match uu___19 with
                                   | FStar_Pervasives_Native.Some
                                       (files, deps) -> (files, deps, false)
                                   | FStar_Pervasives_Native.None ->
                                       default_flydeps ()
                                   | uu___20 ->
                                       FStarC_Errors.raise_error0
                                         FStarC_Errors_Codes.Error_TooManyFiles
                                         ()
                                         (Obj.magic
                                            FStarC_Errors_Msg.is_error_message_string)
                                         (Obj.magic
                                            "When using --ext fly_deps, only one file can be provided."))))
                        else
                          (let uu___17 =
                             FStarC_Dependencies.find_deps_if_needed
                               filenames
                               FStarC_CheckedFiles.load_parsing_data_from_cache in
                           match uu___17 with
                           | (files, deps) -> (files, deps, false)) in
                      match uu___14 with
                      | (filenames1, dep_graph, fly_deps) ->
                          let uu___15 =
                            FStarC_Universal.batch_mode_tc fly_deps
                              filenames1 dep_graph in
                          (match uu___15 with
                           | (tcrs, env, cleanup1) ->
                               ((let uu___17 = cleanup1 env in ());
                                (let module_names =
                                   FStarC_List.map
                                     (fun tcr ->
                                        FStarC_Universal.module_or_interface_name
                                          tcr.FStarC_CheckedFiles.checked_module)
                                     tcrs in
                                 report_errors module_names;
                                 finished_message module_names Prims.int_zero)))))))))))
let go (uu___ : unit) : unit=
  let args = FStarC_Util.get_cmd_args () in
  match args with
  | uu___1::"--ocamlenv"::[] ->
      let new_ocamlpath = FStarC_OCaml.new_ocamlpath () in
      ((let uu___3 = FStarC_OCaml.shellescape new_ocamlpath in
        FStarC_Format.print1 "OCAMLPATH='%s'; export OCAMLPATH;\n" uu___3);
       FStarC_Effect.exit Prims.int_zero)
  | uu___1::"--ocamlenv"::cmd::args1 ->
      FStarC_OCaml.exec_in_ocamlenv cmd args1
  | uu___1::"--ocamlc"::rest -> FStarC_OCaml.exec_ocamlc rest
  | uu___1::"--ocamlopt"::rest -> FStarC_OCaml.exec_ocamlopt rest
  | uu___1::"--ocamlopt_plugin"::rest ->
      FStarC_OCaml.exec_ocamlopt_plugin rest
  | uu___1 -> go_normal ()
let handle_error (e : Prims.exn) : unit=
  (let uu___1 = FStarC_Errors.handleable e in
   if uu___1
   then FStarC_Errors.err_exn e
   else
     ((let uu___4 = FStarC_Util.message_of_exn e in
       FStarC_Format.print1_error "Unexpected error: %s\n" uu___4);
      (let uu___4 = FStarC_Options.trace_error () in
       if uu___4
       then
         let uu___5 = FStarC_Util.trace_of_exn e in
         FStarC_Format.print1_error "Trace:\n%s\n" uu___5
       else
         FStarC_Format.print_error
           "Please file a bug report, ideally with a minimized version of the source program that triggered the error.\n")));
  report_errors []
let main (uu___ : unit) : 'uuuuu=
  try
    (fun uu___1 ->
       match () with
       | () ->
           let uu___2 = FStarC_Timing.record_ms go in
           (match uu___2 with
            | (uu___3, time) ->
                ((let uu___5 = FStarC_Options.query_stats () in
                  if uu___5
                  then
                    let uu___6 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_int
                        time in
                    let uu___7 =
                      let uu___8 = FStarC_Getopt.cmdline () in
                      FStarC_String.concat " " uu___8 in
                    FStarC_Format.print2_error "TOTAL TIME %s ms: %s\n"
                      uu___6 uu___7
                  else ());
                 print_stats ();
                 cleanup ();
                 FStarC_Effect.exit Prims.int_zero))) ()
  with
  | uu___1 ->
      (handle_error uu___1; print_stats (); FStarC_Effect.exit Prims.int_one)
