open Prims
let (uu___0 : unit) = FStarC_Version.dummy ()
let (process_args :
  unit -> (FStarC_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu___ -> FStarC_Options.parse_cmd_line ()
let (cleanup : unit -> unit) = fun uu___ -> FStarC_Compiler_Util.kill_all ()
let (finished_message :
  (Prims.bool * FStarC_Ident.lident) Prims.list -> Prims.int -> unit) =
  fun fmods ->
    fun errs ->
      let print_to =
        if errs > Prims.int_zero
        then FStarC_Compiler_Util.print_error
        else FStarC_Compiler_Util.print_string in
      let uu___ =
        let uu___1 = FStarC_Options.silent () in Prims.op_Negation uu___1 in
      if uu___
      then
        (FStarC_Compiler_List.iter
           (fun uu___2 ->
              match uu___2 with
              | (iface, name) ->
                  let tag =
                    if iface then "i'face (or impl+i'face)" else "module" in
                  let uu___3 =
                    let uu___4 = FStarC_Ident.string_of_lid name in
                    FStarC_Options.should_print_message uu___4 in
                  if uu___3
                  then
                    let uu___4 =
                      let uu___5 = FStarC_Ident.string_of_lid name in
                      FStarC_Compiler_Util.format2 "Verified %s: %s\n" tag
                        uu___5 in
                    print_to uu___4
                  else ()) fmods;
         if errs > Prims.int_zero
         then
           (if errs = Prims.int_one
            then
              FStarC_Compiler_Util.print_error
                "1 error was reported (see above)\n"
            else
              (let uu___3 = FStarC_Compiler_Util.string_of_int errs in
               FStarC_Compiler_Util.print1_error
                 "%s errors were reported (see above)\n" uu___3))
         else
           (let uu___3 =
              FStarC_Compiler_Util.colorize_bold
                "All verification conditions discharged successfully" in
            FStarC_Compiler_Util.print1 "%s\n" uu___3))
      else ()
let (report_errors : (Prims.bool * FStarC_Ident.lident) Prims.list -> unit) =
  fun fmods ->
    (let uu___1 = FStarC_Errors.report_all () in ());
    (let nerrs = FStarC_Errors.get_err_count () in
     if nerrs > Prims.int_zero
     then
       (finished_message fmods nerrs;
        FStarC_Compiler_Effect.exit Prims.int_one)
     else ())
let (load_native_tactics : unit -> unit) =
  fun uu___ ->
    let modules_to_load =
      let uu___1 = FStarC_Options.load () in
      FStarC_Compiler_List.map FStarC_Ident.lid_of_str uu___1 in
    let cmxs_to_load =
      let uu___1 = FStarC_Options.load_cmxs () in
      FStarC_Compiler_List.map FStarC_Ident.lid_of_str uu___1 in
    let ml_module_name m = FStarC_Extraction_ML_Util.ml_module_name_of_lid m in
    let ml_file m =
      let uu___1 = ml_module_name m in Prims.strcat uu___1 ".ml" in
    let cmxs_file m =
      let cmxs = let uu___1 = ml_module_name m in Prims.strcat uu___1 ".cmxs" in
      let uu___1 = FStarC_Find.find_file_odir cmxs in
      match uu___1 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None ->
          if FStarC_Compiler_List.contains m cmxs_to_load
          then
            let uu___2 =
              FStarC_Compiler_Util.format1 "Could not find %s to load" cmxs in
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
                   let uu___5 = ml_file m in
                   FStarC_Compiler_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu___5 in
                 FStarC_Errors.raise_error0
                   FStarC_Errors_Codes.Fatal_FailToCompileNativeTactic ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___4)
             | FStar_Pervasives_Native.Some ml ->
                 let dir = FStarC_Compiler_Util.dirname ml in
                 ((let uu___5 = let uu___6 = ml_module_name m in [uu___6] in
                   FStarC_Compiler_Plugins.compile_modules dir uu___5);
                  (let uu___5 = FStarC_Find.find_file_odir cmxs in
                   match uu___5 with
                   | FStar_Pervasives_Native.None ->
                       let uu___6 =
                         FStarC_Compiler_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs in
                       FStarC_Errors.raise_error0
                         FStarC_Errors_Codes.Fatal_FailToCompileNativeTactic
                         ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic uu___6)
                   | FStar_Pervasives_Native.Some f -> f))) in
    let cmxs_files =
      FStarC_Compiler_List.map cmxs_file
        (FStarC_Compiler_List.op_At modules_to_load cmxs_to_load) in
    (let uu___2 = FStarC_Compiler_Debug.any () in
     if uu___2
     then
       FStarC_Compiler_Util.print1 "Will try to load cmxs files: [%s]\n"
         (FStarC_Compiler_String.concat ", " cmxs_files)
     else ());
    FStarC_Compiler_Plugins.load_plugins cmxs_files;
    (let uu___4 = FStarC_Options.use_native_tactics () in
     FStarC_Compiler_Util.iter_opt uu___4
       FStarC_Compiler_Plugins.load_plugins_dir)
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (go_ocamlenv : Prims.string Prims.list -> unit) =
  fun rest_args ->
    if FStarC_Platform.system = FStarC_Platform.Windows
    then
      (let uu___1 =
         let uu___2 =
           FStarC_Errors_Msg.text
             "--ocamlenv is not supported on Windows (yet?)" in
         [uu___2] in
       FStarC_Errors.raise_error0
         FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic uu___1))
    else ();
    (let shellescape s =
       let uu___1 =
         let uu___2 = FStarC_Compiler_String.list_of_string s in
         FStarC_Compiler_List.map
           (fun uu___3 ->
              match uu___3 with
              | 39 -> "'\"'\"'"
              | c -> FStarC_Compiler_String.make Prims.int_one c) uu___2 in
       FStarC_Compiler_String.concat "" uu___1 in
     let ocamldir = FStarC_Find.locate_ocaml () in
     let old_ocamlpath =
       let uu___1 =
         FStarC_Compiler_Util.expand_environment_variable "OCAMLPATH" in
       FStarC_Compiler_Util.dflt "" uu___1 in
     let new_ocamlpath =
       Prims.strcat ocamldir (Prims.strcat ":" old_ocamlpath) in
     match rest_args with
     | [] ->
         ((let uu___2 = shellescape new_ocamlpath in
           FStarC_Compiler_Util.print1 "OCAMLPATH='%s'; export OCAMLPATH;\n"
             uu___2);
          FStarC_Compiler_Effect.exit Prims.int_zero)
     | cmd::args ->
         (FStarC_Compiler_Util.putenv "OCAMLPATH" new_ocamlpath;
          FStarC_Compiler_Util.execvp cmd (cmd :: args)))
let (set_error_trap : unit -> unit) =
  fun uu___ ->
    let h = FStarC_Compiler_Util.get_sigint_handler () in
    let h' s =
      FStarC_Compiler_Debug.enable ();
      FStarC_Options.set_option "error_contexts" (FStarC_Options.Bool true);
      (let uu___4 =
         let uu___5 = FStarC_Errors_Msg.text "GOT SIGINT! Exiting" in
         [uu___5] in
       FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
         FStarC_Compiler_Range_Type.dummyRange ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic uu___4));
      FStarC_Compiler_Effect.exit Prims.int_one in
    let uu___1 = FStarC_Compiler_Util.sigint_handler_f h' in
    FStarC_Compiler_Util.set_sigint_handler uu___1
let (go_normal : unit -> unit) =
  fun uu___ ->
    let uu___1 = process_args () in
    match uu___1 with
    | (res, filenames) ->
        ((let uu___3 = FStarC_Options.trace_error () in
          if uu___3 then set_error_trap () else ());
         (match res with
          | FStarC_Getopt.Empty ->
              (FStarC_Options.display_usage ();
               FStarC_Compiler_Effect.exit Prims.int_one)
          | FStarC_Getopt.Help ->
              (FStarC_Options.display_usage ();
               FStarC_Compiler_Effect.exit Prims.int_zero)
          | FStarC_Getopt.Error msg ->
              (FStarC_Compiler_Util.print_error msg;
               FStarC_Compiler_Effect.exit Prims.int_one)
          | FStarC_Getopt.Success when FStarC_Options.print_cache_version ()
              ->
              ((let uu___4 =
                  FStarC_Compiler_Util.string_of_int
                    FStarC_CheckedFiles.cache_version_number in
                FStarC_Compiler_Util.print1 "F* cache version number: %s\n"
                  uu___4);
               FStarC_Compiler_Effect.exit Prims.int_zero)
          | FStarC_Getopt.Success when
              let uu___3 = FStarC_Options.dep () in
              uu___3 <> FStar_Pervasives_Native.None ->
              let uu___3 =
                FStarC_Parser_Dep.collect filenames
                  FStarC_CheckedFiles.load_parsing_data_from_cache in
              (match uu___3 with
               | (uu___4, deps) ->
                   (FStarC_Parser_Dep.print deps; report_errors []))
          | FStarC_Getopt.Success when
              (FStarC_Options.print ()) || (FStarC_Options.print_in_place ())
              ->
              (if
                 Prims.op_Negation
                   FStarC_Platform.is_fstar_compiler_using_ocaml
               then
                 failwith
                   "You seem to be using the F#-generated version of the compiler ; \\o\n                   reindenting is not known to work yet with this version"
               else ();
               (let printing_mode =
                  let uu___4 = FStarC_Options.print () in
                  if uu___4
                  then FStarC_Prettyprint.FromTempToStdout
                  else FStarC_Prettyprint.FromTempToFile in
                FStarC_Prettyprint.generate printing_mode filenames))
          | FStarC_Getopt.Success when
              let uu___3 = FStarC_Options.read_checked_file () in
              FStar_Pervasives_Native.uu___is_Some uu___3 ->
              let path =
                let uu___3 = FStarC_Options.read_checked_file () in
                FStar_Pervasives_Native.__proj__Some__item__v uu___3 in
              let env =
                FStarC_Universal.init_env FStarC_Parser_Dep.empty_deps in
              let res1 = FStarC_CheckedFiles.load_tc_result path in
              (match res1 with
               | FStar_Pervasives_Native.None ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Errors_Msg.text
                           "Could not read checked file:" in
                       let uu___6 = FStarC_Pprint.doc_of_string path in
                       FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                     [uu___4] in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_ModuleOrFileNotFound ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___3)
               | FStar_Pervasives_Native.Some (uu___3, tcr) ->
                   let uu___4 =
                     FStarC_Class_Show.show
                       FStarC_Syntax_Print.showable_modul
                       tcr.FStarC_CheckedFiles.checked_module in
                   FStarC_Compiler_Util.print1 "%s\n" uu___4)
          | FStarC_Getopt.Success when
              let uu___3 = FStarC_Options.read_krml_file () in
              FStar_Pervasives_Native.uu___is_Some uu___3 ->
              let path =
                let uu___3 = FStarC_Options.read_krml_file () in
                FStar_Pervasives_Native.__proj__Some__item__v uu___3 in
              let uu___3 = FStarC_Compiler_Util.load_value_from_file path in
              (match uu___3 with
               | FStar_Pervasives_Native.None ->
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStarC_Errors_Msg.text "Could not read krml file:" in
                       let uu___7 = FStarC_Pprint.doc_of_string path in
                       FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                     [uu___5] in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_ModuleOrFileNotFound ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___4)
               | FStar_Pervasives_Native.Some (version, files) ->
                   ((let uu___5 =
                       FStarC_Class_Show.show FStarC_Class_Show.showable_int
                         version in
                     FStarC_Compiler_Util.print1
                       "Karamel format version: %s\n" uu___5);
                    FStarC_Compiler_List.iter
                      (fun uu___5 ->
                         match uu___5 with
                         | (name, decls) ->
                             (FStarC_Compiler_Util.print1 "%s:\n" name;
                              FStarC_Compiler_List.iter
                                (fun d ->
                                   let uu___7 =
                                     FStarC_Class_Show.show
                                       FStarC_Extraction_Krml.showable_decl d in
                                   FStarC_Compiler_Util.print1 "  %s\n"
                                     uu___7) decls)) files))
          | FStarC_Getopt.Success when FStarC_Options.list_plugins () ->
              let ps = FStarC_TypeChecker_Cfg.list_plugins () in
              let ts = FStarC_Tactics_Interpreter.native_tactics_steps () in
              ((let uu___4 =
                  let uu___5 =
                    FStarC_Compiler_List.map
                      (fun p ->
                         let uu___6 =
                           FStarC_Class_Show.show
                             FStarC_Ident.showable_lident
                             p.FStarC_TypeChecker_Primops_Base.name in
                         Prims.strcat "  " uu___6) ps in
                  FStarC_Compiler_String.concat "\n" uu___5 in
                FStarC_Compiler_Util.print1 "Registered plugins:\n%s\n"
                  uu___4);
               (let uu___5 =
                  let uu___6 =
                    FStarC_Compiler_List.map
                      (fun p ->
                         let uu___7 =
                           FStarC_Class_Show.show
                             FStarC_Ident.showable_lident
                             p.FStarC_TypeChecker_Primops_Base.name in
                         Prims.strcat "  " uu___7) ts in
                  FStarC_Compiler_String.concat "\n" uu___6 in
                FStarC_Compiler_Util.print1
                  "Registered tactic plugins:\n%s\n" uu___5))
          | FStarC_Getopt.Success when FStarC_Options.locate () ->
              ((let uu___4 = FStarC_Find.locate () in
                FStarC_Compiler_Util.print1 "%s\n" uu___4);
               FStarC_Compiler_Effect.exit Prims.int_zero)
          | FStarC_Getopt.Success when FStarC_Options.locate_lib () ->
              let uu___3 = FStarC_Find.locate_lib () in
              (match uu___3 with
               | FStar_Pervasives_Native.None ->
                   (FStarC_Compiler_Util.print_error
                      "No library found (is --no_default_includes set?)\n";
                    FStarC_Compiler_Effect.exit Prims.int_one)
               | FStar_Pervasives_Native.Some s ->
                   (FStarC_Compiler_Util.print1 "%s\n" s;
                    FStarC_Compiler_Effect.exit Prims.int_zero))
          | FStarC_Getopt.Success when FStarC_Options.locate_ocaml () ->
              ((let uu___4 = FStarC_Find.locate_ocaml () in
                FStarC_Compiler_Util.print1 "%s\n" uu___4);
               FStarC_Compiler_Effect.exit Prims.int_zero)
          | FStarC_Getopt.Success ->
              (FStarC_Compiler_Effect.op_Colon_Equals fstar_files
                 (FStar_Pervasives_Native.Some filenames);
               (let uu___5 = FStarC_Compiler_Debug.any () in
                if uu___5
                then
                  (FStarC_Compiler_Util.print1 "- F* executable: %s\n"
                     FStarC_Compiler_Util.exec_name;
                   (let uu___8 =
                      let uu___9 = FStarC_Find.lib_root () in
                      FStarC_Compiler_Util.dflt "<none>" uu___9 in
                    FStarC_Compiler_Util.print1 "- Library root: %s\n" uu___8);
                   (let uu___9 =
                      let uu___10 = FStarC_Find.include_path () in
                      FStarC_Class_Show.show
                        (FStarC_Class_Show.show_list
                           FStarC_Class_Show.showable_string) uu___10 in
                    FStarC_Compiler_Util.print1 "- Full include path: %s\n"
                      uu___9);
                   FStarC_Compiler_Util.print_string "\n")
                else ());
               FStarC_Syntax_Unionfind.set_ro ();
               load_native_tactics ();
               (let uu___7 = FStarC_Options.lsp_server () in
                if uu___7
                then FStarC_Interactive_Lsp.start_server ()
                else
                  (let uu___9 = FStarC_Options.interactive () in
                   if uu___9
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
                            FStarC_Compiler_Effect.exit Prims.int_one)
                       | uu___11::uu___12::uu___13 ->
                           (FStarC_Errors.log_issue0
                              FStarC_Errors_Codes.Error_TooManyFiles ()
                              (Obj.magic
                                 FStarC_Errors_Msg.is_error_message_string)
                              (Obj.magic
                                 "--ide: Too many files in command line invocation\n");
                            FStarC_Compiler_Effect.exit Prims.int_one)
                       | filename::[] ->
                           let uu___11 = FStarC_Options.legacy_interactive () in
                           if uu___11
                           then
                             FStarC_Interactive_Legacy.interactive_mode
                               filename
                           else
                             FStarC_Interactive_Ide.interactive_mode filename))
                   else
                     if
                       (FStarC_Compiler_List.length filenames) >=
                         Prims.int_one
                     then
                       (if Prims.uu___is_Nil filenames
                        then
                          FStarC_Errors.raise_error0
                            FStarC_Errors_Codes.Error_MissingFileName ()
                            (Obj.magic
                               FStarC_Errors_Msg.is_error_message_string)
                            (Obj.magic "No file provided")
                        else ();
                        (let uu___12 =
                           FStarC_Dependencies.find_deps_if_needed filenames
                             FStarC_CheckedFiles.load_parsing_data_from_cache in
                         match uu___12 with
                         | (filenames1, dep_graph) ->
                             let uu___13 =
                               FStarC_Universal.batch_mode_tc filenames1
                                 dep_graph in
                             (match uu___13 with
                              | (tcrs, env, cleanup1) ->
                                  ((let uu___15 = cleanup1 env in ());
                                   (let module_names =
                                      FStarC_Compiler_List.map
                                        (fun tcr ->
                                           FStarC_Universal.module_or_interface_name
                                             tcr.FStarC_CheckedFiles.checked_module)
                                        tcrs in
                                    report_errors module_names;
                                    finished_message module_names
                                      Prims.int_zero)))))
                     else ())))))
let (go : unit -> unit) =
  fun uu___ ->
    let args = FStarC_Compiler_Util.get_cmd_args () in
    match args with
    | uu___1::"--ocamlenv"::rest -> go_ocamlenv rest
    | uu___1 -> go_normal ()
let (lazy_chooser :
  FStarC_Syntax_Syntax.lazy_kind ->
    FStarC_Syntax_Syntax.lazyinfo -> FStarC_Syntax_Syntax.term)
  =
  fun k ->
    fun i ->
      match k with
      | FStarC_Syntax_Syntax.BadLazy ->
          failwith "lazy chooser: got a BadLazy"
      | FStarC_Syntax_Syntax.Lazy_bv ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_bv i
      | FStarC_Syntax_Syntax.Lazy_namedv ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_namedv i
      | FStarC_Syntax_Syntax.Lazy_binder ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_binder i
      | FStarC_Syntax_Syntax.Lazy_letbinding ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_letbinding i
      | FStarC_Syntax_Syntax.Lazy_optionstate ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_optionstate i
      | FStarC_Syntax_Syntax.Lazy_fvar ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_fvar i
      | FStarC_Syntax_Syntax.Lazy_comp ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_comp i
      | FStarC_Syntax_Syntax.Lazy_env ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_env i
      | FStarC_Syntax_Syntax.Lazy_sigelt ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_sigelt i
      | FStarC_Syntax_Syntax.Lazy_universe ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_universe i
      | FStarC_Syntax_Syntax.Lazy_proofstate ->
          FStarC_Tactics_Embedding.unfold_lazy_proofstate i
      | FStarC_Syntax_Syntax.Lazy_goal ->
          FStarC_Tactics_Embedding.unfold_lazy_goal i
      | FStarC_Syntax_Syntax.Lazy_doc ->
          FStarC_Reflection_V2_Embeddings.unfold_lazy_doc i
      | FStarC_Syntax_Syntax.Lazy_uvar ->
          FStarC_Syntax_Util.exp_string "((uvar))"
      | FStarC_Syntax_Syntax.Lazy_universe_uvar ->
          FStarC_Syntax_Util.exp_string "((universe_uvar))"
      | FStarC_Syntax_Syntax.Lazy_issue ->
          FStarC_Syntax_Util.exp_string "((issue))"
      | FStarC_Syntax_Syntax.Lazy_ident ->
          FStarC_Syntax_Util.exp_string "((ident))"
      | FStarC_Syntax_Syntax.Lazy_tref ->
          FStarC_Syntax_Util.exp_string "((tref))"
      | FStarC_Syntax_Syntax.Lazy_embedding (uu___, t) ->
          FStarC_Thunk.force t
      | FStarC_Syntax_Syntax.Lazy_extension s ->
          let uu___ = FStarC_Compiler_Util.format1 "((extension %s))" s in
          FStarC_Syntax_Util.exp_string uu___
let (setup_hooks : unit -> unit) =
  fun uu___ ->
    FStarC_Compiler_Effect.op_Colon_Equals
      FStarC_Syntax_DsEnv.ugly_sigelt_to_string_hook
      (FStarC_Class_Show.show FStarC_Syntax_Print.showable_sigelt);
    FStarC_Errors.set_parse_warn_error FStarC_Parser_ParseIt.parse_warn_error;
    FStarC_Compiler_Effect.op_Colon_Equals FStarC_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStarC_Compiler_Effect.op_Colon_Equals FStarC_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some
         (FStarC_Class_Show.show FStarC_Syntax_Print.showable_term));
    FStarC_Compiler_Effect.op_Colon_Equals FStarC_Syntax_Util.ttd_f
      (FStar_Pervasives_Native.Some
         (FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term));
    FStarC_Compiler_Effect.op_Colon_Equals
      FStarC_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStarC_Reflection_V2_Embeddings.e_binder);
    FStarC_Compiler_List.iter
      FStarC_Tactics_Interpreter.register_tactic_primitive_step
      FStarC_Tactics_V1_Primops.ops;
    FStarC_Compiler_List.iter
      FStarC_Tactics_Interpreter.register_tactic_primitive_step
      FStarC_Tactics_V2_Primops.ops
let (handle_error : Prims.exn -> unit) =
  fun e ->
    (let uu___1 = FStarC_Errors.handleable e in
     if uu___1 then FStarC_Errors.err_exn e else ());
    (let uu___2 = FStarC_Options.trace_error () in
     if uu___2
     then
       let uu___3 = FStarC_Compiler_Util.message_of_exn e in
       let uu___4 = FStarC_Compiler_Util.trace_of_exn e in
       FStarC_Compiler_Util.print2_error "Unexpected error\n%s\n%s\n" uu___3
         uu___4
     else
       (let uu___4 =
          let uu___5 = FStarC_Errors.handleable e in Prims.op_Negation uu___5 in
        if uu___4
        then
          let uu___5 = FStarC_Compiler_Util.message_of_exn e in
          FStarC_Compiler_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu___5
        else ()));
    cleanup ();
    report_errors []
let main : 'uuuuu . unit -> 'uuuuu =
  fun uu___ ->
    try
      (fun uu___1 ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu___3 = FStarC_Compiler_Util.record_time go in
               match uu___3 with
               | (uu___4, time) ->
                   ((let uu___6 = FStarC_Options.query_stats () in
                     if uu___6
                     then
                       let uu___7 = FStarC_Compiler_Util.string_of_int time in
                       let uu___8 =
                         let uu___9 = FStarC_Getopt.cmdline () in
                         FStarC_Compiler_String.concat " " uu___9 in
                       FStarC_Compiler_Util.print2_error
                         "TOTAL TIME %s ms: %s\n" uu___7 uu___8
                     else ());
                    cleanup ();
                    FStarC_Compiler_Effect.exit Prims.int_zero)))) ()
    with
    | uu___1 ->
        (handle_error uu___1; FStarC_Compiler_Effect.exit Prims.int_one)