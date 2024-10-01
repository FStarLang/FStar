open Prims
let (uu___0 : unit) = FStar_Version.dummy ()
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu___ -> FStar_Options.parse_cmd_line ()
let (cleanup : unit -> unit) = fun uu___ -> FStar_Compiler_Util.kill_all ()
let (finished_message :
  (Prims.bool * FStar_Ident.lident) Prims.list -> Prims.int -> unit) =
  fun fmods ->
    fun errs ->
      let print_to =
        if errs > Prims.int_zero
        then FStar_Compiler_Util.print_error
        else FStar_Compiler_Util.print_string in
      let uu___ =
        let uu___1 = FStar_Options.silent () in Prims.op_Negation uu___1 in
      if uu___
      then
        (FStar_Compiler_List.iter
           (fun uu___2 ->
              match uu___2 with
              | (iface, name) ->
                  let tag =
                    if iface then "i'face (or impl+i'face)" else "module" in
                  let uu___3 =
                    let uu___4 = FStar_Ident.string_of_lid name in
                    FStar_Options.should_print_message uu___4 in
                  if uu___3
                  then
                    let uu___4 =
                      let uu___5 = FStar_Ident.string_of_lid name in
                      FStar_Compiler_Util.format2 "Verified %s: %s\n" tag
                        uu___5 in
                    print_to uu___4
                  else ()) fmods;
         if errs > Prims.int_zero
         then
           (if errs = Prims.int_one
            then
              FStar_Compiler_Util.print_error
                "1 error was reported (see above)\n"
            else
              (let uu___3 = FStar_Compiler_Util.string_of_int errs in
               FStar_Compiler_Util.print1_error
                 "%s errors were reported (see above)\n" uu___3))
         else
           (let uu___3 =
              FStar_Compiler_Util.colorize_bold
                "All verification conditions discharged successfully" in
            FStar_Compiler_Util.print1 "%s\n" uu___3))
      else ()
let (report_errors : (Prims.bool * FStar_Ident.lident) Prims.list -> unit) =
  fun fmods ->
    (let uu___1 = FStar_Errors.report_all () in ());
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > Prims.int_zero
     then
       (finished_message fmods nerrs;
        FStar_Compiler_Effect.exit Prims.int_one)
     else ())
let (load_native_tactics : unit -> unit) =
  fun uu___ ->
    let modules_to_load =
      let uu___1 = FStar_Options.load () in
      FStar_Compiler_List.map FStar_Ident.lid_of_str uu___1 in
    let cmxs_to_load =
      let uu___1 = FStar_Options.load_cmxs () in
      FStar_Compiler_List.map FStar_Ident.lid_of_str uu___1 in
    let ml_module_name m = FStar_Extraction_ML_Util.ml_module_name_of_lid m in
    let ml_file m =
      let uu___1 = ml_module_name m in Prims.strcat uu___1 ".ml" in
    let cmxs_file m =
      let cmxs = let uu___1 = ml_module_name m in Prims.strcat uu___1 ".cmxs" in
      let uu___1 = FStar_Options.find_file cmxs in
      match uu___1 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None ->
          if FStar_Compiler_List.contains m cmxs_to_load
          then
            let uu___2 =
              FStar_Compiler_Util.format1 "Could not find %s to load" cmxs in
            FStar_Errors.raise_error0
              FStar_Errors_Codes.Fatal_FailToCompileNativeTactic ()
              (Obj.magic FStar_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2)
          else
            (let uu___3 =
               let uu___4 = ml_file m in FStar_Options.find_file uu___4 in
             match uu___3 with
             | FStar_Pervasives_Native.None ->
                 let uu___4 =
                   let uu___5 = ml_file m in
                   FStar_Compiler_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu___5 in
                 FStar_Errors.raise_error0
                   FStar_Errors_Codes.Fatal_FailToCompileNativeTactic ()
                   (Obj.magic FStar_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___4)
             | FStar_Pervasives_Native.Some ml ->
                 let dir = FStar_Compiler_Util.dirname ml in
                 ((let uu___5 = let uu___6 = ml_module_name m in [uu___6] in
                   FStar_Tactics_Load.compile_modules dir uu___5);
                  (let uu___5 = FStar_Options.find_file cmxs in
                   match uu___5 with
                   | FStar_Pervasives_Native.None ->
                       let uu___6 =
                         FStar_Compiler_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs in
                       FStar_Errors.raise_error0
                         FStar_Errors_Codes.Fatal_FailToCompileNativeTactic
                         ()
                         (Obj.magic FStar_Errors_Msg.is_error_message_string)
                         (Obj.magic uu___6)
                   | FStar_Pervasives_Native.Some f -> f))) in
    let cmxs_files =
      FStar_Compiler_List.map cmxs_file
        (FStar_Compiler_List.op_At modules_to_load cmxs_to_load) in
    (let uu___2 = FStar_Compiler_Debug.any () in
     if uu___2
     then
       FStar_Compiler_Util.print1 "Will try to load cmxs files: [%s]\n"
         (FStar_Compiler_String.concat ", " cmxs_files)
     else ());
    FStar_Tactics_Load.load_tactics cmxs_files;
    (let uu___4 = FStar_Options.use_native_tactics () in
     FStar_Compiler_Util.iter_opt uu___4 FStar_Tactics_Load.load_tactics_dir)
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let go : 'uuuuu . 'uuuuu -> unit =
  fun uu___ ->
    let uu___1 = process_args () in
    match uu___1 with
    | (res, filenames) ->
        ((let uu___3 = FStar_Options.trace_error () in
          if uu___3
          then
            let h = FStar_Compiler_Util.get_sigint_handler () in
            let h' s =
              FStar_Compiler_Debug.enable ();
              FStar_Options.set_option "error_contexts"
                (FStar_Options.Bool true);
              (let uu___7 =
                 let uu___8 = FStar_Errors_Msg.text "GOT SIGINT! Exiting" in
                 [uu___8] in
               FStar_Errors.diag FStar_Class_HasRange.hasRange_range
                 FStar_Compiler_Range_Type.dummyRange ()
                 (Obj.magic FStar_Errors_Msg.is_error_message_list_doc)
                 (Obj.magic uu___7));
              FStar_Compiler_Effect.exit Prims.int_one in
            let uu___4 = FStar_Compiler_Util.sigint_handler_f h' in
            FStar_Compiler_Util.set_sigint_handler uu___4
          else ());
         (match res with
          | FStar_Getopt.Empty ->
              (FStar_Options.display_usage ();
               FStar_Compiler_Effect.exit Prims.int_one)
          | FStar_Getopt.Help ->
              (FStar_Options.display_usage ();
               FStar_Compiler_Effect.exit Prims.int_zero)
          | FStar_Getopt.Error msg ->
              (FStar_Compiler_Util.print_error msg;
               FStar_Compiler_Effect.exit Prims.int_one)
          | uu___3 when FStar_Options.print_cache_version () ->
              ((let uu___5 =
                  FStar_Compiler_Util.string_of_int
                    FStar_CheckedFiles.cache_version_number in
                FStar_Compiler_Util.print1 "F* cache version number: %s\n"
                  uu___5);
               FStar_Compiler_Effect.exit Prims.int_zero)
          | FStar_Getopt.Success ->
              (FStar_Compiler_Effect.op_Colon_Equals fstar_files
                 (FStar_Pervasives_Native.Some filenames);
               (let uu___5 = FStar_Compiler_Debug.any () in
                if uu___5
                then
                  let uu___6 =
                    let uu___7 = FStar_Options.include_path () in
                    FStar_Class_Show.show
                      (FStar_Class_Show.show_list
                         (FStar_Class_Show.printableshow
                            FStar_Class_Printable.printable_string)) uu___7 in
                  FStar_Compiler_Util.print1 "Full include path = %s\n"
                    uu___6
                else ());
               load_native_tactics ();
               FStar_Syntax_Unionfind.set_ro ();
               (let uu___7 =
                  let uu___8 = FStar_Options.dep () in
                  uu___8 <> FStar_Pervasives_Native.None in
                if uu___7
                then
                  let uu___8 =
                    FStar_Parser_Dep.collect filenames
                      FStar_CheckedFiles.load_parsing_data_from_cache in
                  match uu___8 with
                  | (uu___9, deps) ->
                      (FStar_Parser_Dep.print deps; report_errors [])
                else
                  (let uu___9 =
                     (FStar_Options.print ()) ||
                       (FStar_Options.print_in_place ()) in
                   if uu___9
                   then
                     (if FStar_Platform.is_fstar_compiler_using_ocaml
                      then
                        let printing_mode =
                          let uu___10 = FStar_Options.print () in
                          if uu___10
                          then FStar_Prettyprint.FromTempToStdout
                          else FStar_Prettyprint.FromTempToFile in
                        FStar_Prettyprint.generate printing_mode filenames
                      else
                        FStar_Compiler_Effect.failwith
                          "You seem to be using the F#-generated version ofthe compiler ; \\o\n                         reindenting is not known to work yet with this version")
                   else
                     (let uu___11 =
                        let uu___12 = FStar_Options.read_checked_file () in
                        FStar_Pervasives_Native.uu___is_Some uu___12 in
                      if uu___11
                      then
                        let path =
                          let uu___12 = FStar_Options.read_checked_file () in
                          FStar_Pervasives_Native.__proj__Some__item__v
                            uu___12 in
                        let env =
                          FStar_Universal.init_env
                            FStar_Parser_Dep.empty_deps in
                        let res1 = FStar_CheckedFiles.load_tc_result path in
                        match res1 with
                        | FStar_Pervasives_Native.None ->
                            let uu___12 =
                              let uu___13 =
                                let uu___14 =
                                  FStar_Errors_Msg.text
                                    "Could not read checked file:" in
                                let uu___15 = FStar_Pprint.doc_of_string path in
                                FStar_Pprint.op_Hat_Slash_Hat uu___14 uu___15 in
                              [uu___13] in
                            FStar_Errors.raise_error0
                              FStar_Errors_Codes.Fatal_ModuleOrFileNotFound
                              ()
                              (Obj.magic
                                 FStar_Errors_Msg.is_error_message_list_doc)
                              (Obj.magic uu___12)
                        | FStar_Pervasives_Native.Some (uu___12, tcr) ->
                            let uu___13 =
                              FStar_Class_Show.show
                                FStar_Syntax_Print.showable_modul
                                tcr.FStar_CheckedFiles.checked_module in
                            FStar_Compiler_Util.print1 "%s\n" uu___13
                      else
                        (let uu___13 = FStar_Options.list_plugins () in
                         if uu___13
                         then
                           let ps = FStar_TypeChecker_Cfg.list_plugins () in
                           let ts =
                             FStar_Tactics_Interpreter.native_tactics_steps
                               () in
                           ((let uu___15 =
                               let uu___16 =
                                 FStar_Compiler_List.map
                                   (fun p ->
                                      let uu___17 =
                                        FStar_Class_Show.show
                                          FStar_Ident.showable_lident
                                          p.FStar_TypeChecker_Primops_Base.name in
                                      Prims.strcat "  " uu___17) ps in
                               FStar_Compiler_String.concat "\n" uu___16 in
                             FStar_Compiler_Util.print1
                               "Registered plugins:\n%s\n" uu___15);
                            (let uu___16 =
                               let uu___17 =
                                 FStar_Compiler_List.map
                                   (fun p ->
                                      let uu___18 =
                                        FStar_Class_Show.show
                                          FStar_Ident.showable_lident
                                          p.FStar_TypeChecker_Primops_Base.name in
                                      Prims.strcat "  " uu___18) ts in
                               FStar_Compiler_String.concat "\n" uu___17 in
                             FStar_Compiler_Util.print1
                               "Registered tactic plugins:\n%s\n" uu___16))
                         else
                           (let uu___15 = FStar_Options.locate () in
                            if uu___15
                            then
                              ((let uu___17 =
                                  let uu___18 =
                                    FStar_Compiler_Util.get_exec_dir () in
                                  FStar_Compiler_Util.normalize_file_path
                                    uu___18 in
                                FStar_Compiler_Util.print1 "%s\n" uu___17);
                               FStar_Compiler_Effect.exit Prims.int_zero)
                            else
                              (let uu___17 = FStar_Options.locate_lib () in
                               if uu___17
                               then
                                 let uu___18 = FStar_Options.lib_root () in
                                 match uu___18 with
                                 | FStar_Pervasives_Native.None ->
                                     (FStar_Compiler_Util.print_error
                                        "No library found (is --no_default_includes set?)\n";
                                      FStar_Compiler_Effect.exit
                                        Prims.int_one)
                                 | FStar_Pervasives_Native.Some s ->
                                     ((let uu___20 =
                                         FStar_Compiler_Util.normalize_file_path
                                           s in
                                       FStar_Compiler_Util.print1 "%s\n"
                                         uu___20);
                                      FStar_Compiler_Effect.exit
                                        Prims.int_zero)
                               else
                                 (let uu___19 = FStar_Options.locate_ocaml () in
                                  if uu___19
                                  then
                                    ((let uu___21 =
                                        let uu___22 =
                                          let uu___23 =
                                            FStar_Compiler_Util.get_exec_dir
                                              () in
                                          Prims.strcat uu___23 "/../lib" in
                                        FStar_Compiler_Util.normalize_file_path
                                          uu___22 in
                                      FStar_Compiler_Util.print1 "%s\n"
                                        uu___21);
                                     FStar_Compiler_Effect.exit
                                       Prims.int_zero)
                                  else
                                    (let uu___21 =
                                       let uu___22 =
                                         FStar_Options.read_krml_file () in
                                       FStar_Pervasives_Native.uu___is_Some
                                         uu___22 in
                                     if uu___21
                                     then
                                       let path =
                                         let uu___22 =
                                           FStar_Options.read_krml_file () in
                                         FStar_Pervasives_Native.__proj__Some__item__v
                                           uu___22 in
                                       let uu___22 =
                                         FStar_Compiler_Util.load_value_from_file
                                           path in
                                       match uu___22 with
                                       | FStar_Pervasives_Native.None ->
                                           let uu___23 =
                                             let uu___24 =
                                               let uu___25 =
                                                 FStar_Errors_Msg.text
                                                   "Could not read krml file:" in
                                               let uu___26 =
                                                 FStar_Pprint.doc_of_string
                                                   path in
                                               FStar_Pprint.op_Hat_Slash_Hat
                                                 uu___25 uu___26 in
                                             [uu___24] in
                                           FStar_Errors.raise_error0
                                             FStar_Errors_Codes.Fatal_ModuleOrFileNotFound
                                             ()
                                             (Obj.magic
                                                FStar_Errors_Msg.is_error_message_list_doc)
                                             (Obj.magic uu___23)
                                       | FStar_Pervasives_Native.Some
                                           (version, files) ->
                                           ((let uu___24 =
                                               FStar_Class_Show.show
                                                 (FStar_Class_Show.printableshow
                                                    FStar_Class_Printable.printable_int)
                                                 version in
                                             FStar_Compiler_Util.print1
                                               "Karamel format version: %s\n"
                                               uu___24);
                                            FStar_Compiler_List.iter
                                              (fun uu___24 ->
                                                 match uu___24 with
                                                 | (name, decls) ->
                                                     (FStar_Compiler_Util.print1
                                                        "%s:\n" name;
                                                      FStar_Compiler_List.iter
                                                        (fun d ->
                                                           let uu___26 =
                                                             FStar_Class_Show.show
                                                               FStar_Extraction_Krml.showable_decl
                                                               d in
                                                           FStar_Compiler_Util.print1
                                                             "  %s\n" uu___26)
                                                        decls)) files)
                                     else
                                       (let uu___23 =
                                          FStar_Options.lsp_server () in
                                        if uu___23
                                        then
                                          FStar_Interactive_Lsp.start_server
                                            ()
                                        else
                                          (let uu___25 =
                                             FStar_Options.interactive () in
                                           if uu___25
                                           then
                                             (FStar_Syntax_Unionfind.set_rw
                                                ();
                                              (match filenames with
                                               | [] ->
                                                   (FStar_Errors.log_issue0
                                                      FStar_Errors_Codes.Error_MissingFileName
                                                      ()
                                                      (Obj.magic
                                                         FStar_Errors_Msg.is_error_message_string)
                                                      (Obj.magic
                                                         "--ide: Name of current file missing in command line invocation\n");
                                                    FStar_Compiler_Effect.exit
                                                      Prims.int_one)
                                               | uu___27::uu___28::uu___29 ->
                                                   (FStar_Errors.log_issue0
                                                      FStar_Errors_Codes.Error_TooManyFiles
                                                      ()
                                                      (Obj.magic
                                                         FStar_Errors_Msg.is_error_message_string)
                                                      (Obj.magic
                                                         "--ide: Too many files in command line invocation\n");
                                                    FStar_Compiler_Effect.exit
                                                      Prims.int_one)
                                               | filename::[] ->
                                                   let uu___27 =
                                                     FStar_Options.legacy_interactive
                                                       () in
                                                   if uu___27
                                                   then
                                                     FStar_Interactive_Legacy.interactive_mode
                                                       filename
                                                   else
                                                     FStar_Interactive_Ide.interactive_mode
                                                       filename))
                                           else
                                             if
                                               (FStar_Compiler_List.length
                                                  filenames)
                                                 >= Prims.int_one
                                             then
                                               (let uu___27 =
                                                  FStar_Dependencies.find_deps_if_needed
                                                    filenames
                                                    FStar_CheckedFiles.load_parsing_data_from_cache in
                                                match uu___27 with
                                                | (filenames1, dep_graph) ->
                                                    let uu___28 =
                                                      FStar_Universal.batch_mode_tc
                                                        filenames1 dep_graph in
                                                    (match uu___28 with
                                                     | (tcrs, env, cleanup1)
                                                         ->
                                                         ((let uu___30 =
                                                             cleanup1 env in
                                                           ());
                                                          (let module_names =
                                                             FStar_Compiler_List.map
                                                               (fun tcr ->
                                                                  FStar_Universal.module_or_interface_name
                                                                    tcr.FStar_CheckedFiles.checked_module)
                                                               tcrs in
                                                           report_errors
                                                             module_names;
                                                           finished_message
                                                             module_names
                                                             Prims.int_zero))))
                                             else
                                               FStar_Errors.raise_error0
                                                 FStar_Errors_Codes.Error_MissingFileName
                                                 ()
                                                 (Obj.magic
                                                    FStar_Errors_Msg.is_error_message_string)
                                                 (Obj.magic
                                                    "No file provided"))))))))))))))
let (lazy_chooser :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun k ->
    fun i ->
      match k with
      | FStar_Syntax_Syntax.BadLazy ->
          FStar_Compiler_Effect.failwith "lazy chooser: got a BadLazy"
      | FStar_Syntax_Syntax.Lazy_bv ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_bv i
      | FStar_Syntax_Syntax.Lazy_namedv ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_namedv i
      | FStar_Syntax_Syntax.Lazy_binder ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_binder i
      | FStar_Syntax_Syntax.Lazy_letbinding ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_letbinding i
      | FStar_Syntax_Syntax.Lazy_optionstate ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_optionstate i
      | FStar_Syntax_Syntax.Lazy_fvar ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_fvar i
      | FStar_Syntax_Syntax.Lazy_comp ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_comp i
      | FStar_Syntax_Syntax.Lazy_env ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_env i
      | FStar_Syntax_Syntax.Lazy_sigelt ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_sigelt i
      | FStar_Syntax_Syntax.Lazy_universe ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_universe i
      | FStar_Syntax_Syntax.Lazy_proofstate ->
          FStar_Tactics_Embedding.unfold_lazy_proofstate i
      | FStar_Syntax_Syntax.Lazy_goal ->
          FStar_Tactics_Embedding.unfold_lazy_goal i
      | FStar_Syntax_Syntax.Lazy_doc ->
          FStar_Reflection_V2_Embeddings.unfold_lazy_doc i
      | FStar_Syntax_Syntax.Lazy_uvar ->
          FStar_Syntax_Util.exp_string "((uvar))"
      | FStar_Syntax_Syntax.Lazy_universe_uvar ->
          FStar_Syntax_Util.exp_string "((universe_uvar))"
      | FStar_Syntax_Syntax.Lazy_issue ->
          FStar_Syntax_Util.exp_string "((issue))"
      | FStar_Syntax_Syntax.Lazy_ident ->
          FStar_Syntax_Util.exp_string "((ident))"
      | FStar_Syntax_Syntax.Lazy_tref ->
          FStar_Syntax_Util.exp_string "((tref))"
      | FStar_Syntax_Syntax.Lazy_embedding (uu___, t) -> FStar_Thunk.force t
      | FStar_Syntax_Syntax.Lazy_extension s ->
          let uu___ = FStar_Compiler_Util.format1 "((extension %s))" s in
          FStar_Syntax_Util.exp_string uu___
let (setup_hooks : unit -> unit) =
  fun uu___ ->
    FStar_Compiler_Effect.op_Colon_Equals
      FStar_Syntax_DsEnv.ugly_sigelt_to_string_hook
      (FStar_Class_Show.show FStar_Syntax_Print.showable_sigelt);
    FStar_Errors.set_parse_warn_error FStar_Parser_ParseIt.parse_warn_error;
    FStar_Compiler_Effect.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_Compiler_Effect.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some
         (FStar_Class_Show.show FStar_Syntax_Print.showable_term));
    FStar_Compiler_Effect.op_Colon_Equals FStar_Syntax_Util.ttd_f
      (FStar_Pervasives_Native.Some
         (FStar_Class_PP.pp FStar_Syntax_Print.pretty_term));
    FStar_Compiler_Effect.op_Colon_Equals
      FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_V2_Embeddings.e_binder);
    FStar_Compiler_List.iter
      FStar_Tactics_Interpreter.register_tactic_primitive_step
      FStar_Tactics_V1_Primops.ops;
    FStar_Compiler_List.iter
      FStar_Tactics_Interpreter.register_tactic_primitive_step
      FStar_Tactics_V2_Primops.ops
let (handle_error : Prims.exn -> unit) =
  fun e ->
    (let uu___1 = FStar_Errors.handleable e in
     if uu___1 then FStar_Errors.err_exn e else ());
    (let uu___2 = FStar_Options.trace_error () in
     if uu___2
     then
       let uu___3 = FStar_Compiler_Util.message_of_exn e in
       let uu___4 = FStar_Compiler_Util.trace_of_exn e in
       FStar_Compiler_Util.print2_error "Unexpected error\n%s\n%s\n" uu___3
         uu___4
     else
       (let uu___4 =
          let uu___5 = FStar_Errors.handleable e in Prims.op_Negation uu___5 in
        if uu___4
        then
          let uu___5 = FStar_Compiler_Util.message_of_exn e in
          FStar_Compiler_Util.print1_error
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
              (let uu___3 = FStar_Compiler_Util.record_time go in
               match uu___3 with
               | (uu___4, time) ->
                   ((let uu___6 = FStar_Options.query_stats () in
                     if uu___6
                     then
                       let uu___7 = FStar_Compiler_Util.string_of_int time in
                       let uu___8 =
                         let uu___9 = FStar_Getopt.cmdline () in
                         FStar_Compiler_String.concat " " uu___9 in
                       FStar_Compiler_Util.print2_error
                         "TOTAL TIME %s ms: %s\n" uu___7 uu___8
                     else ());
                    cleanup ();
                    FStar_Compiler_Effect.exit Prims.int_zero)))) ()
    with
    | uu___1 ->
        (handle_error uu___1; FStar_Compiler_Effect.exit Prims.int_one)