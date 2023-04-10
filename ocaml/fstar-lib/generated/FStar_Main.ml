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
        (FStar_Compiler_Effect.op_Bar_Greater fmods
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
                     else ()));
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
    (let uu___1 = FStar_Errors.report_all () in
     FStar_Compiler_Effect.op_Bar_Greater uu___1 (fun uu___2 -> ()));
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
      FStar_Compiler_Effect.op_Bar_Greater uu___1
        (FStar_Compiler_List.map FStar_Ident.lid_of_str) in
    let cmxs_to_load =
      let uu___1 = FStar_Options.load_cmxs () in
      FStar_Compiler_Effect.op_Bar_Greater uu___1
        (FStar_Compiler_List.map FStar_Ident.lid_of_str) in
    let ml_module_name m = FStar_Extraction_ML_Util.ml_module_name_of_lid m in
    let ml_file m =
      let uu___1 = ml_module_name m in Prims.op_Hat uu___1 ".ml" in
    let cmxs_file m =
      let cmxs = let uu___1 = ml_module_name m in Prims.op_Hat uu___1 ".cmxs" in
      let uu___1 = FStar_Options.find_file cmxs in
      match uu___1 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None ->
          if FStar_Compiler_List.contains m cmxs_to_load
          then
            let uu___2 =
              let uu___3 =
                FStar_Compiler_Util.format1 "Could not find %s to load" cmxs in
              (FStar_Errors_Codes.Fatal_FailToCompileNativeTactic, uu___3) in
            FStar_Errors.raise_err uu___2
          else
            (let uu___3 =
               let uu___4 = ml_file m in FStar_Options.find_file uu___4 in
             match uu___3 with
             | FStar_Pervasives_Native.None ->
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = ml_file m in
                     FStar_Compiler_Util.format1
                       "Failed to compile native tactic; extracted module %s not found"
                       uu___6 in
                   (FStar_Errors_Codes.Fatal_FailToCompileNativeTactic,
                     uu___5) in
                 FStar_Errors.raise_err uu___4
             | FStar_Pervasives_Native.Some ml ->
                 let dir = FStar_Compiler_Util.dirname ml in
                 ((let uu___5 = let uu___6 = ml_module_name m in [uu___6] in
                   FStar_Tactics_Load.compile_modules dir uu___5);
                  (let uu___5 = FStar_Options.find_file cmxs in
                   match uu___5 with
                   | FStar_Pervasives_Native.None ->
                       let uu___6 =
                         let uu___7 =
                           FStar_Compiler_Util.format1
                             "Failed to compile native tactic; compiled object %s not found"
                             cmxs in
                         (FStar_Errors_Codes.Fatal_FailToCompileNativeTactic,
                           uu___7) in
                       FStar_Errors.raise_err uu___6
                   | FStar_Pervasives_Native.Some f -> f))) in
    let cmxs_files =
      FStar_Compiler_Effect.op_Bar_Greater
        (FStar_Compiler_List.op_At modules_to_load cmxs_to_load)
        (FStar_Compiler_List.map cmxs_file) in
    (let uu___2 = FStar_Options.debug_any () in
     if uu___2
     then
       FStar_Compiler_Util.print1 "Will try to load cmxs files: %s\n"
         (FStar_String.concat ", " cmxs_files)
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
         | uu___2 when FStar_Options.print_cache_version () ->
             ((let uu___4 =
                 FStar_Compiler_Util.string_of_int
                   FStar_CheckedFiles.cache_version_number in
               FStar_Compiler_Util.print1 "F* cache version number: %s\n"
                 uu___4);
              FStar_Compiler_Effect.exit Prims.int_zero)
         | FStar_Getopt.Success ->
             (FStar_Compiler_Effect.op_Colon_Equals fstar_files
                (FStar_Pervasives_Native.Some filenames);
              FStar_Syntax_Unionfind.set_ro ();
              (let uu___4 =
                 let uu___5 = FStar_Options.dep () in
                 uu___5 <> FStar_Pervasives_Native.None in
               if uu___4
               then
                 let uu___5 =
                   FStar_Parser_Dep.collect filenames
                     FStar_CheckedFiles.load_parsing_data_from_cache in
                 match uu___5 with
                 | (uu___6, deps) ->
                     (FStar_Parser_Dep.print deps; report_errors [])
               else
                 (let uu___6 =
                    (FStar_Options.print ()) ||
                      (FStar_Options.print_in_place ()) in
                  if uu___6
                  then
                    (if FStar_Platform.is_fstar_compiler_using_ocaml
                     then
                       let printing_mode =
                         let uu___7 = FStar_Options.print () in
                         if uu___7
                         then FStar_Prettyprint.FromTempToStdout
                         else FStar_Prettyprint.FromTempToFile in
                       FStar_Prettyprint.generate printing_mode filenames
                     else
                       failwith
                         "You seem to be using the F#-generated version ofthe compiler ; \\o\n                         reindenting is not known to work yet with this version")
                  else
                    (let uu___8 = FStar_Options.lsp_server () in
                     if uu___8
                     then FStar_Interactive_Lsp.start_server ()
                     else
                       (load_native_tactics ();
                        (let uu___11 = FStar_Options.interactive () in
                         if uu___11
                         then
                           (FStar_Syntax_Unionfind.set_rw ();
                            (match filenames with
                             | [] ->
                                 (FStar_Errors.log_issue
                                    FStar_Compiler_Range.dummyRange
                                    (FStar_Errors_Codes.Error_MissingFileName,
                                      "--ide: Name of current file missing in command line invocation\n");
                                  FStar_Compiler_Effect.exit Prims.int_one)
                             | uu___13::uu___14::uu___15 ->
                                 (FStar_Errors.log_issue
                                    FStar_Compiler_Range.dummyRange
                                    (FStar_Errors_Codes.Error_TooManyFiles,
                                      "--ide: Too many files in command line invocation\n");
                                  FStar_Compiler_Effect.exit Prims.int_one)
                             | filename::[] ->
                                 let uu___13 =
                                   FStar_Options.legacy_interactive () in
                                 if uu___13
                                 then
                                   FStar_Interactive_Legacy.interactive_mode
                                     filename
                                 else
                                   FStar_Interactive_Ide.interactive_mode
                                     filename))
                         else
                           if
                             (FStar_Compiler_List.length filenames) >=
                               Prims.int_one
                           then
                             (let uu___13 =
                                FStar_Dependencies.find_deps_if_needed
                                  filenames
                                  FStar_CheckedFiles.load_parsing_data_from_cache in
                              match uu___13 with
                              | (filenames1, dep_graph) ->
                                  let uu___14 =
                                    FStar_Universal.batch_mode_tc filenames1
                                      dep_graph in
                                  (match uu___14 with
                                   | (tcrs, env, cleanup1) ->
                                       ((let uu___16 = cleanup1 env in ());
                                        (let module_names =
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             tcrs
                                             (FStar_Compiler_List.map
                                                (fun tcr ->
                                                   FStar_Universal.module_or_interface_name
                                                     tcr.FStar_CheckedFiles.checked_module)) in
                                         report_errors module_names;
                                         finished_message module_names
                                           Prims.int_zero))))
                           else
                             FStar_Errors.raise_error
                               (FStar_Errors_Codes.Error_MissingFileName,
                                 "No file provided")
                               FStar_Compiler_Range.dummyRange)))))))
let (lazy_chooser :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazyinfo ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun k ->
    fun i ->
      match k with
      | FStar_Syntax_Syntax.BadLazy -> failwith "lazy chooser: got a BadLazy"
      | FStar_Syntax_Syntax.Lazy_bv ->
          FStar_Reflection_Embeddings.unfold_lazy_bv i
      | FStar_Syntax_Syntax.Lazy_binder ->
          FStar_Reflection_Embeddings.unfold_lazy_binder i
      | FStar_Syntax_Syntax.Lazy_letbinding ->
          FStar_Reflection_Embeddings.unfold_lazy_letbinding i
      | FStar_Syntax_Syntax.Lazy_optionstate ->
          FStar_Reflection_Embeddings.unfold_lazy_optionstate i
      | FStar_Syntax_Syntax.Lazy_fvar ->
          FStar_Reflection_Embeddings.unfold_lazy_fvar i
      | FStar_Syntax_Syntax.Lazy_comp ->
          FStar_Reflection_Embeddings.unfold_lazy_comp i
      | FStar_Syntax_Syntax.Lazy_env ->
          FStar_Reflection_Embeddings.unfold_lazy_env i
      | FStar_Syntax_Syntax.Lazy_sigelt ->
          FStar_Reflection_Embeddings.unfold_lazy_sigelt i
      | FStar_Syntax_Syntax.Lazy_proofstate ->
          FStar_Tactics_Embedding.unfold_lazy_proofstate i
      | FStar_Syntax_Syntax.Lazy_goal ->
          FStar_Tactics_Embedding.unfold_lazy_goal i
      | FStar_Syntax_Syntax.Lazy_uvar ->
          FStar_Syntax_Util.exp_string "((uvar))"
      | FStar_Syntax_Syntax.Lazy_embedding (uu___, t) -> FStar_Thunk.force t
      | FStar_Syntax_Syntax.Lazy_universe ->
          FStar_Reflection_Embeddings.unfold_lazy_universe i
      | FStar_Syntax_Syntax.Lazy_universe_uvar ->
          FStar_Syntax_Util.exp_string "((universe_uvar))"
let (setup_hooks : unit -> unit) =
  fun uu___ ->
    FStar_Errors.set_parse_warn_error FStar_Parser_ParseIt.parse_warn_error;
    FStar_Compiler_Effect.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_Compiler_Effect.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_Compiler_Effect.op_Colon_Equals
      FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder);
    FStar_Extraction_Krml.init ()
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
                         FStar_String.concat " " uu___9 in
                       FStar_Compiler_Util.print2_error
                         "TOTAL TIME %s ms: %s\n" uu___7 uu___8
                     else ());
                    cleanup ();
                    FStar_Compiler_Effect.exit Prims.int_zero)))) ()
    with
    | uu___1 ->
        (handle_error uu___1; FStar_Compiler_Effect.exit Prims.int_one)