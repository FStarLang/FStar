open Prims
let (uu___0 : unit) = FStar_Version.dummy ()
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____10 -> FStar_Options.parse_cmd_line ()
let (cleanup : unit -> unit) = fun uu____21 -> FStar_Util.kill_all ()
let (finished_message :
  (Prims.bool * FStar_Ident.lident) Prims.list -> Prims.int -> unit) =
  fun fmods ->
    fun errs ->
      let print_to =
        if errs > Prims.int_zero
        then FStar_Util.print_error
        else FStar_Util.print_string in
      let uu____53 =
        let uu____54 = FStar_Options.silent () in Prims.op_Negation uu____54 in
      if uu____53
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____72 ->
                 match uu____72 with
                 | (iface, name) ->
                     let tag =
                       if iface then "i'face (or impl+i'face)" else "module" in
                     let uu____81 =
                       let uu____82 = FStar_Ident.string_of_lid name in
                       FStar_Options.should_print_message uu____82 in
                     if uu____81
                     then
                       let uu____83 =
                         let uu____84 = FStar_Ident.string_of_lid name in
                         FStar_Util.format2 "Verified %s: %s\n" tag uu____84 in
                       print_to uu____83
                     else ()));
         if errs > Prims.int_zero
         then
           (if errs = Prims.int_one
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____87 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____87))
         else
           (let uu____89 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully" in
            FStar_Util.print1 "%s\n" uu____89))
      else ()
let (report_errors : (Prims.bool * FStar_Ident.lident) Prims.list -> unit) =
  fun fmods ->
    (let uu____109 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____109 (fun uu____114 -> ()));
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > Prims.int_zero
     then (finished_message fmods nerrs; FStar_All.exit Prims.int_one)
     else ())
let (load_native_tactics : unit -> unit) =
  fun uu____122 ->
    let modules_to_load =
      let uu____126 = FStar_Options.load () in
      FStar_All.pipe_right uu____126 (FStar_List.map FStar_Ident.lid_of_str) in
    let ml_module_name m = FStar_Extraction_ML_Util.ml_module_name_of_lid m in
    let ml_file m =
      let uu____145 = ml_module_name m in Prims.op_Hat uu____145 ".ml" in
    let cmxs_file m =
      let cmxs =
        let uu____153 = ml_module_name m in Prims.op_Hat uu____153 ".cmxs" in
      let uu____154 =
        let uu____157 =
          FStar_All.pipe_right cmxs FStar_Options.prepend_output_dir in
        FStar_Options.find_file uu____157 in
      match uu____154 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None ->
          let uu____159 =
            let uu____162 =
              let uu____163 = ml_file m in
              FStar_All.pipe_right uu____163 FStar_Options.prepend_output_dir in
            FStar_Options.find_file uu____162 in
          (match uu____159 with
           | FStar_Pervasives_Native.None ->
               let uu____164 =
                 let uu____169 =
                   let uu____170 = ml_file m in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____170 in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____169) in
               FStar_Errors.raise_err uu____164
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml in
               ((let uu____174 =
                   let uu____177 = ml_module_name m in [uu____177] in
                 FStar_Tactics_Load.compile_modules dir uu____174);
                (let uu____178 = FStar_Options.find_file cmxs in
                 match uu____178 with
                 | FStar_Pervasives_Native.None ->
                     let uu____181 =
                       let uu____186 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____186) in
                     FStar_Errors.raise_err uu____181
                 | FStar_Pervasives_Native.Some f -> f))) in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file) in
    FStar_List.iter (fun x -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    (let uu____199 =
       (let uu____202 = FStar_Options.no_load_fstartaclib () in
        Prims.op_Negation uu____202) &&
         (Prims.op_Negation (FStar_Platform.system = FStar_Platform.Windows)) in
     if uu____199 then FStar_Tactics_Load.try_load_lib () else ());
    FStar_Tactics_Load.load_tactics cmxs_files;
    (let uu____206 = FStar_Options.use_native_tactics () in
     FStar_Util.iter_opt uu____206 FStar_Tactics_Load.load_tactics_dir)
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let go : 'uuuuuu225 . 'uuuuuu225 -> unit =
  fun uu____230 ->
    let uu____231 = process_args () in
    match uu____231 with
    | (res, filenames) ->
        (match res with
         | FStar_Getopt.Help ->
             (FStar_Options.display_usage (); FStar_All.exit Prims.int_zero)
         | FStar_Getopt.Error msg ->
             (FStar_Util.print_error msg; FStar_All.exit Prims.int_one)
         | uu____247 when FStar_Options.print_cache_version () ->
             ((let uu____249 =
                 FStar_Util.string_of_int
                   FStar_CheckedFiles.cache_version_number in
               FStar_Util.print1 "F* cache version number: %s\n" uu____249);
              FStar_All.exit Prims.int_zero)
         | FStar_Getopt.Success ->
             (FStar_ST.op_Colon_Equals fstar_files
                (FStar_Pervasives_Native.Some filenames);
              FStar_Syntax_Unionfind.set_ro ();
              (let uu____268 =
                 let uu____269 = FStar_Options.dep () in
                 uu____269 <> FStar_Pervasives_Native.None in
               if uu____268
               then
                 let uu____274 =
                   FStar_Parser_Dep.collect filenames
                     FStar_CheckedFiles.load_parsing_data_from_cache in
                 match uu____274 with
                 | (uu____281, deps) ->
                     (FStar_Parser_Dep.print deps; report_errors [])
               else
                 (let uu____293 =
                    (FStar_Options.print ()) ||
                      (FStar_Options.print_in_place ()) in
                  if uu____293
                  then
                    (if FStar_Platform.is_fstar_compiler_using_ocaml
                     then
                       let printing_mode =
                         let uu____295 = FStar_Options.print () in
                         if uu____295
                         then FStar_Prettyprint.FromTempToStdout
                         else FStar_Prettyprint.FromTempToFile in
                       FStar_Prettyprint.generate printing_mode filenames
                     else
                       failwith
                         "You seem to be using the F#-generated version ofthe compiler ; \\o\n                         reindenting is not known to work yet with this version")
                  else
                    (let uu____299 = FStar_Options.lsp_server () in
                     if uu____299
                     then FStar_Interactive_Lsp.start_server ()
                     else
                       (load_native_tactics ();
                        (let uu____302 = FStar_Options.interactive () in
                         if uu____302
                         then
                           (FStar_Syntax_Unionfind.set_rw ();
                            (match filenames with
                             | [] ->
                                 (FStar_Errors.log_issue
                                    FStar_Range.dummyRange
                                    (FStar_Errors.Error_MissingFileName,
                                      "--ide: Name of current file missing in command line invocation\n");
                                  FStar_All.exit Prims.int_one)
                             | uu____305::uu____306::uu____307 ->
                                 (FStar_Errors.log_issue
                                    FStar_Range.dummyRange
                                    (FStar_Errors.Error_TooManyFiles,
                                      "--ide: Too many files in command line invocation\n");
                                  FStar_All.exit Prims.int_one)
                             | filename::[] ->
                                 let uu____312 =
                                   FStar_Options.legacy_interactive () in
                                 if uu____312
                                 then
                                   FStar_Interactive_Legacy.interactive_mode
                                     filename
                                 else
                                   FStar_Interactive_Ide.interactive_mode
                                     filename))
                         else
                           if (FStar_List.length filenames) >= Prims.int_one
                           then
                             (let uu____315 =
                                FStar_Dependencies.find_deps_if_needed
                                  filenames
                                  FStar_CheckedFiles.load_parsing_data_from_cache in
                              match uu____315 with
                              | (filenames1, dep_graph) ->
                                  let uu____328 =
                                    FStar_Universal.batch_mode_tc filenames1
                                      dep_graph in
                                  (match uu____328 with
                                   | (tcrs, env, cleanup1) ->
                                       ((let uu____354 = cleanup1 env in ());
                                        (let module_names =
                                           FStar_All.pipe_right tcrs
                                             (FStar_List.map
                                                (fun tcr ->
                                                   FStar_Universal.module_or_interface_name
                                                     tcr.FStar_CheckedFiles.checked_module)) in
                                         report_errors module_names;
                                         finished_message module_names
                                           Prims.int_zero))))
                           else
                             FStar_Errors.raise_error
                               (FStar_Errors.Error_MissingFileName,
                                 "No file provided") FStar_Range.dummyRange)))))))
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____394, t) ->
          FStar_Thunk.force t
let (setup_hooks : unit -> unit) =
  fun uu____410 ->
    FStar_Errors.set_parse_warn_error FStar_Parser_ParseIt.parse_warn_error;
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Tc.unembed_optionstate_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_optionstate)
let (handle_error : Prims.exn -> unit) =
  fun e ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____503 = FStar_Options.trace_error () in
     if uu____503
     then
       let uu____504 = FStar_Util.message_of_exn e in
       let uu____505 = FStar_Util.trace_of_exn e in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____504
         uu____505
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____507 = FStar_Util.message_of_exn e in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____507)
       else ());
    cleanup ();
    report_errors []
let main : 'uuuuuu518 . unit -> 'uuuuuu518 =
  fun uu____523 ->
    try
      (fun uu___131_531 ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____533 = FStar_Util.record_time go in
               match uu____533 with
               | (uu____538, time) ->
                   ((let uu____541 = FStar_Options.query_stats () in
                     if uu____541
                     then
                       let uu____542 = FStar_Util.string_of_int time in
                       let uu____543 =
                         let uu____544 = FStar_Getopt.cmdline () in
                         FStar_String.concat " " uu____544 in
                       FStar_Util.print2_error "TOTAL TIME %s ms: %s\n"
                         uu____542 uu____543
                     else ());
                    cleanup ();
                    FStar_All.exit Prims.int_zero)))) ()
    with
    | uu___130_551 ->
        (handle_error uu___130_551; FStar_All.exit Prims.int_one)