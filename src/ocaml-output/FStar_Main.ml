open Prims
let (uu___0 : unit) = FStar_Version.dummy ()
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____12 -> FStar_Options.parse_cmd_line ()
let (cleanup : unit -> unit) = fun uu____25 -> FStar_Util.kill_all ()
let (finished_message :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list ->
    Prims.int -> unit)
  =
  fun fmods ->
    fun errs ->
      let print_to =
        if errs > (Prims.parse_int "0")
        then FStar_Util.print_error
        else FStar_Util.print_string in
      let uu____77 =
        let uu____79 = FStar_Options.silent () in Prims.op_Negation uu____79 in
      if uu____77
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____112 ->
                 match uu____112 with
                 | ((iface1, name), time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module" in
                     let uu____143 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____143
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____148 =
                            let uu____150 = FStar_Ident.text_of_lid name in
                            let uu____152 = FStar_Util.string_of_int time in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____150 uu____152 in
                          print_to uu____148
                        else
                          (let uu____157 =
                             let uu____159 = FStar_Ident.text_of_lid name in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____159 in
                           print_to uu____157))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____172 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____172))
         else
           (let uu____177 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully" in
            FStar_Util.print1 "%s\n" uu____177))
      else ()
let (report_errors :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list -> unit) =
  fun fmods ->
    (let uu____214 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____214 (fun a1 -> ()));
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
let (load_native_tactics : unit -> unit) =
  fun uu____232 ->
    let modules_to_load =
      let uu____236 = FStar_Options.load () in
      FStar_All.pipe_right uu____236 (FStar_List.map FStar_Ident.lid_of_str) in
    let ml_module_name m =
      let uu____253 = FStar_Extraction_ML_Util.mlpath_of_lid m in
      FStar_All.pipe_right uu____253 FStar_Extraction_ML_Util.flatten_mlpath in
    let ml_file m =
      let uu____278 = ml_module_name m in Prims.op_Hat uu____278 ".ml" in
    let cmxs_file m =
      let cmxs =
        let uu____290 = ml_module_name m in Prims.op_Hat uu____290 ".cmxs" in
      let uu____293 = FStar_Options.find_file cmxs in
      match uu____293 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None ->
          let uu____302 =
            let uu____306 = ml_file m in FStar_Options.find_file uu____306 in
          (match uu____302 with
           | FStar_Pervasives_Native.None ->
               let uu____310 =
                 let uu____316 =
                   let uu____318 = ml_file m in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____318 in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____316) in
               FStar_Errors.raise_err uu____310
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml in
               ((let uu____329 =
                   let uu____333 = ml_module_name m in [uu____333] in
                 FStar_Tactics_Load.compile_modules dir uu____329);
                (let uu____337 = FStar_Options.find_file cmxs in
                 match uu____337 with
                 | FStar_Pervasives_Native.None ->
                     let uu____343 =
                       let uu____349 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____349) in
                     FStar_Errors.raise_err uu____343
                 | FStar_Pervasives_Native.Some f -> f))) in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file) in
    FStar_List.iter (fun x -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let go : 'Auu____394 . 'Auu____394 -> unit =
  fun uu____399 ->
    let uu____400 = process_args () in
    match uu____400 with
    | (res, filenames) ->
        (match res with
         | FStar_Getopt.Help ->
             (FStar_Options.display_usage ();
              FStar_All.exit (Prims.parse_int "0"))
         | FStar_Getopt.Error msg ->
             (FStar_Util.print_error msg;
              FStar_All.exit (Prims.parse_int "1"))
         | FStar_Getopt.Success ->
             (FStar_ST.op_Colon_Equals fstar_files
                (FStar_Pervasives_Native.Some filenames);
              load_native_tactics ();
              (let uu____456 =
                 let uu____458 = FStar_Options.dep () in
                 uu____458 <> FStar_Pervasives_Native.None in
               if uu____456
               then
                 let uu____467 =
                   FStar_Parser_Dep.collect filenames
                     FStar_CheckedFiles.load_parsing_data_from_cache in
                 match uu____467 with
                 | (uu____475, deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____485 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____488 = FStar_Options.expose_interfaces () in
                        Prims.op_Negation uu____488))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1")) in
                  if uu____485
                  then
                    let uu____493 =
                      let uu____499 =
                        let uu____501 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames) in
                        Prims.op_Hat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____501 in
                      (FStar_Errors.Error_TooManyFiles, uu____499) in
                    FStar_Errors.raise_error uu____493 FStar_Range.dummyRange
                  else
                    (let uu____508 = FStar_Options.lsp_server () in
                     if uu____508
                     then FStar_Interactive_Lsp.start_server ()
                     else
                       (let uu____513 = FStar_Options.interactive () in
                        if uu____513
                        then
                          match filenames with
                          | [] ->
                              (FStar_Errors.log_issue FStar_Range.dummyRange
                                 (FStar_Errors.Error_MissingFileName,
                                   "--ide: Name of current file missing in command line invocation\n");
                               FStar_All.exit (Prims.parse_int "1"))
                          | uu____521::uu____522::uu____523 ->
                              (FStar_Errors.log_issue FStar_Range.dummyRange
                                 (FStar_Errors.Error_TooManyFiles,
                                   "--ide: Too many files in command line invocation\n");
                               FStar_All.exit (Prims.parse_int "1"))
                          | filename::[] ->
                              let uu____539 =
                                FStar_Options.legacy_interactive () in
                              (if uu____539
                               then
                                 FStar_Interactive_Legacy.interactive_mode
                                   filename
                               else
                                 FStar_Interactive_Ide.interactive_mode
                                   filename)
                        else
                          (let uu____546 = FStar_Options.doc () in
                           if uu____546
                           then FStar_Fsdoc_Generator.generate filenames
                           else
                             (let uu____551 =
                                (FStar_Options.print ()) ||
                                  (FStar_Options.print_in_place ()) in
                              if uu____551
                              then
                                (if
                                   FStar_Platform.is_fstar_compiler_using_ocaml
                                 then
                                   FStar_Prettyprint.generate
                                     FStar_Prettyprint.ToTempFile filenames
                                 else
                                   failwith
                                     "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
                              else
                                if
                                  (FStar_List.length filenames) >=
                                    (Prims.parse_int "1")
                                then
                                  (let uu____563 =
                                     FStar_Dependencies.find_deps_if_needed
                                       filenames
                                       FStar_CheckedFiles.load_parsing_data_from_cache in
                                   match uu____563 with
                                   | (filenames1, dep_graph1) ->
                                       let uu____579 =
                                         FStar_Universal.batch_mode_tc
                                           filenames1 dep_graph1 in
                                       (match uu____579 with
                                        | (tcrs, env, cleanup1) ->
                                            ((let uu____605 = cleanup1 env in
                                              ());
                                             (let module_names_and_times =
                                                FStar_All.pipe_right tcrs
                                                  (FStar_List.map
                                                     (fun tcr ->
                                                        ((FStar_Universal.module_or_interface_name
                                                            tcr.FStar_CheckedFiles.checked_module),
                                                          (tcr.FStar_CheckedFiles.tc_time)))) in
                                              report_errors
                                                module_names_and_times;
                                              finished_message
                                                module_names_and_times
                                                (Prims.parse_int "0")))))
                                else
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Error_MissingFileName,
                                      "No file provided")
                                    FStar_Range.dummyRange))))))))
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____676, t) ->
          FStar_Common.force_thunk t
let (setup_hooks : unit -> unit) =
  fun uu____693 ->
    FStar_Options.initialize_parse_warn_error
      FStar_Parser_ParseIt.parse_warn_error;
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder)
let (handle_error : Prims.exn -> unit) =
  fun e ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____813 = FStar_Options.trace_error () in
     if uu____813
     then
       let uu____816 = FStar_Util.message_of_exn e in
       let uu____818 = FStar_Util.trace_of_exn e in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____816
         uu____818
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____824 = FStar_Util.message_of_exn e in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____824)
       else ());
    cleanup ();
    report_errors []
let (main : unit -> unit) =
  fun uu____845 ->
    try
      (fun uu___122_855 ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____857 = FStar_Util.record_time go in
               match uu____857 with
               | (uu____863, time) ->
                   let uu____867 =
                     (FStar_Options.print ()) ||
                       (FStar_Options.print_in_place ()) in
                   if uu____867
                   then
                     let uu____870 = FStar_ST.op_Bang fstar_files in
                     (match uu____870 with
                      | FStar_Pervasives_Native.Some filenames ->
                          let printing_mode =
                            let uu____913 = FStar_Options.print () in
                            if uu____913
                            then FStar_Prettyprint.FromTempToStdout
                            else FStar_Prettyprint.FromTempToFile in
                          FStar_Prettyprint.generate printing_mode filenames
                      | FStar_Pervasives_Native.None ->
                          (FStar_Util.print_error
                             "Internal error: List of source files not properly set";
                           (let uu____924 = FStar_Options.query_stats () in
                            if uu____924
                            then
                              let uu____927 = FStar_Util.string_of_int time in
                              let uu____929 =
                                let uu____931 = FStar_Getopt.cmdline () in
                                FStar_String.concat " " uu____931 in
                              FStar_Util.print2 "TOTAL TIME %s ms: %s\n"
                                uu____927 uu____929
                            else ());
                           cleanup ();
                           FStar_All.exit (Prims.parse_int "0")))
                   else ()))) ()
    with
    | uu___121_945 ->
        (handle_error uu___121_945; FStar_All.exit (Prims.parse_int "1"))