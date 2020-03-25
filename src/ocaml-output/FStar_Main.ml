open Prims
let (uu___0 : unit) = FStar_Version.dummy () 
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____12  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____25  -> FStar_Util.kill_all () 
let (finished_message :
  (Prims.bool * FStar_Ident.lident) Prims.list -> Prims.int -> unit) =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > Prims.int_zero
        then FStar_Util.print_error
        else FStar_Util.print_string  in
      let uu____67 =
        let uu____69 = FStar_Options.silent ()  in Prims.op_Negation uu____69
         in
      if uu____67
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____91  ->
                 match uu____91 with
                 | (iface1,name) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____109 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____109
                     then
                       let uu____112 =
                         let uu____114 = FStar_Ident.text_of_lid name  in
                         FStar_Util.format2 "Verified %s: %s\n" tag uu____114
                          in
                       print_to uu____112
                     else ()));
         if errs > Prims.int_zero
         then
           (if errs = Prims.int_one
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____127 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____127))
         else
           (let uu____132 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____132))
      else ()
  
let (report_errors : (Prims.bool * FStar_Ident.lident) Prims.list -> unit) =
  fun fmods  ->
    (let uu____159 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____159 (fun uu____164  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > Prims.int_zero
     then (finished_message fmods nerrs; FStar_All.exit Prims.int_one)
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____178  ->
    let modules_to_load =
      let uu____182 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____182 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____199 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____199 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____224 = ml_module_name m  in Prims.op_Hat uu____224 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____236 = ml_module_name m  in Prims.op_Hat uu____236 ".cmxs"
         in
      let uu____239 = FStar_Options.find_file cmxs  in
      match uu____239 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____248 =
            let uu____252 = ml_file m  in FStar_Options.find_file uu____252
             in
          (match uu____248 with
           | FStar_Pervasives_Native.None  ->
               let uu____256 =
                 let uu____262 =
                   let uu____264 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____264
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____262)
                  in
               FStar_Errors.raise_err uu____256
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____275 =
                   let uu____279 = ml_module_name m  in [uu____279]  in
                 FStar_Tactics_Load.compile_modules dir uu____275);
                (let uu____283 = FStar_Options.find_file cmxs  in
                 match uu____283 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____289 =
                       let uu____295 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____295)
                        in
                     FStar_Errors.raise_err uu____289
                 | FStar_Pervasives_Native.Some f -> f)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files;
    (let uu____321 = FStar_Options.use_native_tactics ()  in
     FStar_Util.iter_opt uu____321 FStar_Tactics_Load.load_tactics_dir)
  
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let go : 'uu____347 . 'uu____347 -> unit =
  fun uu____352  ->
    let uu____353 = process_args ()  in
    match uu____353 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             (FStar_Options.display_usage (); FStar_All.exit Prims.int_zero)
         | FStar_Getopt.Error msg ->
             (FStar_Util.print_error msg; FStar_All.exit Prims.int_one)
         | FStar_Getopt.Success  ->
             (FStar_ST.op_Colon_Equals fstar_files
                (FStar_Pervasives_Native.Some filenames);
              load_native_tactics ();
              (let uu____409 =
                 let uu____411 = FStar_Options.dep ()  in
                 uu____411 <> FStar_Pervasives_Native.None  in
               if uu____409
               then
                 let uu____420 =
                   FStar_Parser_Dep.collect filenames
                     FStar_CheckedFiles.load_parsing_data_from_cache
                    in
                 match uu____420 with
                 | (uu____428,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____438 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____441 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____441))
                      && ((FStar_List.length filenames) > Prims.int_one)
                     in
                  if uu____438
                  then
                    let uu____446 =
                      let uu____452 =
                        let uu____454 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.op_Hat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____454
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____452)  in
                    FStar_Errors.raise_error uu____446 FStar_Range.dummyRange
                  else
                    (let uu____461 = FStar_Options.lsp_server ()  in
                     if uu____461
                     then FStar_Interactive_Lsp.start_server ()
                     else
                       (let uu____466 = FStar_Options.interactive ()  in
                        if uu____466
                        then
                          match filenames with
                          | [] ->
                              (FStar_Errors.log_issue FStar_Range.dummyRange
                                 (FStar_Errors.Error_MissingFileName,
                                   "--ide: Name of current file missing in command line invocation\n");
                               FStar_All.exit Prims.int_one)
                          | uu____474::uu____475::uu____476 ->
                              (FStar_Errors.log_issue FStar_Range.dummyRange
                                 (FStar_Errors.Error_TooManyFiles,
                                   "--ide: Too many files in command line invocation\n");
                               FStar_All.exit Prims.int_one)
                          | filename::[] ->
                              let uu____492 =
                                FStar_Options.legacy_interactive ()  in
                              (if uu____492
                               then
                                 FStar_Interactive_Legacy.interactive_mode
                                   filename
                               else
                                 FStar_Interactive_Ide.interactive_mode
                                   filename)
                        else
                          (let uu____499 =
                             (FStar_Options.print ()) ||
                               (FStar_Options.print_in_place ())
                              in
                           if uu____499
                           then
                             (if FStar_Platform.is_fstar_compiler_using_ocaml
                              then
                                let printing_mode =
                                  let uu____504 = FStar_Options.print ()  in
                                  if uu____504
                                  then FStar_Prettyprint.FromTempToStdout
                                  else FStar_Prettyprint.FromTempToFile  in
                                FStar_Prettyprint.generate printing_mode
                                  filenames
                              else
                                failwith
                                  "You seem to be using the F#-generated version ofthe compiler ; \\o\n                         reindenting is not known to work yet with this version")
                           else
                             if
                               (FStar_List.length filenames) >= Prims.int_one
                             then
                               (let uu____517 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                    FStar_CheckedFiles.load_parsing_data_from_cache
                                   in
                                match uu____517 with
                                | (filenames1,dep_graph1) ->
                                    let uu____533 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____533 with
                                     | (tcrs,env,cleanup1) ->
                                         ((let uu____559 = cleanup1 env  in
                                           ());
                                          (let module_names =
                                             FStar_All.pipe_right tcrs
                                               (FStar_List.map
                                                  (fun tcr  ->
                                                     FStar_Universal.module_or_interface_name
                                                       tcr.FStar_CheckedFiles.checked_module))
                                              in
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
  fun k  ->
    fun i  ->
      match k with
      | FStar_Syntax_Syntax.BadLazy  ->
          failwith "lazy chooser: got a BadLazy"
      | FStar_Syntax_Syntax.Lazy_bv  ->
          FStar_Reflection_Embeddings.unfold_lazy_bv i
      | FStar_Syntax_Syntax.Lazy_binder  ->
          FStar_Reflection_Embeddings.unfold_lazy_binder i
      | FStar_Syntax_Syntax.Lazy_optionstate  ->
          FStar_Reflection_Embeddings.unfold_lazy_optionstate i
      | FStar_Syntax_Syntax.Lazy_fvar  ->
          FStar_Reflection_Embeddings.unfold_lazy_fvar i
      | FStar_Syntax_Syntax.Lazy_comp  ->
          FStar_Reflection_Embeddings.unfold_lazy_comp i
      | FStar_Syntax_Syntax.Lazy_env  ->
          FStar_Reflection_Embeddings.unfold_lazy_env i
      | FStar_Syntax_Syntax.Lazy_sigelt  ->
          FStar_Reflection_Embeddings.unfold_lazy_sigelt i
      | FStar_Syntax_Syntax.Lazy_proofstate  ->
          FStar_Tactics_Embedding.unfold_lazy_proofstate i
      | FStar_Syntax_Syntax.Lazy_goal  ->
          FStar_Tactics_Embedding.unfold_lazy_goal i
      | FStar_Syntax_Syntax.Lazy_uvar  ->
          FStar_Syntax_Util.exp_string "((uvar))"
      | FStar_Syntax_Syntax.Lazy_embedding (uu____609,t) ->
          FStar_Thunk.force t
  
let (setup_hooks : unit -> unit) =
  fun uu____626  ->
    FStar_Options.initialize_parse_warn_error
      FStar_Parser_ParseIt.parse_warn_error;
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Tc.unembed_optionstate_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_optionstate)
  
let (handle_error : Prims.exn -> unit) =
  fun e  ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____777 = FStar_Options.trace_error ()  in
     if uu____777
     then
       let uu____780 = FStar_Util.message_of_exn e  in
       let uu____782 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____780
         uu____782
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____788 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____788)
       else ());
    cleanup ();
    report_errors []
  
let main : 'uu____804 . unit -> 'uu____804 =
  fun uu____809  ->
    try
      (fun uu___125_817  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____819 = FStar_Util.record_time go  in
               match uu____819 with
               | (uu____825,time) ->
                   ((let uu____830 = FStar_Options.query_stats ()  in
                     if uu____830
                     then
                       let uu____833 = FStar_Util.string_of_int time  in
                       let uu____835 =
                         let uu____837 = FStar_Getopt.cmdline ()  in
                         FStar_String.concat " " uu____837  in
                       FStar_Util.print2_error "TOTAL TIME %s ms: %s\n"
                         uu____833 uu____835
                     else ());
                    cleanup ();
                    FStar_All.exit Prims.int_zero)))) ()
    with
    | uu___124_849 ->
        (handle_error uu___124_849; FStar_All.exit Prims.int_one)
  