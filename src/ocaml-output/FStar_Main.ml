open Prims
let (uu___742 : unit) = FStar_Version.dummy () 
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____82929  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____82942  -> FStar_Util.kill_all () 
let (finished_message :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list ->
    Prims.int -> unit)
  =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > (Prims.parse_int "0")
        then FStar_Util.print_error
        else FStar_Util.print_string  in
      let uu____82994 =
        let uu____82996 = FStar_Options.silent ()  in
        Prims.op_Negation uu____82996  in
      if uu____82994
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____83029  ->
                 match uu____83029 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____83060 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____83060
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____83065 =
                            let uu____83067 = FStar_Ident.text_of_lid name
                               in
                            let uu____83069 = FStar_Util.string_of_int time
                               in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____83067 uu____83069
                             in
                          print_to uu____83065
                        else
                          (let uu____83074 =
                             let uu____83076 = FStar_Ident.text_of_lid name
                                in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____83076
                              in
                           print_to uu____83074))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____83089 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____83089))
         else
           (let uu____83094 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____83094))
      else ()
  
let (report_errors :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list -> unit) =
  fun fmods  ->
    (let uu____83131 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____83131 (fun a1  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____83149  ->
    let modules_to_load =
      let uu____83153 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____83153
        (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____83170 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____83170
        FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____83195 = ml_module_name m  in Prims.op_Hat uu____83195 ".ml"
       in
    let cmxs_file m =
      let cmxs =
        let uu____83207 = ml_module_name m  in
        Prims.op_Hat uu____83207 ".cmxs"  in
      let uu____83210 = FStar_Options.find_file cmxs  in
      match uu____83210 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____83219 =
            let uu____83223 = ml_file m  in
            FStar_Options.find_file uu____83223  in
          (match uu____83219 with
           | FStar_Pervasives_Native.None  ->
               let uu____83227 =
                 let uu____83233 =
                   let uu____83235 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____83235
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____83233)
                  in
               FStar_Errors.raise_err uu____83227
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____83246 =
                   let uu____83250 = ml_module_name m  in [uu____83250]  in
                 FStar_Tactics_Load.compile_modules dir uu____83246);
                (let uu____83254 = FStar_Options.find_file cmxs  in
                 match uu____83254 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____83260 =
                       let uu____83266 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____83266)
                        in
                     FStar_Errors.raise_err uu____83260
                 | FStar_Pervasives_Native.Some f -> f)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files
  
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let go : 'Auu____83322 . 'Auu____83322 -> unit =
  fun uu____83327  ->
    let uu____83328 = process_args ()  in
    match uu____83328 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             (FStar_Options.display_usage ();
              FStar_All.exit (Prims.parse_int "0"))
         | FStar_Getopt.Error msg ->
             (FStar_Util.print_string msg;
              FStar_All.exit (Prims.parse_int "1"))
         | FStar_Getopt.Success  ->
             (FStar_ST.op_Colon_Equals fstar_files
                (FStar_Pervasives_Native.Some filenames);
              load_native_tactics ();
              (let uu____83384 =
                 let uu____83386 = FStar_Options.dep ()  in
                 uu____83386 <> FStar_Pervasives_Native.None  in
               if uu____83384
               then
                 let uu____83395 =
                   FStar_Parser_Dep.collect filenames
                     FStar_Universal.load_parsing_data_from_cache
                    in
                 match uu____83395 with
                 | (uu____83403,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____83413 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____83416 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____83416))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____83413
                  then
                    let uu____83421 =
                      let uu____83427 =
                        let uu____83429 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.op_Hat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____83429
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____83427)  in
                    FStar_Errors.raise_error uu____83421
                      FStar_Range.dummyRange
                  else
                    (let uu____83436 = FStar_Options.interactive ()  in
                     if uu____83436
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____83444::uu____83445::uu____83446 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____83462 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____83462
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____83469 = FStar_Options.doc ()  in
                        if uu____83469
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____83474 =
                             (FStar_Options.print ()) ||
                               (FStar_Options.print_in_place ())
                              in
                           if uu____83474
                           then
                             (if FStar_Platform.is_fstar_compiler_using_ocaml
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
                               (let uu____83486 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                    FStar_Universal.load_parsing_data_from_cache
                                   in
                                match uu____83486 with
                                | (filenames1,dep_graph1) ->
                                    let uu____83502 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____83502 with
                                     | (tcrs,env,delta_env) ->
                                         let module_names_and_times =
                                           FStar_All.pipe_right tcrs
                                             (FStar_List.map
                                                (fun tcr  ->
                                                   ((FStar_Universal.module_or_interface_name
                                                       tcr.FStar_Universal.checked_module),
                                                     (tcr.FStar_Universal.tc_time))))
                                            in
                                         (report_errors
                                            module_names_and_times;
                                          finished_message
                                            module_names_and_times
                                            (Prims.parse_int "0"))))
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____83603,t) ->
          FStar_Common.force_thunk t
  
let (setup_hooks : unit -> unit) =
  fun uu____83660  ->
    FStar_Options.initialize_parse_warn_error
      FStar_Parser_ParseIt.parse_warn_error;
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder)
  
let (handle_error : Prims.exn -> unit) =
  fun e  ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____83780 = FStar_Options.trace_error ()  in
     if uu____83780
     then
       let uu____83783 = FStar_Util.message_of_exn e  in
       let uu____83785 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____83783
         uu____83785
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____83791 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____83791)
       else ());
    cleanup ();
    report_errors []
  
let (main : unit -> unit) =
  fun uu____83812  ->
    try
      (fun uu___862_83822  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____83824 = FStar_Util.record_time go  in
               match uu____83824 with
               | (uu____83830,time) ->
                   let uu____83834 =
                     (FStar_Options.print ()) ||
                       (FStar_Options.print_in_place ())
                      in
                   if uu____83834
                   then
                     let uu____83837 = FStar_ST.op_Bang fstar_files  in
                     (match uu____83837 with
                      | FStar_Pervasives_Native.Some filenames ->
                          let printing_mode =
                            let uu____83880 = FStar_Options.print ()  in
                            if uu____83880
                            then FStar_Prettyprint.FromTempToStdout
                            else FStar_Prettyprint.FromTempToFile  in
                          FStar_Prettyprint.generate printing_mode filenames
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Util.print_error
                             "Internal error: List of source files not properly set";
                           (let uu____83891 = FStar_Options.query_stats ()
                               in
                            if uu____83891
                            then
                              let uu____83894 = FStar_Util.string_of_int time
                                 in
                              let uu____83896 =
                                let uu____83898 = FStar_Getopt.cmdline ()  in
                                FStar_String.concat " " uu____83898  in
                              FStar_Util.print2 "TOTAL TIME %s ms: %s\n"
                                uu____83894 uu____83896
                            else ());
                           cleanup ();
                           FStar_All.exit (Prims.parse_int "0")))
                   else ()))) ()
    with
    | uu___861_83912 ->
        (handle_error uu___861_83912; FStar_All.exit (Prims.parse_int "1"))
  