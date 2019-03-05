open Prims
let (uu___742 : unit) = FStar_Version.dummy () 
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____83049  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____83062  -> FStar_Util.kill_all () 
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
      let uu____83114 =
        let uu____83116 = FStar_Options.silent ()  in
        Prims.op_Negation uu____83116  in
      if uu____83114
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____83149  ->
                 match uu____83149 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____83180 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____83180
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____83185 =
                            let uu____83187 = FStar_Ident.text_of_lid name
                               in
                            let uu____83189 = FStar_Util.string_of_int time
                               in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____83187 uu____83189
                             in
                          print_to uu____83185
                        else
                          (let uu____83194 =
                             let uu____83196 = FStar_Ident.text_of_lid name
                                in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____83196
                              in
                           print_to uu____83194))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____83209 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____83209))
         else
           (let uu____83214 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____83214))
      else ()
  
let (report_errors :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list -> unit) =
  fun fmods  ->
    (let uu____83251 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____83251 (fun a1  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____83269  ->
    let modules_to_load =
      let uu____83273 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____83273
        (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____83290 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____83290
        FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____83315 = ml_module_name m  in Prims.op_Hat uu____83315 ".ml"
       in
    let cmxs_file m =
      let cmxs =
        let uu____83327 = ml_module_name m  in
        Prims.op_Hat uu____83327 ".cmxs"  in
      let uu____83330 = FStar_Options.find_file cmxs  in
      match uu____83330 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____83339 =
            let uu____83343 = ml_file m  in
            FStar_Options.find_file uu____83343  in
          (match uu____83339 with
           | FStar_Pervasives_Native.None  ->
               let uu____83347 =
                 let uu____83353 =
                   let uu____83355 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____83355
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____83353)
                  in
               FStar_Errors.raise_err uu____83347
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____83366 =
                   let uu____83370 = ml_module_name m  in [uu____83370]  in
                 FStar_Tactics_Load.compile_modules dir uu____83366);
                (let uu____83374 = FStar_Options.find_file cmxs  in
                 match uu____83374 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____83380 =
                       let uu____83386 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____83386)
                        in
                     FStar_Errors.raise_err uu____83380
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
let go : 'Auu____83442 . 'Auu____83442 -> unit =
  fun uu____83447  ->
    let uu____83448 = process_args ()  in
    match uu____83448 with
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
              (let uu____83504 =
                 let uu____83506 = FStar_Options.dep ()  in
                 uu____83506 <> FStar_Pervasives_Native.None  in
               if uu____83504
               then
                 let uu____83515 =
                   FStar_Parser_Dep.collect filenames
                     FStar_Universal.load_parsing_data_from_cache
                    in
                 match uu____83515 with
                 | (uu____83523,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____83533 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____83536 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____83536))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____83533
                  then
                    let uu____83541 =
                      let uu____83547 =
                        let uu____83549 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.op_Hat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____83549
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____83547)  in
                    FStar_Errors.raise_error uu____83541
                      FStar_Range.dummyRange
                  else
                    (let uu____83556 = FStar_Options.interactive ()  in
                     if uu____83556
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____83564::uu____83565::uu____83566 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____83582 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____83582
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____83589 = FStar_Options.doc ()  in
                        if uu____83589
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____83594 =
                             (FStar_Options.print ()) ||
                               (FStar_Options.print_in_place ())
                              in
                           if uu____83594
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
                               (let uu____83606 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                    FStar_Universal.load_parsing_data_from_cache
                                   in
                                match uu____83606 with
                                | (filenames1,dep_graph1) ->
                                    let uu____83622 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____83622 with
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____83723,t) ->
          FStar_Common.force_thunk t
  
let (setup_hooks : unit -> unit) =
  fun uu____83780  ->
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
    (let uu____83900 = FStar_Options.trace_error ()  in
     if uu____83900
     then
       let uu____83903 = FStar_Util.message_of_exn e  in
       let uu____83905 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____83903
         uu____83905
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____83911 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____83911)
       else ());
    cleanup ();
    report_errors []
  
let (main : unit -> unit) =
  fun uu____83932  ->
    try
      (fun uu___862_83942  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____83944 = FStar_Util.record_time go  in
               match uu____83944 with
               | (uu____83950,time) ->
                   let uu____83954 =
                     (FStar_Options.print ()) ||
                       (FStar_Options.print_in_place ())
                      in
                   if uu____83954
                   then
                     let uu____83957 = FStar_ST.op_Bang fstar_files  in
                     (match uu____83957 with
                      | FStar_Pervasives_Native.Some filenames ->
                          let printing_mode =
                            let uu____84000 = FStar_Options.print ()  in
                            if uu____84000
                            then FStar_Prettyprint.FromTempToStdout
                            else FStar_Prettyprint.FromTempToFile  in
                          FStar_Prettyprint.generate printing_mode filenames
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Util.print_error
                             "Internal error: List of source files not properly set";
                           (let uu____84011 = FStar_Options.query_stats ()
                               in
                            if uu____84011
                            then
                              let uu____84014 = FStar_Util.string_of_int time
                                 in
                              let uu____84016 =
                                let uu____84018 = FStar_Getopt.cmdline ()  in
                                FStar_String.concat " " uu____84018  in
                              FStar_Util.print2 "TOTAL TIME %s ms: %s\n"
                                uu____84014 uu____84016
                            else ());
                           cleanup ();
                           FStar_All.exit (Prims.parse_int "0")))
                   else ()))) ()
    with
    | uu___861_84032 ->
        (handle_error uu___861_84032; FStar_All.exit (Prims.parse_int "1"))
  