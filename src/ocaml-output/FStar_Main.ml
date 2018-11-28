open Prims
let (uu___477 : unit) = FStar_Version.dummy () 
let (process_args :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun uu____13  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____26  -> FStar_Util.kill_all () 
let (finished_message :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int -> unit)
  =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > (Prims.parse_int "0")
        then FStar_Util.print_error
        else FStar_Util.print_string  in
      let uu____78 =
        let uu____80 = FStar_Options.silent ()  in Prims.op_Negation uu____80
         in
      if uu____78
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____113  ->
                 match uu____113 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____144 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____144
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____149 =
                            let uu____151 = FStar_Ident.text_of_lid name  in
                            let uu____153 = FStar_Util.string_of_int time  in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____151 uu____153
                             in
                          print_to uu____149
                        else
                          (let uu____158 =
                             let uu____160 = FStar_Ident.text_of_lid name  in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____160
                              in
                           print_to uu____158))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____173 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____173))
         else
           (let uu____178 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____178))
      else ()
  
let (report_errors :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> unit)
  =
  fun fmods  ->
    (let uu____215 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____215 (fun a1  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____233  ->
    let modules_to_load =
      let uu____237 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____237 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____254 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____254 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____279 = ml_module_name m  in Prims.strcat uu____279 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____291 = ml_module_name m  in Prims.strcat uu____291 ".cmxs"
         in
      let uu____294 = FStar_Options.find_file cmxs  in
      match uu____294 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____303 =
            let uu____307 = ml_file m  in FStar_Options.find_file uu____307
             in
          (match uu____303 with
           | FStar_Pervasives_Native.None  ->
               let uu____311 =
                 let uu____317 =
                   let uu____319 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____319
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____317)
                  in
               FStar_Errors.raise_err uu____311
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____330 =
                   let uu____334 = ml_module_name m  in [uu____334]  in
                 FStar_Tactics_Load.compile_modules dir uu____330);
                (let uu____338 = FStar_Options.find_file cmxs  in
                 match uu____338 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____344 =
                       let uu____350 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____350)
                        in
                     FStar_Errors.raise_err uu____344
                 | FStar_Pervasives_Native.Some f -> f)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files
  
let (init_warn_error : unit -> unit) =
  fun uu____379  ->
    let s = FStar_Options.warn_error ()  in
    if s <> "" then FStar_Parser_ParseIt.parse_warn_error s else ()
  
let (fstar_files :
  Prims.string Prims.list FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let go : 'Auu____420 . 'Auu____420 -> unit =
  fun uu____425  ->
    let uu____426 = process_args ()  in
    match uu____426 with
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
              init_warn_error ();
              (let uu____483 =
                 let uu____485 = FStar_Options.dep ()  in
                 uu____485 <> FStar_Pervasives_Native.None  in
               if uu____483
               then
                 let uu____494 = FStar_Parser_Dep.collect filenames  in
                 match uu____494 with
                 | (uu____502,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____512 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____515 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____515))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____512
                  then
                    let uu____520 =
                      let uu____526 =
                        let uu____528 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.strcat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____528
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____526)  in
                    FStar_Errors.raise_error uu____520 FStar_Range.dummyRange
                  else
                    (let uu____535 = FStar_Options.interactive ()  in
                     if uu____535
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____543::uu____544::uu____545 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____561 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____561
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____568 = FStar_Options.doc ()  in
                        if uu____568
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____573 =
                             (FStar_Options.print ()) ||
                               (FStar_Options.print_in_place ())
                              in
                           if uu____573
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
                               (let uu____585 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                   in
                                match uu____585 with
                                | (filenames1,dep_graph1) ->
                                    let uu____601 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____601 with
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____702,t) ->
          FStar_Common.force_thunk t
  
let (setup_hooks : unit -> unit) =
  fun uu____759  ->
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder)
  
let (handle_error : Prims.exn -> unit) =
  fun e  ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____878 = FStar_Options.trace_error ()  in
     if uu____878
     then
       let uu____881 = FStar_Util.message_of_exn e  in
       let uu____883 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____881
         uu____883
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____889 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____889)
       else ());
    cleanup ();
    report_errors []
  
let (main : unit -> unit) =
  fun uu____910  ->
    try
      (fun uu___479_920  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____922 = FStar_Util.record_time go  in
               match uu____922 with
               | (uu____928,time) ->
                   let uu____932 =
                     (FStar_Options.print ()) ||
                       (FStar_Options.print_in_place ())
                      in
                   if uu____932
                   then
                     let uu____935 = FStar_ST.op_Bang fstar_files  in
                     (match uu____935 with
                      | FStar_Pervasives_Native.Some filenames ->
                          let printing_mode =
                            let uu____978 = FStar_Options.print ()  in
                            if uu____978
                            then FStar_Prettyprint.FromTempToStdout
                            else FStar_Prettyprint.FromTempToFile  in
                          FStar_Prettyprint.generate printing_mode filenames
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Util.print_error
                             "Internal error: List of source files not properly set";
                           (let uu____989 = FStar_Options.query_stats ()  in
                            if uu____989
                            then
                              let uu____992 = FStar_Util.string_of_int time
                                 in
                              let uu____994 =
                                let uu____996 = FStar_Getopt.cmdline ()  in
                                FStar_String.concat " " uu____996  in
                              FStar_Util.print2 "TOTAL TIME %s ms: %s\n"
                                uu____992 uu____994
                            else ());
                           cleanup ();
                           FStar_All.exit (Prims.parse_int "0")))
                   else ()))) ()
    with
    | uu___478_1010 ->
        (handle_error uu___478_1010; FStar_All.exit (Prims.parse_int "1"))
  