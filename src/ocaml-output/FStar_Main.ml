open Prims
let (uu___479 : unit) = FStar_Version.dummy () 
let (process_args :
  unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun uu____11  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____22  -> FStar_Util.kill_all () 
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
      let uu____62 =
        let uu____63 = FStar_Options.silent ()  in Prims.op_Negation uu____63
         in
      if uu____62
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____90  ->
                 match uu____90 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____108 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____108
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____109 =
                            let uu____110 = FStar_Ident.text_of_lid name  in
                            let uu____111 = FStar_Util.string_of_int time  in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____110 uu____111
                             in
                          print_to uu____109
                        else
                          (let uu____113 =
                             let uu____114 = FStar_Ident.text_of_lid name  in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____114
                              in
                           print_to uu____113))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____117 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____117))
         else
           (let uu____119 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____119))
      else ()
  
let (report_errors :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> unit)
  =
  fun fmods  ->
    (let uu____147 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____147 (fun a1  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____159  ->
    let modules_to_load =
      let uu____163 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____163 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____176 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____176 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____195 = ml_module_name m  in Prims.strcat uu____195 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____203 = ml_module_name m  in Prims.strcat uu____203 ".cmxs"
         in
      let uu____204 = FStar_Options.find_file cmxs  in
      match uu____204 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____208 =
            let uu____211 = ml_file m  in FStar_Options.find_file uu____211
             in
          (match uu____208 with
           | FStar_Pervasives_Native.None  ->
               let uu____212 =
                 let uu____217 =
                   let uu____218 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____218
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____217)
                  in
               FStar_Errors.raise_err uu____212
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____222 =
                   let uu____225 = ml_module_name m  in [uu____225]  in
                 FStar_Tactics_Load.compile_modules dir uu____222);
                (let uu____226 = FStar_Options.find_file cmxs  in
                 match uu____226 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____229 =
                       let uu____234 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____234)
                        in
                     FStar_Errors.raise_err uu____229
                 | FStar_Pervasives_Native.Some f -> f)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files
  
let (init_warn_error : unit -> unit) =
  fun uu____250  ->
    let s = FStar_Options.warn_error ()  in
    if s <> "" then FStar_Parser_ParseIt.parse_warn_error s else ()
  
let go : 'Auu____258 . 'Auu____258 -> unit =
  fun uu____263  ->
    let uu____264 = process_args ()  in
    match uu____264 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             (FStar_Options.display_usage ();
              FStar_All.exit (Prims.parse_int "0"))
         | FStar_Getopt.Error msg ->
             (FStar_Util.print_string msg;
              FStar_All.exit (Prims.parse_int "1"))
         | FStar_Getopt.Success  ->
             (load_native_tactics ();
              init_warn_error ();
              (let uu____282 =
                 let uu____283 = FStar_Options.dep ()  in
                 uu____283 <> FStar_Pervasives_Native.None  in
               if uu____282
               then
                 let uu____288 = FStar_Parser_Dep.collect filenames  in
                 match uu____288 with
                 | (uu____295,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____302 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____304 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____304))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____302
                  then
                    let uu____305 =
                      let uu____310 =
                        let uu____311 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.strcat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found %s"
                          uu____311
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____310)  in
                    FStar_Errors.raise_error uu____305 FStar_Range.dummyRange
                  else
                    (let uu____313 = FStar_Options.interactive ()  in
                     if uu____313
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____315::uu____316::uu____317 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____322 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____322
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____325 = FStar_Options.doc ()  in
                        if uu____325
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____327 = FStar_Options.indent ()  in
                           if uu____327
                           then
                             (if FStar_Platform.is_fstar_compiler_using_ocaml
                              then FStar_Indent.generate filenames
                              else
                                failwith
                                  "You seem to be using the F#-generated version ofthe compiler ; reindenting is not known to work yet with this version")
                           else
                             if
                               (FStar_List.length filenames) >=
                                 (Prims.parse_int "1")
                             then
                               (let uu____330 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                   in
                                match uu____330 with
                                | (filenames1,dep_graph1) ->
                                    let uu____343 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____343 with
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____429,t) ->
          FStar_Common.force_thunk t
  
let (setup_hooks : unit -> unit) =
  fun uu____485  ->
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder)
  
let (handle_error : Prims.exn -> unit) =
  fun e  ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____598 = FStar_Options.trace_error ()  in
     if uu____598
     then
       let uu____599 = FStar_Util.message_of_exn e  in
       let uu____600 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____599
         uu____600
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____602 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____602)
       else ());
    cleanup ();
    report_errors []
  
let main : 'Auu____617 . unit -> 'Auu____617 =
  fun uu____622  ->
    try
      (fun uu___481_630  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____632 = FStar_Util.record_time go  in
               match uu____632 with
               | (uu____637,time) ->
                   ((let uu____640 = FStar_Options.query_stats ()  in
                     if uu____640
                     then
                       let uu____641 = FStar_Util.string_of_int time  in
                       let uu____642 =
                         let uu____643 = FStar_Getopt.cmdline ()  in
                         FStar_String.concat " " uu____643  in
                       FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____641
                         uu____642
                     else ());
                    cleanup ();
                    FStar_All.exit (Prims.parse_int "0"))))) ()
    with
    | uu___480_650 ->
        (handle_error uu___480_650; FStar_All.exit (Prims.parse_int "1"))
  