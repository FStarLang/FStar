open Prims
let (uu___742 : unit) = FStar_Version.dummy () 
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____77707  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____77720  -> FStar_Util.kill_all () 
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
      let uu____77772 =
        let uu____77774 = FStar_Options.silent ()  in
        Prims.op_Negation uu____77774  in
      if uu____77772
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____77807  ->
                 match uu____77807 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____77838 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____77838
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____77843 =
                            let uu____77845 = FStar_Ident.text_of_lid name
                               in
                            let uu____77847 = FStar_Util.string_of_int time
                               in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____77845 uu____77847
                             in
                          print_to uu____77843
                        else
                          (let uu____77852 =
                             let uu____77854 = FStar_Ident.text_of_lid name
                                in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____77854
                              in
                           print_to uu____77852))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____77867 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____77867))
         else
           (let uu____77872 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____77872))
      else ()
  
let (report_errors :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list -> unit) =
  fun fmods  ->
    (let uu____77909 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____77909 (fun a1  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____77927  ->
    let modules_to_load =
      let uu____77931 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____77931
        (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____77948 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____77948
        FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____77973 = ml_module_name m  in Prims.op_Hat uu____77973 ".ml"
       in
    let cmxs_file m =
      let cmxs =
        let uu____77985 = ml_module_name m  in
        Prims.op_Hat uu____77985 ".cmxs"  in
      let uu____77988 = FStar_Options.find_file cmxs  in
      match uu____77988 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____77997 =
            let uu____78001 = ml_file m  in
            FStar_Options.find_file uu____78001  in
          (match uu____77997 with
           | FStar_Pervasives_Native.None  ->
               let uu____78005 =
                 let uu____78011 =
                   let uu____78013 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____78013
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____78011)
                  in
               FStar_Errors.raise_err uu____78005
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____78024 =
                   let uu____78028 = ml_module_name m  in [uu____78028]  in
                 FStar_Tactics_Load.compile_modules dir uu____78024);
                (let uu____78032 = FStar_Options.find_file cmxs  in
                 match uu____78032 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____78038 =
                       let uu____78044 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____78044)
                        in
                     FStar_Errors.raise_err uu____78038
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
let go : 'Auu____78089 . 'Auu____78089 -> unit =
  fun uu____78094  ->
    let uu____78095 = process_args ()  in
    match uu____78095 with
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
              (let uu____78151 =
                 let uu____78153 = FStar_Options.dep ()  in
                 uu____78153 <> FStar_Pervasives_Native.None  in
               if uu____78151
               then
                 let uu____78162 =
                   FStar_Parser_Dep.collect filenames
                     FStar_CheckedFiles.load_parsing_data_from_cache
                    in
                 match uu____78162 with
                 | (uu____78170,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____78180 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____78183 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____78183))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____78180
                  then
                    let uu____78188 =
                      let uu____78194 =
                        let uu____78196 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.op_Hat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____78196
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____78194)  in
                    FStar_Errors.raise_error uu____78188
                      FStar_Range.dummyRange
                  else
                    (let uu____78203 = FStar_Options.interactive ()  in
                     if uu____78203
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____78211::uu____78212::uu____78213 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____78229 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____78229
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____78236 = FStar_Options.doc ()  in
                        if uu____78236
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____78241 =
                             (FStar_Options.print ()) ||
                               (FStar_Options.print_in_place ())
                              in
                           if uu____78241
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
                               (let uu____78253 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                    FStar_CheckedFiles.load_parsing_data_from_cache
                                   in
                                match uu____78253 with
                                | (filenames1,dep_graph1) ->
                                    let uu____78269 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____78269 with
                                     | (tcrs,env,delta_env) ->
                                         let module_names_and_times =
                                           FStar_All.pipe_right tcrs
                                             (FStar_List.map
                                                (fun tcr  ->
                                                   ((FStar_Universal.module_or_interface_name
                                                       tcr.FStar_CheckedFiles.checked_module),
                                                     (tcr.FStar_CheckedFiles.tc_time))))
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____78370,t) ->
          FStar_Common.force_thunk t
  
let (setup_hooks : unit -> unit) =
  fun uu____78387  ->
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
    (let uu____78507 = FStar_Options.trace_error ()  in
     if uu____78507
     then
       let uu____78510 = FStar_Util.message_of_exn e  in
       let uu____78512 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____78510
         uu____78512
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____78518 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____78518)
       else ());
    cleanup ();
    report_errors []
  
let (main : unit -> unit) =
  fun uu____78539  ->
    try
      (fun uu___862_78549  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____78551 = FStar_Util.record_time go  in
               match uu____78551 with
               | (uu____78557,time) ->
                   let uu____78561 =
                     (FStar_Options.print ()) ||
                       (FStar_Options.print_in_place ())
                      in
                   if uu____78561
                   then
                     let uu____78564 = FStar_ST.op_Bang fstar_files  in
                     (match uu____78564 with
                      | FStar_Pervasives_Native.Some filenames ->
                          let printing_mode =
                            let uu____78607 = FStar_Options.print ()  in
                            if uu____78607
                            then FStar_Prettyprint.FromTempToStdout
                            else FStar_Prettyprint.FromTempToFile  in
                          FStar_Prettyprint.generate printing_mode filenames
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Util.print_error
                             "Internal error: List of source files not properly set";
                           (let uu____78618 = FStar_Options.query_stats ()
                               in
                            if uu____78618
                            then
                              let uu____78621 = FStar_Util.string_of_int time
                                 in
                              let uu____78623 =
                                let uu____78625 = FStar_Getopt.cmdline ()  in
                                FStar_String.concat " " uu____78625  in
                              FStar_Util.print2 "TOTAL TIME %s ms: %s\n"
                                uu____78621 uu____78623
                            else ());
                           cleanup ();
                           FStar_All.exit (Prims.parse_int "0")))
                   else ()))) ()
    with
    | uu___861_78639 ->
        (handle_error uu___861_78639; FStar_All.exit (Prims.parse_int "1"))
  