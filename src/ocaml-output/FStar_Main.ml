open Prims
let (uu___742 : unit) = FStar_Version.dummy () 
let (process_args :
  unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu____78665  -> FStar_Options.parse_cmd_line () 
let (cleanup : unit -> unit) = fun uu____78678  -> FStar_Util.kill_all () 
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
      let uu____78730 =
        let uu____78732 = FStar_Options.silent ()  in
        Prims.op_Negation uu____78732  in
      if uu____78730
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____78765  ->
                 match uu____78765 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____78796 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____78796
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____78801 =
                            let uu____78803 = FStar_Ident.text_of_lid name
                               in
                            let uu____78805 = FStar_Util.string_of_int time
                               in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____78803 uu____78805
                             in
                          print_to uu____78801
                        else
                          (let uu____78810 =
                             let uu____78812 = FStar_Ident.text_of_lid name
                                in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____78812
                              in
                           print_to uu____78810))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____78825 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____78825))
         else
           (let uu____78830 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____78830))
      else ()
  
let (report_errors :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list -> unit) =
  fun fmods  ->
    (let uu____78867 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____78867 (fun a1  -> ()));
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let (load_native_tactics : unit -> unit) =
  fun uu____78885  ->
    let modules_to_load =
      let uu____78889 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____78889
        (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____78906 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____78906
        FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____78931 = ml_module_name m  in Prims.op_Hat uu____78931 ".ml"
       in
    let cmxs_file m =
      let cmxs =
        let uu____78943 = ml_module_name m  in
        Prims.op_Hat uu____78943 ".cmxs"  in
      let uu____78946 = FStar_Options.find_file cmxs  in
      match uu____78946 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____78955 =
            let uu____78959 = ml_file m  in
            FStar_Options.find_file uu____78959  in
          (match uu____78955 with
           | FStar_Pervasives_Native.None  ->
               let uu____78963 =
                 let uu____78969 =
                   let uu____78971 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____78971
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____78969)
                  in
               FStar_Errors.raise_err uu____78963
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____78982 =
                   let uu____78986 = ml_module_name m  in [uu____78986]  in
                 FStar_Tactics_Load.compile_modules dir uu____78982);
                (let uu____78990 = FStar_Options.find_file cmxs  in
                 match uu____78990 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____78996 =
                       let uu____79002 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____79002)
                        in
                     FStar_Errors.raise_err uu____78996
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
let go : 'Auu____79047 . 'Auu____79047 -> unit =
  fun uu____79052  ->
    let uu____79053 = process_args ()  in
    match uu____79053 with
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
              (let uu____79109 =
                 let uu____79111 = FStar_Options.dep ()  in
                 uu____79111 <> FStar_Pervasives_Native.None  in
               if uu____79109
               then
                 let uu____79120 =
                   FStar_Parser_Dep.collect filenames
                     FStar_Universal.load_parsing_data_from_cache
                    in
                 match uu____79120 with
                 | (uu____79128,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____79138 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____79141 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____79141))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____79138
                  then
                    let uu____79146 =
                      let uu____79152 =
                        let uu____79154 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.op_Hat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found "
                          uu____79154
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____79152)  in
                    FStar_Errors.raise_error uu____79146
                      FStar_Range.dummyRange
                  else
                    (let uu____79161 = FStar_Options.interactive ()  in
                     if uu____79161
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____79169::uu____79170::uu____79171 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____79187 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____79187
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____79194 = FStar_Options.doc ()  in
                        if uu____79194
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____79199 =
                             (FStar_Options.print ()) ||
                               (FStar_Options.print_in_place ())
                              in
                           if uu____79199
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
                               (let uu____79211 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                    FStar_Universal.load_parsing_data_from_cache
                                   in
                                match uu____79211 with
                                | (filenames1,dep_graph1) ->
                                    let uu____79227 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____79227 with
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____79328,t) ->
          FStar_Common.force_thunk t
  
let (setup_hooks : unit -> unit) =
  fun uu____79345  ->
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
    (let uu____79465 = FStar_Options.trace_error ()  in
     if uu____79465
     then
       let uu____79468 = FStar_Util.message_of_exn e  in
       let uu____79470 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____79468
         uu____79470
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____79476 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____79476)
       else ());
    cleanup ();
    report_errors []
  
let (main : unit -> unit) =
  fun uu____79497  ->
    try
      (fun uu___862_79507  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____79509 = FStar_Util.record_time go  in
               match uu____79509 with
               | (uu____79515,time) ->
                   let uu____79519 =
                     (FStar_Options.print ()) ||
                       (FStar_Options.print_in_place ())
                      in
                   if uu____79519
                   then
                     let uu____79522 = FStar_ST.op_Bang fstar_files  in
                     (match uu____79522 with
                      | FStar_Pervasives_Native.Some filenames ->
                          let printing_mode =
                            let uu____79565 = FStar_Options.print ()  in
                            if uu____79565
                            then FStar_Prettyprint.FromTempToStdout
                            else FStar_Prettyprint.FromTempToFile  in
                          FStar_Prettyprint.generate printing_mode filenames
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Util.print_error
                             "Internal error: List of source files not properly set";
                           (let uu____79576 = FStar_Options.query_stats ()
                               in
                            if uu____79576
                            then
                              let uu____79579 = FStar_Util.string_of_int time
                                 in
                              let uu____79581 =
                                let uu____79583 = FStar_Getopt.cmdline ()  in
                                FStar_String.concat " " uu____79583  in
                              FStar_Util.print2 "TOTAL TIME %s ms: %s\n"
                                uu____79579 uu____79581
                            else ());
                           cleanup ();
                           FStar_All.exit (Prims.parse_int "0")))
                   else ()))) ()
    with
    | uu___861_79597 ->
        (handle_error uu___861_79597; FStar_All.exit (Prims.parse_int "1"))
  