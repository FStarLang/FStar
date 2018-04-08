open Prims
let uu___77 : Prims.unit = FStar_Version.dummy () 
let process_args :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun uu____9  -> FStar_Options.parse_cmd_line () 
let cleanup : Prims.unit -> Prims.unit =
  fun uu____18  -> FStar_Util.kill_all () 
let finished_message :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int -> Prims.unit
  =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > (Prims.parse_int "0")
        then FStar_Util.print_error
        else FStar_Util.print_string  in
      let uu____51 =
        let uu____52 = FStar_Options.silent ()  in Prims.op_Negation uu____52
         in
      if uu____51
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____79  ->
                 match uu____79 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____97 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____97
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____98 =
                            let uu____99 = FStar_Ident.text_of_lid name  in
                            let uu____100 = FStar_Util.string_of_int time  in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              uu____99 uu____100
                             in
                          print_to uu____98
                        else
                          (let uu____102 =
                             let uu____103 = FStar_Ident.text_of_lid name  in
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               uu____103
                              in
                           print_to uu____102))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____106 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____106))
         else
           (let uu____108 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____108))
      else ()
  
let report_errors :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit
  =
  fun fmods  ->
    (let uu____134 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____134 FStar_Pervasives.ignore);
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let codegen :
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____152  ->
    match uu____152 with
    | (umods,env) ->
        let opt = FStar_Options.codegen ()  in
        if opt <> FStar_Pervasives_Native.None
        then
          let mllibs =
            let uu____175 =
              let uu____184 = FStar_Extraction_ML_UEnv.mkContext env  in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____184
                umods
               in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____175  in
          let mllibs1 = FStar_List.flatten mllibs  in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) -> ".fs"
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) ->
                ".krml"
            | uu____207 -> failwith "Unrecognized option"  in
          (match opt with
           | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) ->
               let outdir = FStar_Options.output_dir ()  in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) ->
               let outdir = FStar_Options.output_dir ()  in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) ->
               let outdir = FStar_Options.output_dir ()  in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) ->
               let programs =
                 let uu____222 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1
                    in
                 FStar_List.flatten uu____222  in
               let bin = (FStar_Extraction_Kremlin.current_version, programs)
                  in
               (match programs with
                | (name,uu____233)::[] ->
                    let uu____242 =
                      FStar_Options.prepend_output_dir
                        (Prims.strcat name ext)
                       in
                    FStar_Util.save_value_to_file uu____242 bin
                | uu____243 ->
                    let uu____246 =
                      FStar_Options.prepend_output_dir "out.krml"  in
                    FStar_Util.save_value_to_file uu____246 bin)
           | uu____247 -> failwith "Unrecognized option")
        else ()
  
let load_native_tactics : Prims.unit -> Prims.unit =
  fun uu____253  ->
    let modules_to_load =
      let uu____257 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____257 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____268 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____268 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____285 = ml_module_name m  in Prims.strcat uu____285 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____291 = ml_module_name m  in Prims.strcat uu____291 ".cmxs"
         in
      let uu____292 = FStar_Options.find_file cmxs  in
      match uu____292 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____296 =
            let uu____299 = ml_file m  in FStar_Options.find_file uu____299
             in
          (match uu____296 with
           | FStar_Pervasives_Native.None  ->
               let uu____300 =
                 let uu____305 =
                   let uu____306 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____306
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____305)
                  in
               FStar_Errors.raise_err uu____300
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____310 =
                   let uu____313 = ml_module_name m  in [uu____313]  in
                 FStar_Tactics_Load.compile_modules dir uu____310);
                (let uu____314 = FStar_Options.find_file cmxs  in
                 match uu____314 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____317 =
                       let uu____322 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____322)
                        in
                     FStar_Errors.raise_err uu____317
                 | FStar_Pervasives_Native.Some f -> f)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files
  
let init_warn_error : Prims.unit -> Prims.unit =
  fun uu____336  ->
    let s = FStar_Options.warn_error ()  in
    if s <> "" then FStar_Parser_ParseIt.parse_warn_error s else ()
  
let go : 'Auu____342 . 'Auu____342 -> Prims.unit =
  fun uu____346  ->
    let uu____347 = process_args ()  in
    match uu____347 with
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
              (let uu____365 =
                 let uu____366 = FStar_Options.dep ()  in
                 uu____366 <> FStar_Pervasives_Native.None  in
               if uu____365
               then
                 let uu____371 = FStar_Parser_Dep.collect filenames  in
                 match uu____371 with
                 | (uu____378,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____385 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____387 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____387))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____385
                  then
                    let uu____388 =
                      let uu____393 =
                        let uu____394 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.strcat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found %s"
                          uu____394
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____393)  in
                    FStar_Errors.raise_error uu____388 FStar_Range.dummyRange
                  else
                    (let uu____396 = FStar_Options.interactive ()  in
                     if uu____396
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____398::uu____399::uu____400 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____405 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____405
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____408 = FStar_Options.doc ()  in
                        if uu____408
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____410 = FStar_Options.indent ()  in
                           if uu____410
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
                               (let uu____413 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                   in
                                match uu____413 with
                                | (filenames1,dep_graph1) ->
                                    let uu____426 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____426 with
                                     | (fmods,env) ->
                                         let module_names_and_times =
                                           FStar_All.pipe_right fmods
                                             (FStar_List.map
                                                (fun uu____493  ->
                                                   match uu____493 with
                                                   | (x,t) ->
                                                       ((FStar_Universal.module_or_interface_name
                                                           x), t)))
                                            in
                                         (report_errors
                                            module_names_and_times;
                                          (let uu____514 =
                                             let uu____521 =
                                               FStar_All.pipe_right fmods
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             (uu____521, env)  in
                                           codegen uu____514);
                                          report_errors
                                            module_names_and_times;
                                          finished_message
                                            module_names_and_times
                                            (Prims.parse_int "0"))))
                             else
                               FStar_Errors.log_issue FStar_Range.dummyRange
                                 (FStar_Errors.Error_MissingFileName,
                                   "no file provided\n"))))))))
  
let lazy_chooser :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term
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
  
let main : 'Auu____548 . Prims.unit -> 'Auu____548 =
  fun uu____552  ->
    try
      FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
        (FStar_Pervasives_Native.Some lazy_chooser);
      FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
        (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
      FStar_ST.op_Colon_Equals
        FStar_TypeChecker_Normalize.unembed_binder_knot
        (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder);
      (let uu____659 = FStar_Util.record_time go  in
       match uu____659 with
       | (uu____664,time) ->
           ((let uu____667 = FStar_Options.query_stats ()  in
             if uu____667
             then
               let uu____668 = FStar_Util.string_of_int time  in
               let uu____669 =
                 let uu____670 = FStar_Getopt.cmdline ()  in
                 FStar_String.concat " " uu____670  in
               FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____668 uu____669
             else ());
            cleanup ();
            FStar_All.exit (Prims.parse_int "0")))
    with
    | e ->
        let trace = FStar_Util.trace_of_exn e  in
        (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
         (let uu____687 = FStar_Options.trace_error ()  in
          if uu____687
          then
            let uu____688 = FStar_Util.message_of_exn e  in
            FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____688
              trace
          else
            if Prims.op_Negation (FStar_Errors.handleable e)
            then
              (let uu____690 = FStar_Util.message_of_exn e  in
               FStar_Util.print1_error
                 "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
                 uu____690)
            else ());
         cleanup ();
         report_errors [];
         FStar_All.exit (Prims.parse_int "1"))
  