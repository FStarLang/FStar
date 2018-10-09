open Prims
let (uu___478 : unit) = FStar_Version.dummy () 
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
  
let (codegen :
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env,FStar_Universal.delta_env)
    FStar_Pervasives_Native.tuple3 -> unit)
  =
  fun uu____241  ->
    match uu____241 with
    | (umods,env,delta1) ->
        let opt = FStar_Options.codegen ()  in
        if opt <> FStar_Pervasives_Native.None
        then
          let env1 = FStar_Universal.apply_delta_env env delta1  in
          let mllibs =
            let uu____271 =
              let uu____280 = FStar_Extraction_ML_UEnv.mkContext env1  in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____280
                umods
               in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____271  in
          let mllibs1 = FStar_List.flatten mllibs  in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) -> ".fs"
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) ->
                ".krml"
            | uu____309 -> failwith "Unrecognized option"  in
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
                 let uu____334 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1
                    in
                 FStar_List.flatten uu____334  in
               let bin = (FStar_Extraction_Kremlin.current_version, programs)
                  in
               (match programs with
                | (name,uu____361)::[] ->
                    let uu____374 =
                      FStar_Options.prepend_output_dir
                        (Prims.strcat name ext)
                       in
                    FStar_Util.save_value_to_file uu____374 bin
                | uu____376 ->
                    let uu____384 =
                      FStar_Options.prepend_output_dir "out.krml"  in
                    FStar_Util.save_value_to_file uu____384 bin)
           | uu____387 -> failwith "Unrecognized option")
        else ()
  
let (load_native_tactics : unit -> unit) =
  fun uu____398  ->
    let modules_to_load =
      let uu____402 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____402 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____419 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____419 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____444 = ml_module_name m  in Prims.strcat uu____444 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____456 = ml_module_name m  in Prims.strcat uu____456 ".cmxs"
         in
      let uu____459 = FStar_Options.find_file cmxs  in
      match uu____459 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____468 =
            let uu____472 = ml_file m  in FStar_Options.find_file uu____472
             in
          (match uu____468 with
           | FStar_Pervasives_Native.None  ->
               let uu____476 =
                 let uu____482 =
                   let uu____484 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____484
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____482)
                  in
               FStar_Errors.raise_err uu____476
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____495 =
                   let uu____499 = ml_module_name m  in [uu____499]  in
                 FStar_Tactics_Load.compile_modules dir uu____495);
                (let uu____503 = FStar_Options.find_file cmxs  in
                 match uu____503 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____509 =
                       let uu____515 =
                         FStar_Util.format1
                           "Failed to compile native tactic; compiled object %s not found"
                           cmxs
                          in
                       (FStar_Errors.Fatal_FailToCompileNativeTactic,
                         uu____515)
                        in
                     FStar_Errors.raise_err uu____509
                 | FStar_Pervasives_Native.Some f -> f)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files
  
let (init_warn_error : unit -> unit) =
  fun uu____544  ->
    let s = FStar_Options.warn_error ()  in
    if s <> "" then FStar_Parser_ParseIt.parse_warn_error s else ()
  
let go : 'Auu____558 . 'Auu____558 -> unit =
  fun uu____563  ->
    let uu____564 = process_args ()  in
    match uu____564 with
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
              (let uu____588 =
                 let uu____590 = FStar_Options.dep ()  in
                 uu____590 <> FStar_Pervasives_Native.None  in
               if uu____588
               then
                 let uu____599 = FStar_Parser_Dep.collect filenames  in
                 match uu____599 with
                 | (uu____607,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____617 =
                    ((FStar_Options.use_extracted_interfaces ()) &&
                       (let uu____620 = FStar_Options.expose_interfaces ()
                           in
                        Prims.op_Negation uu____620))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____617
                  then
                    let uu____625 =
                      let uu____631 =
                        let uu____633 =
                          FStar_Util.string_of_int
                            (FStar_List.length filenames)
                           in
                        Prims.strcat
                          "Only one command line file is allowed if --use_extracted_interfaces is set, found %s"
                          uu____633
                         in
                      (FStar_Errors.Error_TooManyFiles, uu____631)  in
                    FStar_Errors.raise_error uu____625 FStar_Range.dummyRange
                  else
                    (let uu____640 = FStar_Options.interactive ()  in
                     if uu____640
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____648::uu____649::uu____650 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____666 =
                             FStar_Options.legacy_interactive ()  in
                           (if uu____666
                            then
                              FStar_Interactive_Legacy.interactive_mode
                                filename
                            else
                              FStar_Interactive_Ide.interactive_mode filename)
                     else
                       (let uu____673 = FStar_Options.doc ()  in
                        if uu____673
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____678 = FStar_Options.indent ()  in
                           if uu____678
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
                               (let uu____690 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                   in
                                match uu____690 with
                                | (filenames1,dep_graph1) ->
                                    let uu____706 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____706 with
                                     | (fmods,env,delta_env) ->
                                         let module_names_and_times =
                                           FStar_All.pipe_right fmods
                                             (FStar_List.map
                                                (fun uu____802  ->
                                                   match uu____802 with
                                                   | (x,t) ->
                                                       ((FStar_Universal.module_or_interface_name
                                                           x), t)))
                                            in
                                         (report_errors
                                            module_names_and_times;
                                          (let uu____830 =
                                             let uu____839 =
                                               FStar_All.pipe_right fmods
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             (uu____839, env, delta_env)  in
                                           codegen uu____830);
                                          report_errors
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
      | FStar_Syntax_Syntax.Lazy_embedding (uu____884,t) ->
          FStar_Common.force_thunk t
  
let (setup_hooks : unit -> unit) =
  fun uu____941  ->
    FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
      (FStar_Pervasives_Native.Some lazy_chooser);
    FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
      (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string);
    FStar_ST.op_Colon_Equals FStar_TypeChecker_Normalize.unembed_binder_knot
      (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder)
  
let (handle_error : Prims.exn -> unit) =
  fun e  ->
    if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
    (let uu____1060 = FStar_Options.trace_error ()  in
     if uu____1060
     then
       let uu____1063 = FStar_Util.message_of_exn e  in
       let uu____1065 = FStar_Util.trace_of_exn e  in
       FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____1063
         uu____1065
     else
       if Prims.op_Negation (FStar_Errors.handleable e)
       then
         (let uu____1071 = FStar_Util.message_of_exn e  in
          FStar_Util.print1_error
            "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
            uu____1071)
       else ());
    cleanup ();
    report_errors []
  
let main : 'Auu____1092 . unit -> 'Auu____1092 =
  fun uu____1097  ->
    try
      (fun uu___480_1105  ->
         match () with
         | () ->
             (setup_hooks ();
              (let uu____1107 = FStar_Util.record_time go  in
               match uu____1107 with
               | (uu____1113,time) ->
                   ((let uu____1118 = FStar_Options.query_stats ()  in
                     if uu____1118
                     then
                       let uu____1121 = FStar_Util.string_of_int time  in
                       let uu____1123 =
                         let uu____1125 = FStar_Getopt.cmdline ()  in
                         FStar_String.concat " " uu____1125  in
                       FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____1121
                         uu____1123
                     else ());
                    cleanup ();
                    FStar_All.exit (Prims.parse_int "0"))))) ()
    with
    | uu___479_1137 ->
        (handle_error uu___479_1137; FStar_All.exit (Prims.parse_int "1"))
  