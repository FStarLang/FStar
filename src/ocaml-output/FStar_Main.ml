open Prims

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
      let uu____61 =
        let uu____62 = FStar_Options.silent ()  in Prims.op_Negation uu____62
         in
      if uu____61
      then
        let uu____63 =
          FStar_All.pipe_right fmods
            (FStar_List.iter
               (fun uu____89  ->
                  match uu____89 with
                  | ((iface1,name),time) ->
                      let tag =
                        if iface1
                        then "i'face (or impl+i'face)"
                        else "module"  in
                      let uu____107 =
                        FStar_Options.should_print_message
                          name.FStar_Ident.str
                         in
                      if uu____107
                      then
                        (if time >= (Prims.parse_int "0")
                         then
                           let uu____108 =
                             let uu____109 = FStar_Ident.text_of_lid name  in
                             let uu____110 = FStar_Util.string_of_int time
                                in
                             FStar_Util.format3
                               "Verified %s: %s (%s milliseconds)\n" tag
                               uu____109 uu____110
                              in
                           print_to uu____108
                         else
                           (let uu____112 =
                              let uu____113 = FStar_Ident.text_of_lid name
                                 in
                              FStar_Util.format2 "Verified %s: %s\n" tag
                                uu____113
                               in
                            print_to uu____112))
                      else ()))
           in
        (if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____116 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____116))
         else
           (let uu____118 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____118))
      else ()
  
let (report_errors :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> unit)
  =
  fun fmods  ->
    let uu____145 =
      let uu____146 = FStar_Errors.report_all ()  in
      FStar_All.pipe_right uu____146 (fun a251  -> (Obj.magic ()) a251)  in
    let nerrs = FStar_Errors.get_err_count ()  in
    if nerrs > (Prims.parse_int "0")
    then
      let uu____152 = finished_message fmods nerrs  in
      FStar_All.exit (Prims.parse_int "1")
    else ()
  
let (codegen :
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env,FStar_Universal.delta_env)
    FStar_Pervasives_Native.tuple3 -> unit)
  =
  fun uu____166  ->
    match uu____166 with
    | (umods,env,delta1) ->
        let opt = FStar_Options.codegen ()  in
        if opt <> FStar_Pervasives_Native.None
        then
          let env1 = FStar_Universal.apply_delta_env env delta1  in
          let mllibs =
            let uu____195 =
              let uu____204 = FStar_Extraction_ML_UEnv.mkContext env1  in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____204
                umods
               in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____195  in
          let mllibs1 = FStar_List.flatten mllibs  in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) -> ".fs"
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) ->
                ".krml"
            | uu____227 -> failwith "Unrecognized option"  in
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
                 let uu____242 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1
                    in
                 FStar_List.flatten uu____242  in
               let bin = (FStar_Extraction_Kremlin.current_version, programs)
                  in
               (match programs with
                | (name,uu____253)::[] ->
                    let uu____262 =
                      FStar_Options.prepend_output_dir
                        (Prims.strcat name ext)
                       in
                    FStar_Util.save_value_to_file uu____262 bin
                | uu____263 ->
                    let uu____266 =
                      FStar_Options.prepend_output_dir "out.krml"  in
                    FStar_Util.save_value_to_file uu____266 bin)
           | uu____267 -> failwith "Unrecognized option")
        else ()
  
let (load_native_tactics : unit -> unit) =
  fun uu____275  ->
    let modules_to_load =
      let uu____279 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____279 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____291 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____291 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____309 = ml_module_name m  in Prims.strcat uu____309 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____316 = ml_module_name m  in Prims.strcat uu____316 ".cmxs"
         in
      let uu____317 = FStar_Options.find_file cmxs  in
      match uu____317 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____321 =
            let uu____324 = ml_file m  in FStar_Options.find_file uu____324
             in
          (match uu____321 with
           | FStar_Pervasives_Native.None  ->
               let uu____325 =
                 let uu____330 =
                   let uu____331 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____331
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____330)
                  in
               FStar_Errors.raise_err uu____325
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               let uu____334 =
                 let uu____335 =
                   let uu____338 = ml_module_name m  in [uu____338]  in
                 FStar_Tactics_Load.compile_modules dir uu____335  in
               let uu____339 = FStar_Options.find_file cmxs  in
               (match uu____339 with
                | FStar_Pervasives_Native.None  ->
                    let uu____342 =
                      let uu____347 =
                        FStar_Util.format1
                          "Failed to compile native tactic; compiled object %s not found"
                          cmxs
                         in
                      (FStar_Errors.Fatal_FailToCompileNativeTactic,
                        uu____347)
                       in
                    FStar_Errors.raise_err uu____342
                | FStar_Pervasives_Native.Some f -> f))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    let uu____356 =
      FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
        cmxs_files
       in
    FStar_Tactics_Load.load_tactics cmxs_files
  
let (init_warn_error : unit -> unit) =
  fun uu____363  ->
    let uu____364 = ()  in
    let s = FStar_Options.warn_error ()  in
    if s <> "" then FStar_Parser_ParseIt.parse_warn_error s else ()
  
let go : 'Auu____371 . 'Auu____371 -> unit =
  fun uu____376  ->
    let uu____377 = process_args ()  in
    match uu____377 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             let uu____390 = FStar_Options.display_usage ()  in
             FStar_All.exit (Prims.parse_int "0")
         | FStar_Getopt.Error msg ->
             let uu____392 = FStar_Util.print_string msg  in
             FStar_All.exit (Prims.parse_int "1")
         | FStar_Getopt.Success  ->
             let uu____393 = load_native_tactics ()  in
             let uu____394 = init_warn_error ()  in
             let uu____395 =
               let uu____396 = FStar_Options.dep ()  in
               uu____396 <> FStar_Pervasives_Native.None  in
             if uu____395
             then
               let uu____401 = FStar_Parser_Dep.collect filenames  in
               (match uu____401 with
                | (uu____408,deps) -> FStar_Parser_Dep.print deps)
             else
               (let uu____415 =
                  ((FStar_Options.use_extracted_interfaces ()) &&
                     (let uu____417 = FStar_Options.expose_interfaces ()  in
                      Prims.op_Negation uu____417))
                    &&
                    ((FStar_List.length filenames) > (Prims.parse_int "1"))
                   in
                if uu____415
                then
                  let uu____418 =
                    let uu____423 =
                      let uu____424 =
                        FStar_Util.string_of_int
                          (FStar_List.length filenames)
                         in
                      Prims.strcat
                        "Only one command line file is allowed if --use_extracted_interfaces is set, found %s"
                        uu____424
                       in
                    (FStar_Errors.Error_TooManyFiles, uu____423)  in
                  FStar_Errors.raise_error uu____418 FStar_Range.dummyRange
                else
                  (let uu____426 = FStar_Options.interactive ()  in
                   if uu____426
                   then
                     match filenames with
                     | [] ->
                         let uu____427 =
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             (FStar_Errors.Error_MissingFileName,
                               "--ide: Name of current file missing in command line invocation\n")
                            in
                         FStar_All.exit (Prims.parse_int "1")
                     | uu____428::uu____429::uu____430 ->
                         let uu____433 =
                           FStar_Errors.log_issue FStar_Range.dummyRange
                             (FStar_Errors.Error_TooManyFiles,
                               "--ide: Too many files in command line invocation\n")
                            in
                         FStar_All.exit (Prims.parse_int "1")
                     | filename::[] ->
                         let uu____435 = FStar_Options.legacy_interactive ()
                            in
                         (if uu____435
                          then
                            FStar_Interactive_Legacy.interactive_mode
                              filename
                          else
                            FStar_Interactive_Ide.interactive_mode filename)
                   else
                     (let uu____438 = FStar_Options.doc ()  in
                      if uu____438
                      then FStar_Fsdoc_Generator.generate filenames
                      else
                        (let uu____440 = FStar_Options.indent ()  in
                         if uu____440
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
                             (let uu____443 =
                                FStar_Dependencies.find_deps_if_needed
                                  filenames
                                 in
                              match uu____443 with
                              | (filenames1,dep_graph1) ->
                                  let uu____456 =
                                    FStar_Universal.batch_mode_tc filenames1
                                      dep_graph1
                                     in
                                  (match uu____456 with
                                   | (fmods,env,delta_env) ->
                                       let module_names_and_times =
                                         FStar_All.pipe_right fmods
                                           (FStar_List.map
                                              (fun uu____541  ->
                                                 match uu____541 with
                                                 | (x,t) ->
                                                     ((FStar_Universal.module_or_interface_name
                                                         x), t)))
                                          in
                                       let uu____560 =
                                         report_errors module_names_and_times
                                          in
                                       let uu____561 =
                                         let uu____562 =
                                           let uu____571 =
                                             FStar_All.pipe_right fmods
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst)
                                              in
                                           (uu____571, env, delta_env)  in
                                         codegen uu____562  in
                                       let uu____593 =
                                         report_errors module_names_and_times
                                          in
                                       finished_message
                                         module_names_and_times
                                         (Prims.parse_int "0")))
                           else
                             FStar_Errors.log_issue FStar_Range.dummyRange
                               (FStar_Errors.Error_MissingFileName,
                                 "no file provided\n"))))))
  
let (lazy_chooser :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
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
  
let main : 'Auu____609 . unit -> 'Auu____609 =
  fun uu____614  ->
    try
      let uu____625 =
        FStar_ST.op_Colon_Equals FStar_Syntax_Syntax.lazy_chooser
          (FStar_Pervasives_Native.Some lazy_chooser)
         in
      let uu____671 =
        FStar_ST.op_Colon_Equals FStar_Syntax_Util.tts_f
          (FStar_Pervasives_Native.Some FStar_Syntax_Print.term_to_string)
         in
      let uu____708 =
        FStar_ST.op_Colon_Equals
          FStar_TypeChecker_Normalize.unembed_binder_knot
          (FStar_Pervasives_Native.Some FStar_Reflection_Embeddings.e_binder)
         in
      let uu____742 = FStar_Util.record_time go  in
      match uu____742 with
      | (uu____747,time) ->
          let uu____749 =
            let uu____750 = FStar_Options.query_stats ()  in
            if uu____750
            then
              let uu____751 = FStar_Util.string_of_int time  in
              let uu____752 =
                let uu____753 = FStar_Getopt.cmdline ()  in
                FStar_String.concat " " uu____753  in
              FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____751 uu____752
            else ()  in
          let uu____757 = cleanup ()  in FStar_All.exit (Prims.parse_int "0")
    with
    | e ->
        let trace = FStar_Util.trace_of_exn e  in
        let uu____767 =
          let uu____768 =
            if FStar_Errors.handleable e then FStar_Errors.err_exn e else ()
             in
          let uu____770 = FStar_Options.trace_error ()  in
          if uu____770
          then
            let uu____771 = FStar_Util.message_of_exn e  in
            FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____771
              trace
          else
            if Prims.op_Negation (FStar_Errors.handleable e)
            then
              (let uu____773 = FStar_Util.message_of_exn e  in
               FStar_Util.print1_error
                 "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
                 uu____773)
            else ()
           in
        let uu____775 = cleanup ()  in
        let uu____776 = report_errors []  in
        FStar_All.exit (Prims.parse_int "1")
  