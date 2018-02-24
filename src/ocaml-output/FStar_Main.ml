open Prims
let (uu___75 : Prims.unit) = FStar_Version.dummy () 
let (process_args :
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun uu____9  -> FStar_Options.parse_cmd_line () 
let (cleanup : Prims.unit -> Prims.unit) =
  fun uu____18  -> FStar_Util.kill_all () 
let (finished_message :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int -> Prims.unit)
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
                            let uu____99 = FStar_Util.string_of_int time  in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____99
                             in
                          print_to uu____98
                        else
                          (let uu____101 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name)
                              in
                           print_to uu____101))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____104 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____104))
         else
           (let uu____106 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully"
               in
            FStar_Util.print1 "%s\n" uu____106))
      else ()
  
let (report_errors :
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit)
  =
  fun fmods  ->
    (let uu____132 = FStar_Errors.report_all ()  in
     FStar_All.pipe_right uu____132 FStar_Pervasives.ignore);
    (let nerrs = FStar_Errors.get_err_count ()  in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
  
let (codegen :
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.unit)
  =
  fun uu____150  ->
    match uu____150 with
    | (umods,env) ->
        let opt = FStar_Options.codegen ()  in
        if opt <> FStar_Pervasives_Native.None
        then
          let mllibs =
            let uu____173 =
              let uu____182 = FStar_Extraction_ML_UEnv.mkContext env  in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____182
                umods
               in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____173  in
          let mllibs1 = FStar_List.flatten mllibs  in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) -> ".fs"
            | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) -> ".ml"
            | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) ->
                ".krml"
            | uu____205 -> failwith "Unrecognized option"  in
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
                 let uu____220 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1
                    in
                 FStar_List.flatten uu____220  in
               let bin = (FStar_Extraction_Kremlin.current_version, programs)
                  in
               (match programs with
                | (name,uu____231)::[] ->
                    let uu____240 =
                      FStar_Options.prepend_output_dir
                        (Prims.strcat name ext)
                       in
                    FStar_Util.save_value_to_file uu____240 bin
                | uu____241 ->
                    let uu____244 =
                      FStar_Options.prepend_output_dir "out.krml"  in
                    FStar_Util.save_value_to_file uu____244 bin)
           | uu____245 -> failwith "Unrecognized option")
        else ()
  
let (load_native_tactics : Prims.unit -> Prims.unit) =
  fun uu____251  ->
    let modules_to_load =
      let uu____255 = FStar_Options.load ()  in
      FStar_All.pipe_right uu____255 (FStar_List.map FStar_Ident.lid_of_str)
       in
    let ml_module_name m =
      let uu____266 = FStar_Extraction_ML_Util.mlpath_of_lid m  in
      FStar_All.pipe_right uu____266 FStar_Extraction_ML_Util.flatten_mlpath
       in
    let ml_file m =
      let uu____283 = ml_module_name m  in Prims.strcat uu____283 ".ml"  in
    let cmxs_file m =
      let cmxs =
        let uu____289 = ml_module_name m  in Prims.strcat uu____289 ".cmxs"
         in
      let uu____290 = FStar_Options.find_file cmxs  in
      match uu____290 with
      | FStar_Pervasives_Native.Some f -> f
      | FStar_Pervasives_Native.None  ->
          let uu____294 =
            let uu____297 = ml_file m  in FStar_Options.find_file uu____297
             in
          (match uu____294 with
           | FStar_Pervasives_Native.None  ->
               let uu____298 =
                 let uu____303 =
                   let uu____304 = ml_file m  in
                   FStar_Util.format1
                     "Failed to compile native tactic; extracted module %s not found"
                     uu____304
                    in
                 (FStar_Errors.Fatal_FailToCompileNativeTactic, uu____303)
                  in
               FStar_Errors.raise_err uu____298
           | FStar_Pervasives_Native.Some ml ->
               let dir = FStar_Util.dirname ml  in
               ((let uu____308 =
                   let uu____311 = ml_module_name m  in [uu____311]  in
                 FStar_Tactics_Load.compile_modules dir uu____308);
                (let uu____312 = FStar_Options.find_file cmxs  in
                 FStar_Util.must uu____312)))
       in
    let cmxs_files =
      FStar_All.pipe_right modules_to_load (FStar_List.map cmxs_file)  in
    FStar_List.iter (fun x  -> FStar_Util.print1 "cmxs file: %s\n" x)
      cmxs_files;
    FStar_Tactics_Load.load_tactics cmxs_files
  
let (init_warn_error : Prims.unit -> Prims.unit) =
  fun uu____327  ->
    let s = FStar_Options.warn_error ()  in
    if s <> "" then FStar_Parser_ParseIt.parse_warn_error s else ()
  
let go : 'Auu____333 . 'Auu____333 -> Prims.unit =
  fun uu____337  ->
    let uu____338 = process_args ()  in
    match uu____338 with
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
              (let uu____356 =
                 let uu____357 = FStar_Options.dep ()  in
                 uu____357 <> FStar_Pervasives_Native.None  in
               if uu____356
               then
                 let uu____362 = FStar_Parser_Dep.collect filenames  in
                 match uu____362 with
                 | (uu____369,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____376 =
                    ((FStar_Options.use_extracted_interfaces ()) ||
                       (FStar_Options.check_interface ()))
                      &&
                      ((FStar_List.length filenames) > (Prims.parse_int "1"))
                     in
                  if uu____376
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_TooManyFiles,
                        "Only one command line file is allowed if either --check_interface or --use_extracted_interfaces is set")
                      FStar_Range.dummyRange
                  else
                    (let uu____378 = FStar_Options.interactive ()  in
                     if uu____378
                     then
                       match filenames with
                       | [] ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_MissingFileName,
                                "--ide: Name of current file missing in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | uu____380::uu____381::uu____382 ->
                           (FStar_Errors.log_issue FStar_Range.dummyRange
                              (FStar_Errors.Error_TooManyFiles,
                                "--ide: Too many files in command line invocation\n");
                            FStar_All.exit (Prims.parse_int "1"))
                       | filename::[] ->
                           let uu____387 = FStar_Options.check_interface ()
                              in
                           (if uu____387
                            then
                              (FStar_Errors.log_issue FStar_Range.dummyRange
                                 (FStar_Errors.Fatal_OptionsNotCompatible,
                                   "Only one command line file is allowed if either --check_interface or --use_extracted_interfaces is set\n");
                               FStar_All.exit (Prims.parse_int "1"))
                            else
                              (let uu____390 =
                                 FStar_Options.legacy_interactive ()  in
                               if uu____390
                               then
                                 FStar_Interactive_Legacy.interactive_mode
                                   filename
                               else
                                 FStar_Interactive_Ide.interactive_mode
                                   filename))
                     else
                       (let uu____393 = FStar_Options.doc ()  in
                        if uu____393
                        then FStar_Fsdoc_Generator.generate filenames
                        else
                          (let uu____395 = FStar_Options.indent ()  in
                           if uu____395
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
                               (let uu____398 =
                                  FStar_Dependencies.find_deps_if_needed
                                    filenames
                                   in
                                match uu____398 with
                                | (filenames1,dep_graph1) ->
                                    let uu____411 =
                                      FStar_Universal.batch_mode_tc
                                        filenames1 dep_graph1
                                       in
                                    (match uu____411 with
                                     | (fmods,env) ->
                                         let module_names_and_times =
                                           FStar_All.pipe_right fmods
                                             (FStar_List.map
                                                (fun uu____478  ->
                                                   match uu____478 with
                                                   | (x,t) ->
                                                       ((FStar_Universal.module_or_interface_name
                                                           x), t)))
                                            in
                                         (report_errors
                                            module_names_and_times;
                                          (let uu____499 =
                                             let uu____506 =
                                               FStar_All.pipe_right fmods
                                                 (FStar_List.map
                                                    FStar_Pervasives_Native.fst)
                                                in
                                             (uu____506, env)  in
                                           codegen uu____499);
                                          report_errors
                                            module_names_and_times;
                                          finished_message
                                            module_names_and_times
                                            (Prims.parse_int "0"))))
                             else
                               FStar_Errors.log_issue FStar_Range.dummyRange
                                 (FStar_Errors.Error_MissingFileName,
                                   "no file provided\n"))))))))
  
let main : 'Auu____527 . Prims.unit -> 'Auu____527 =
  fun uu____531  ->
    try
      let uu____539 = FStar_Util.record_time go  in
      match uu____539 with
      | (uu____544,time) ->
          ((let uu____547 = FStar_Options.query_stats ()  in
            if uu____547
            then
              let uu____548 = FStar_Util.string_of_int time  in
              let uu____549 =
                let uu____550 = FStar_Getopt.cmdline ()  in
                FStar_String.concat " " uu____550  in
              FStar_Util.print2 "TOTAL TIME %s ms: %s\n" uu____548 uu____549
            else ());
           cleanup ();
           FStar_All.exit (Prims.parse_int "0"))
    with
    | e ->
        let trace = FStar_Util.trace_of_exn e  in
        (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
         (let uu____567 = FStar_Options.trace_error ()  in
          if uu____567
          then
            let uu____568 = FStar_Util.message_of_exn e  in
            FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____568
              trace
          else
            if Prims.op_Negation (FStar_Errors.handleable e)
            then
              (let uu____570 = FStar_Util.message_of_exn e  in
               FStar_Util.print1_error
                 "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
                 uu____570)
            else ());
         cleanup ();
         report_errors [];
         FStar_All.exit (Prims.parse_int "1"))
  