open Prims
let uu___618: Prims.unit = FStar_Version.dummy ()
let process_args:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun uu____9  -> FStar_Options.parse_cmd_line ()
let cleanup: Prims.unit -> Prims.unit =
  fun uu____18  -> FStar_Util.kill_all ()
let finished_message:
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int -> Prims.unit
  =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > (Prims.parse_int "0")
        then FStar_Util.print_error
        else FStar_Util.print_string in
      let uu____51 =
        let uu____52 = FStar_Options.silent () in Prims.op_Negation uu____52 in
      if uu____51
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____79  ->
                 match uu____79 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module" in
                     let uu____97 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____97
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____98 =
                            let uu____99 = FStar_Util.string_of_int time in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____99 in
                          print_to uu____98
                        else
                          (let uu____101 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name) in
                           print_to uu____101))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____104 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____104))
         else
           (let uu____106 =
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully" in
            FStar_Util.print1 "%s\n" uu____106))
      else ()
let report_errors:
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit
  =
  fun fmods  ->
    (let uu____132 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____132 FStar_Pervasives.ignore);
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
let codegen:
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____150  ->
    match uu____150 with
    | (umods,env) ->
        let opt = FStar_Options.codegen () in
        if opt <> FStar_Pervasives_Native.None
        then
          let mllibs =
            let uu____173 =
              let uu____182 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____182
                umods in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____173 in
          let mllibs1 = FStar_List.flatten mllibs in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some "FSharp" -> ".fs"
            | FStar_Pervasives_Native.Some "OCaml" -> ".ml"
            | FStar_Pervasives_Native.Some "tactics" -> ".ml"
            | FStar_Pervasives_Native.Some "Kremlin" -> ".krml"
            | uu____205 -> failwith "Unrecognized option" in
          (match opt with
           | FStar_Pervasives_Native.Some "FSharp" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some "OCaml" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some "tactics" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some "Kremlin" ->
               let programs =
                 let uu____220 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1 in
                 FStar_List.flatten uu____220 in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let uu____230 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____230 bin
           | uu____231 -> failwith "Unrecognized option")
        else ()
let gen_native_tactics:
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.string -> Prims.unit
  =
  fun uu____245  ->
    fun out_dir  ->
      match uu____245 with
      | (umods,env) ->
          (FStar_Options.set_option "codegen"
             (FStar_Options.String "tactics");
           (let mllibs =
              let uu____265 =
                let uu____274 = FStar_Extraction_ML_UEnv.mkContext env in
                FStar_Util.fold_map FStar_Extraction_ML_Modul.extract
                  uu____274 umods in
              FStar_All.pipe_left FStar_Pervasives_Native.snd uu____265 in
            let mllibs1 = FStar_List.flatten mllibs in
            FStar_List.iter
              (FStar_Extraction_ML_PrintML.print
                 (FStar_Pervasives_Native.Some out_dir) ".ml") mllibs1;
            (let user_tactics_modules1 = FStar_Universal.user_tactics_modules in
             let uu____302 = FStar_ST.op_Bang user_tactics_modules1 in
             FStar_Tactics_Load.compile_modules out_dir uu____302)))
let init_native_tactics: Prims.unit -> Prims.unit =
  fun uu____371  ->
    (let uu____373 = FStar_Options.load () in
     FStar_Tactics_Load.load_tactics uu____373);
    (let uu____376 = FStar_Options.use_native_tactics () in
     match uu____376 with
     | FStar_Pervasives_Native.Some dir ->
         (FStar_Util.print1 "Using native tactics from %s\n" dir;
          FStar_Tactics_Load.load_tactics_dir dir)
     | FStar_Pervasives_Native.None  -> ())
let go: 'Auu____383 . 'Auu____383 -> Prims.unit =
  fun uu____387  ->
    let uu____388 = process_args () in
    match uu____388 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             (FStar_Options.display_usage ();
              FStar_All.exit (Prims.parse_int "0"))
         | FStar_Getopt.Error msg ->
             (FStar_Util.print_string msg;
              FStar_All.exit (Prims.parse_int "1"))
         | FStar_Getopt.Success  ->
             (init_native_tactics ();
              (let uu____405 =
                 let uu____406 = FStar_Options.dep () in
                 uu____406 <> FStar_Pervasives_Native.None in
               if uu____405
               then
                 let uu____411 = FStar_Parser_Dep.collect filenames in
                 match uu____411 with
                 | (uu____418,deps) -> FStar_Parser_Dep.print deps
               else
                 (let uu____425 = FStar_Options.interactive () in
                  if uu____425
                  then
                    match filenames with
                    | [] ->
                        (FStar_Util.print_error
                           "--ide: Name of current file missing in command line invocation\n";
                         FStar_All.exit (Prims.parse_int "1"))
                    | uu____427::uu____428::uu____429 ->
                        (FStar_Util.print_error
                           "--ide: Too many files in command line invocation\n";
                         FStar_All.exit (Prims.parse_int "1"))
                    | filename::[] ->
                        let uu____434 = FStar_Options.legacy_interactive () in
                        (if uu____434
                         then
                           FStar_Interactive_Legacy.interactive_mode filename
                         else FStar_Interactive_Ide.interactive_mode filename)
                  else
                    (let uu____437 = FStar_Options.doc () in
                     if uu____437
                     then FStar_Fsdoc_Generator.generate filenames
                     else
                       (let uu____439 = FStar_Options.indent () in
                        if uu____439
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
                            (let uu____442 =
                               FStar_Dependencies.find_deps_if_needed
                                 filenames in
                             match uu____442 with
                             | (filenames1,dep_graph1) ->
                                 ((let uu____456 =
                                     FStar_Options.gen_native_tactics () in
                                   match uu____456 with
                                   | FStar_Pervasives_Native.Some dir ->
                                       (FStar_Util.print1
                                          "Generating native tactics in %s\n"
                                          dir;
                                        FStar_Options.set_option "lax"
                                          (FStar_Options.Bool true))
                                   | FStar_Pervasives_Native.None  -> ());
                                  (let uu____461 =
                                     FStar_Universal.batch_mode_tc filenames1
                                       dep_graph1 in
                                   match uu____461 with
                                   | (fmods,env) ->
                                       let module_names_and_times =
                                         FStar_All.pipe_right fmods
                                           (FStar_List.map
                                              (fun uu____528  ->
                                                 match uu____528 with
                                                 | (x,t) ->
                                                     ((FStar_Universal.module_or_interface_name
                                                         x), t))) in
                                       (report_errors module_names_and_times;
                                        (let uu____549 =
                                           let uu____556 =
                                             FStar_All.pipe_right fmods
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst) in
                                           (uu____556, env) in
                                         codegen uu____549);
                                        (let uu____574 =
                                           FStar_Options.gen_native_tactics
                                             () in
                                         match uu____574 with
                                         | FStar_Pervasives_Native.Some dir
                                             ->
                                             let uu____578 =
                                               let uu____585 =
                                                 FStar_All.pipe_right fmods
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst) in
                                               (uu____585, env) in
                                             gen_native_tactics uu____578 dir
                                         | FStar_Pervasives_Native.None  ->
                                             ());
                                        finished_message
                                          module_names_and_times
                                          (Prims.parse_int "0")))))
                          else FStar_Util.print_error "no file provided\n"))))))
let main: 'Auu____605 . Prims.unit -> 'Auu____605 =
  fun uu____609  ->
    try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
    with
    | e ->
        let trace = FStar_Util.trace_of_exn e in
        (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
         (let uu____628 = FStar_Options.trace_error () in
          if uu____628
          then
            let uu____629 = FStar_Util.message_of_exn e in
            FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____629
              trace
          else
            if Prims.op_Negation (FStar_Errors.handleable e)
            then
              (let uu____631 = FStar_Util.message_of_exn e in
               FStar_Util.print1_error
                 "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
                 uu____631)
            else ());
         cleanup ();
         report_errors [];
         FStar_All.exit (Prims.parse_int "1"))