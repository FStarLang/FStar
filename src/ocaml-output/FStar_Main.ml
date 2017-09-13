open Prims
let uu___279: Prims.unit = FStar_Version.dummy ()
let process_args:
  Prims.unit ->
    (FStar_Getopt.parse_cmdline_res,Prims.string Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun uu____10  -> FStar_Options.parse_cmd_line ()
let cleanup: Prims.unit -> Prims.unit =
  fun uu____20  -> FStar_Util.kill_all ()
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
      let uu____55 =
        let uu____56 = FStar_Options.silent () in Prims.op_Negation uu____56 in
      if uu____55
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____83  ->
                 match uu____83 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module" in
                     let uu____101 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____101
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____102 =
                            let uu____103 = FStar_Util.string_of_int time in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____103 in
                          print_to uu____102
                        else
                          (let uu____105 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name) in
                           print_to uu____105))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____108 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____108))
         else
           (let uu____110 =
              let uu____111 =
                FStar_Util.colorize_bold
                  "All verification conditions discharged successfully" in
              FStar_Util.format1 "%s\n" uu____111 in
            FStar_Util.print_string uu____110))
      else ()
let report_errors:
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit
  =
  fun fmods  ->
    (let uu____138 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____138 FStar_Pervasives.ignore);
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
let codegen:
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____157  ->
    match uu____157 with
    | (umods,env) ->
        let opt = FStar_Options.codegen () in
        if opt <> FStar_Pervasives_Native.None
        then
          let mllibs =
            let uu____180 =
              let uu____189 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____189
                umods in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____180 in
          let mllibs1 = FStar_List.flatten mllibs in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some "FSharp" -> ".fs"
            | FStar_Pervasives_Native.Some "OCaml" -> ".ml"
            | FStar_Pervasives_Native.Some "Kremlin" -> ".krml"
            | FStar_Pervasives_Native.Some "JavaScript" -> ".flow"
            | uu____212 -> failwith "Unrecognized option" in
          (match opt with
           | FStar_Pervasives_Native.Some "FSharp" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some "OCaml" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some "JavaScript" ->
               let newDocs =
                 FStar_List.collect
                   FStar_Extraction_JavaScript_Translate.translate mllibs1 in
               FStar_List.iter
                 (fun uu____233  ->
                    match uu____233 with
                    | (n1,d) ->
                        let res =
                          FStar_Extraction_JavaScript_PrintAst.pretty_print d in
                        let uu____241 =
                          FStar_Options.prepend_output_dir
                            (Prims.strcat n1 ext) in
                        FStar_Util.write_file uu____241
                          (FStar_Format.pretty (Prims.parse_int "120") res))
                 newDocs
           | FStar_Pervasives_Native.Some "Kremlin" ->
               let programs =
                 let uu____245 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1 in
                 FStar_List.flatten uu____245 in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let uu____255 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____255 bin
           | uu____256 -> failwith "Unrecognized option")
        else ()
let gen_native_tactics:
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.string -> Prims.unit
  =
  fun uu____272  ->
    fun out_dir  ->
      match uu____272 with
      | (umods,env) ->
          (FStar_Options.set_option "codegen" (FStar_Options.String "OCaml");
           (let mllibs =
              let uu____292 =
                let uu____301 = FStar_Extraction_ML_UEnv.mkContext env in
                FStar_Util.fold_map FStar_Extraction_ML_Modul.extract
                  uu____301 umods in
              FStar_All.pipe_left FStar_Pervasives_Native.snd uu____292 in
            let mllibs1 = FStar_List.flatten mllibs in
            FStar_List.iter
              (FStar_Extraction_ML_PrintML.print
                 (FStar_Pervasives_Native.Some out_dir) ".ml") mllibs1;
            (let user_tactics_modules1 = FStar_Universal.user_tactics_modules in
             let uu____329 = FStar_ST.op_Bang user_tactics_modules1 in
             FStar_Tactics_Load.compile_modules out_dir uu____329)))
let go: 'Auu____368 . 'Auu____368 -> Prims.unit =
  fun uu____372  ->
    let uu____373 = process_args () in
    match uu____373 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             (FStar_Options.display_usage ();
              FStar_All.exit (Prims.parse_int "0"))
         | FStar_Getopt.Error msg -> FStar_Util.print_string msg
         | FStar_Getopt.Success  ->
             let uu____388 =
               let uu____389 = FStar_Options.dep () in
               uu____389 <> FStar_Pervasives_Native.None in
             if uu____388
             then
               let uu____394 =
                 FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll
                   filenames in
               FStar_Parser_Dep.print uu____394
             else
               (let uu____422 = FStar_Options.interactive () in
                if uu____422
                then
                  ((let uu____424 = FStar_Options.explicit_deps () in
                    if uu____424
                    then
                      (FStar_Util.print_error
                         "--explicit_deps incompatible with --in\n";
                       FStar_All.exit (Prims.parse_int "1"))
                    else ());
                   if (FStar_List.length filenames) <> (Prims.parse_int "1")
                   then
                     (FStar_Util.print_error
                        "fstar-mode.el should pass the current filename to F*\n";
                      FStar_All.exit (Prims.parse_int "1"))
                   else ();
                   (let filename = FStar_List.hd filenames in
                    (let uu____432 =
                       let uu____433 = FStar_Options.verify_module () in
                       uu____433 <> [] in
                     if uu____432
                     then
                       FStar_Util.print_warning
                         "Interactive mode; ignoring --verify_module"
                     else ());
                    (let uu____439 = FStar_Options.legacy_interactive () in
                     if uu____439
                     then FStar_Legacy_Interactive.interactive_mode filename
                     else FStar_Interactive.interactive_mode filename)))
                else
                  (let uu____442 = FStar_Options.doc () in
                   if uu____442
                   then FStar_Fsdoc_Generator.generate filenames
                   else
                     (let uu____444 = FStar_Options.indent () in
                      if uu____444
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
                          (let verify_mode =
                             let uu____448 = FStar_Options.verify_all () in
                             if uu____448
                             then
                               ((let uu____450 =
                                   let uu____451 =
                                     FStar_Options.verify_module () in
                                   uu____451 <> [] in
                                 if uu____450
                                 then
                                   (FStar_Util.print_error
                                      "--verify_module is incompatible with --verify_all";
                                    FStar_All.exit (Prims.parse_int "1"))
                                 else ());
                                FStar_Parser_Dep.VerifyAll)
                             else
                               (let uu____459 =
                                  let uu____460 =
                                    FStar_Options.verify_module () in
                                  uu____460 <> [] in
                                if uu____459
                                then FStar_Parser_Dep.VerifyUserList
                                else FStar_Parser_Dep.VerifyFigureItOut) in
                           let filenames1 =
                             FStar_Dependencies.find_deps_if_needed
                               verify_mode filenames in
                           (let uu____470 =
                              FStar_Options.gen_native_tactics () in
                            match uu____470 with
                            | FStar_Pervasives_Native.Some dir ->
                                (FStar_Util.print1
                                   "Generating native tactics in %s\n" dir;
                                 FStar_Options.set_option "lax"
                                   (FStar_Options.Bool true))
                            | FStar_Pervasives_Native.None  -> ());
                           (let uu____476 =
                              FStar_Options.use_native_tactics () in
                            match uu____476 with
                            | FStar_Pervasives_Native.Some dir ->
                                (FStar_Util.print1
                                   "Using native tactics from %s\n" dir;
                                 FStar_Tactics_Load.load_tactics_dir dir)
                            | FStar_Pervasives_Native.None  -> ());
                           (let uu____482 = FStar_Options.load () in
                            FStar_Tactics_Load.load_tactics uu____482);
                           (let uu____485 =
                              FStar_Universal.batch_mode_tc filenames1 in
                            match uu____485 with
                            | (fmods,dsenv,env) ->
                                let module_names_and_times =
                                  FStar_All.pipe_right fmods
                                    (FStar_List.map
                                       (fun uu____555  ->
                                          match uu____555 with
                                          | (x,t) ->
                                              ((FStar_Universal.module_or_interface_name
                                                  x), t))) in
                                (report_errors module_names_and_times;
                                 (let uu____576 =
                                    let uu____583 =
                                      FStar_All.pipe_right fmods
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    (uu____583, env) in
                                  codegen uu____576);
                                 (let uu____601 =
                                    FStar_Options.gen_native_tactics () in
                                  match uu____601 with
                                  | FStar_Pervasives_Native.Some dir ->
                                      let uu____605 =
                                        let uu____612 =
                                          FStar_All.pipe_right fmods
                                            (FStar_List.map
                                               FStar_Pervasives_Native.fst) in
                                        (uu____612, env) in
                                      gen_native_tactics uu____605 dir
                                  | FStar_Pervasives_Native.None  -> ());
                                 finished_message module_names_and_times
                                   (Prims.parse_int "0"))))
                        else FStar_Util.print_error "no file provided\n"))))
let main: 'Auu____634 . Prims.unit -> 'Auu____634 =
  fun uu____638  ->
    try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
    with
    | e ->
        let trace = FStar_Util.trace_of_exn e in
        (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
         (let uu____657 = FStar_Options.trace_error () in
          if uu____657
          then
            let uu____658 = FStar_Util.message_of_exn e in
            FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____658
              trace
          else
            if Prims.op_Negation (FStar_Errors.handleable e)
            then
              (let uu____660 = FStar_Util.message_of_exn e in
               FStar_Util.print1_error
                 "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
                 uu____660)
            else ());
         cleanup ();
         report_errors [];
         FStar_All.exit (Prims.parse_int "1"))