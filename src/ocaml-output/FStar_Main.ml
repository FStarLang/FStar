open Prims
let uu___302: Prims.unit = FStar_Version.dummy ()
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
              FStar_Util.colorize_bold
                "All verification conditions discharged successfully" in
            FStar_Util.print1 "%s\n" uu____110))
      else ()
let report_errors:
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit
  =
  fun fmods  ->
    (let uu____137 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____137 FStar_Pervasives.ignore);
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
let codegen:
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____156  ->
    match uu____156 with
    | (umods,env) ->
        let opt = FStar_Options.codegen () in
        if opt <> FStar_Pervasives_Native.None
        then
          let mllibs =
            let uu____179 =
              let uu____188 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____188
                umods in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____179 in
          let mllibs1 = FStar_List.flatten mllibs in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some "FSharp" -> ".fs"
            | FStar_Pervasives_Native.Some "OCaml" -> ".ml"
            | FStar_Pervasives_Native.Some "Kremlin" -> ".krml"
            | uu____211 -> failwith "Unrecognized option" in
          (match opt with
           | FStar_Pervasives_Native.Some "FSharp" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some "OCaml" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | FStar_Pervasives_Native.Some "Kremlin" ->
               let programs =
                 let uu____223 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1 in
                 FStar_List.flatten uu____223 in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let uu____233 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____233 bin
           | uu____234 -> failwith "Unrecognized option")
        else ()
let gen_native_tactics:
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.string -> Prims.unit
  =
  fun uu____250  ->
    fun out_dir  ->
      match uu____250 with
      | (umods,env) ->
          (FStar_Options.set_option "codegen" (FStar_Options.String "OCaml");
           (let mllibs =
              let uu____270 =
                let uu____279 = FStar_Extraction_ML_UEnv.mkContext env in
                FStar_Util.fold_map FStar_Extraction_ML_Modul.extract
                  uu____279 umods in
              FStar_All.pipe_left FStar_Pervasives_Native.snd uu____270 in
            let mllibs1 = FStar_List.flatten mllibs in
            FStar_List.iter
              (FStar_Extraction_ML_PrintML.print
                 (FStar_Pervasives_Native.Some out_dir) ".ml") mllibs1;
            (let user_tactics_modules1 = FStar_Universal.user_tactics_modules in
             let uu____307 = FStar_ST.op_Bang user_tactics_modules1 in
             FStar_Tactics_Load.compile_modules out_dir uu____307)))
let init_native_tactics: Prims.unit -> Prims.unit =
  fun uu____377  ->
    (let uu____379 = FStar_Options.load () in
     FStar_Tactics_Load.load_tactics uu____379);
    (let uu____382 = FStar_Options.use_native_tactics () in
     match uu____382 with
     | FStar_Pervasives_Native.Some dir ->
         (FStar_Util.print1 "Using native tactics from %s\n" dir;
          FStar_Tactics_Load.load_tactics_dir dir)
     | FStar_Pervasives_Native.None  -> ())
let go: 'Auu____391 . 'Auu____391 -> Prims.unit =
  fun uu____395  ->
    let uu____396 = process_args () in
    match uu____396 with
    | (res,filenames) ->
        (match res with
         | FStar_Getopt.Help  ->
             (FStar_Options.display_usage ();
              FStar_All.exit (Prims.parse_int "0"))
         | FStar_Getopt.Error msg -> FStar_Util.print_string msg
         | FStar_Getopt.Success  ->
             (init_native_tactics ();
              (let uu____412 =
                 let uu____413 = FStar_Options.dep () in
                 uu____413 <> FStar_Pervasives_Native.None in
               if uu____412
               then
                 let uu____418 =
                   FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll
                     filenames in
                 FStar_Parser_Dep.print uu____418
               else
                 (let uu____446 = FStar_Options.interactive () in
                  if uu____446
                  then
                    match filenames with
                    | [] ->
                        (FStar_Util.print_error
                           "--ide: Name of current file missing in command line invocation\n";
                         FStar_All.exit (Prims.parse_int "1"))
                    | uu____448::uu____449::uu____450 ->
                        (FStar_Util.print_error
                           "--ide: Too many files in command line invocation\n";
                         FStar_All.exit (Prims.parse_int "1"))
                    | filename::[] ->
                        ((let uu____456 = FStar_Options.explicit_deps () in
                          if uu____456
                          then
                            (FStar_Util.print_error
                               "--ide: --explicit_deps not supported in interactive mode\n";
                             FStar_All.exit (Prims.parse_int "1"))
                          else ());
                         (let uu____459 = FStar_Options.legacy_interactive () in
                          if uu____459
                          then
                            FStar_Interactive_Legacy.interactive_mode
                              filename
                          else
                            FStar_Interactive_Ide.interactive_mode filename))
                  else
                    (let uu____462 = FStar_Options.doc () in
                     if uu____462
                     then FStar_Fsdoc_Generator.generate filenames
                     else
                       (let uu____464 = FStar_Options.indent () in
                        if uu____464
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
                               let uu____468 = FStar_Options.verify_all () in
                               if uu____468
                               then
                                 ((let uu____470 =
                                     let uu____471 =
                                       FStar_Options.verify_module () in
                                     uu____471 <> [] in
                                   if uu____470
                                   then
                                     (FStar_Util.print_error
                                        "--verify_module is incompatible with --verify_all\n";
                                      FStar_All.exit (Prims.parse_int "1"))
                                   else ());
                                  FStar_Parser_Dep.VerifyAll)
                               else
                                 (let uu____479 =
                                    let uu____480 =
                                      FStar_Options.verify_module () in
                                    uu____480 <> [] in
                                  if uu____479
                                  then FStar_Parser_Dep.VerifyUserList
                                  else FStar_Parser_Dep.VerifyFigureItOut) in
                             let filenames1 =
                               FStar_Dependencies.find_deps_if_needed
                                 verify_mode filenames in
                             (let uu____490 =
                                FStar_Options.gen_native_tactics () in
                              match uu____490 with
                              | FStar_Pervasives_Native.Some dir ->
                                  (FStar_Util.print1
                                     "Generating native tactics in %s\n" dir;
                                   FStar_Options.set_option "lax"
                                     (FStar_Options.Bool true))
                              | FStar_Pervasives_Native.None  -> ());
                             (let uu____495 =
                                FStar_Universal.batch_mode_tc filenames1 in
                              match uu____495 with
                              | (fmods,env) ->
                                  let module_names_and_times =
                                    FStar_All.pipe_right fmods
                                      (FStar_List.map
                                         (fun uu____562  ->
                                            match uu____562 with
                                            | (x,t) ->
                                                ((FStar_Universal.module_or_interface_name
                                                    x), t))) in
                                  (report_errors module_names_and_times;
                                   (let uu____583 =
                                      let uu____590 =
                                        FStar_All.pipe_right fmods
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      (uu____590, env) in
                                    codegen uu____583);
                                   (let uu____608 =
                                      FStar_Options.gen_native_tactics () in
                                    match uu____608 with
                                    | FStar_Pervasives_Native.Some dir ->
                                        let uu____612 =
                                          let uu____619 =
                                            FStar_All.pipe_right fmods
                                              (FStar_List.map
                                                 FStar_Pervasives_Native.fst) in
                                          (uu____619, env) in
                                        gen_native_tactics uu____612 dir
                                    | FStar_Pervasives_Native.None  -> ());
                                   finished_message module_names_and_times
                                     (Prims.parse_int "0"))))
                          else FStar_Util.print_error "no file provided\n"))))))
let main: 'Auu____641 . Prims.unit -> 'Auu____641 =
  fun uu____645  ->
    try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
    with
    | e ->
        let trace = FStar_Util.trace_of_exn e in
        (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
         (let uu____664 = FStar_Options.trace_error () in
          if uu____664
          then
            let uu____665 = FStar_Util.message_of_exn e in
            FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____665
              trace
          else
            if Prims.op_Negation (FStar_Errors.handleable e)
            then
              (let uu____667 = FStar_Util.message_of_exn e in
               FStar_Util.print1_error
                 "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
                 uu____667)
            else ());
         cleanup ();
         report_errors [];
         FStar_All.exit (Prims.parse_int "1"))