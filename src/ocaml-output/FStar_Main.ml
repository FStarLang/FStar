open Prims
let uu___229: Prims.unit = FStar_Version.dummy ()
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
              (fun uu____72  ->
                 match uu____72 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module" in
                     let uu____90 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____90
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____91 =
                            let uu____92 = FStar_Util.string_of_int time in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____92 in
                          print_to uu____91
                        else
                          (let uu____94 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name) in
                           print_to uu____94))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____97 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____97))
         else
           (let uu____99 =
              let uu____100 =
                FStar_Util.colorize_bold
                  "All verification conditions discharged successfully" in
              FStar_Util.format1 "%s\n" uu____100 in
            FStar_Util.print_string uu____99))
      else ()
let report_errors:
  ((Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2,Prims.int)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit
  =
  fun fmods  ->
    (let uu____126 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____126 FStar_Pervasives.ignore);
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
let codegen:
  (FStar_Syntax_Syntax.modul Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun uu____144  ->
    match uu____144 with
    | (umods,env) ->
        let opt = FStar_Options.codegen () in
        if opt <> FStar_Pervasives_Native.None
        then
          let mllibs =
            let uu____167 =
              let uu____176 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____176
                umods in
            FStar_All.pipe_left FStar_Pervasives_Native.snd uu____167 in
          let mllibs1 = FStar_List.flatten mllibs in
          let ext =
            match opt with
            | FStar_Pervasives_Native.Some "FSharp" -> ".fs"
            | FStar_Pervasives_Native.Some "OCaml" -> ".ml"
            | FStar_Pervasives_Native.Some "Kremlin" -> ".krml"
            | uu____199 -> failwith "Unrecognized option" in
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
                 let uu____211 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1 in
                 FStar_List.flatten uu____211 in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let uu____221 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____221 bin
           | uu____222 -> failwith "Unrecognized option")
        else ()
let go uu____232 =
  let uu____233 = process_args () in
  match uu____233 with
  | (res,filenames) ->
      (match res with
       | FStar_Getopt.Help  ->
           (FStar_Options.display_usage ();
            FStar_All.exit (Prims.parse_int "0"))
       | FStar_Getopt.Error msg -> FStar_Util.print_string msg
       | FStar_Getopt.Success  ->
           let uu____248 =
             let uu____249 = FStar_Options.dep () in
             uu____249 <> FStar_Pervasives_Native.None in
           if uu____248
           then
             let uu____254 =
               FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames in
             FStar_Parser_Dep.print uu____254
           else
             (let uu____282 = FStar_Options.interactive () in
              if uu____282
              then
                ((let uu____284 = FStar_Options.explicit_deps () in
                  if uu____284
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
                  (let uu____292 =
                     let uu____293 = FStar_Options.verify_module () in
                     uu____293 <> [] in
                   if uu____292
                   then
                     FStar_Util.print_warning
                       "Interactive mode; ignoring --verify_module"
                   else ());
                  (let uu____299 = FStar_Options.legacy_interactive () in
                   if uu____299
                   then FStar_Legacy_Interactive.interactive_mode filename
                   else FStar_Interactive.interactive_mode filename)))
              else
                (let uu____302 = FStar_Options.doc () in
                 if uu____302
                 then FStar_Fsdoc_Generator.generate filenames
                 else
                   (let uu____304 = FStar_Options.indent () in
                    if uu____304
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
                           let uu____308 = FStar_Options.verify_all () in
                           if uu____308
                           then
                             ((let uu____310 =
                                 let uu____311 =
                                   FStar_Options.verify_module () in
                                 uu____311 <> [] in
                               if uu____310
                               then
                                 (FStar_Util.print_error
                                    "--verify_module is incompatible with --verify_all";
                                  FStar_All.exit (Prims.parse_int "1"))
                               else ());
                              FStar_Parser_Dep.VerifyAll)
                           else
                             (let uu____319 =
                                let uu____320 =
                                  FStar_Options.verify_module () in
                                uu____320 <> [] in
                              if uu____319
                              then FStar_Parser_Dep.VerifyUserList
                              else FStar_Parser_Dep.VerifyFigureItOut) in
                         let filenames1 =
                           FStar_Dependencies.find_deps_if_needed verify_mode
                             filenames in
                         let uu____329 =
                           FStar_Universal.batch_mode_tc filenames1 in
                         match uu____329 with
                         | (fmods,dsenv,env) ->
                             let module_names_and_times =
                               FStar_All.pipe_right fmods
                                 (FStar_List.map
                                    (fun uu____396  ->
                                       match uu____396 with
                                       | (x,t) ->
                                           ((FStar_Universal.module_or_interface_name
                                               x), t))) in
                             (report_errors module_names_and_times;
                              (let uu____417 =
                                 let uu____424 =
                                   FStar_All.pipe_right fmods
                                     (FStar_List.map
                                        FStar_Pervasives_Native.fst) in
                                 (uu____424, env) in
                               codegen uu____417);
                              finished_message module_names_and_times
                                (Prims.parse_int "0")))
                      else FStar_Util.print_error "no file provided\n"))))
let main uu____448 =
  try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
  with
  | e ->
      let trace = FStar_Util.trace_of_exn e in
      (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
       (let uu____458 = FStar_Options.trace_error () in
        if uu____458
        then
          let uu____459 = FStar_Util.message_of_exn e in
          FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____459
            trace
        else
          if Prims.op_Negation (FStar_Errors.handleable e)
          then
            (let uu____461 = FStar_Util.message_of_exn e in
             FStar_Util.print1_error
               "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
               uu____461)
          else ());
       cleanup ();
       report_errors [];
       FStar_All.exit (Prims.parse_int "1"))