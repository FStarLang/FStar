open Prims
let uu___271: Prims.unit = FStar_Version.dummy ()
let process_args:
  Prims.unit -> (FStar_Getopt.parse_cmdline_res* Prims.string Prims.list) =
  fun uu____6  -> FStar_Options.parse_cmd_line ()
let cleanup: Prims.unit -> Prims.unit =
  fun uu____12  -> FStar_Util.kill_all ()
let finished_message:
  ((Prims.bool* FStar_Ident.lident)* Prims.int) Prims.list ->
    Prims.int -> Prims.unit
  =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > (Prims.parse_int "0")
        then FStar_Util.print_error
        else FStar_Util.print_string in
      let uu____35 =
        let uu____36 = FStar_Options.silent () in Prims.op_Negation uu____36 in
      if uu____35
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____47  ->
                 match uu____47 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module" in
                     let uu____59 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____59
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____60 =
                            let uu____61 = FStar_Util.string_of_int time in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____61 in
                          print_to uu____60
                        else
                          (let uu____63 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name) in
                           print_to uu____63))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____66 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____66))
         else
           (let uu____68 =
              let uu____69 =
                FStar_Util.colorize_bold
                  "All verification conditions discharged successfully" in
              FStar_Util.format1 "%s\n" uu____69 in
            FStar_Util.print_string uu____68))
      else ()
let report_errors:
  ((Prims.bool* FStar_Ident.lident)* Prims.int) Prims.list -> Prims.unit =
  fun fmods  ->
    (let uu____85 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____85 FStar_Pervasives.ignore);
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
let codegen:
  (FStar_Syntax_Syntax.modul Prims.list* FStar_TypeChecker_Env.env) ->
    Prims.unit
  =
  fun uu____97  ->
    match uu____97 with
    | (umods,env) ->
        let opt = FStar_Options.codegen () in
        if opt <> None
        then
          let mllibs =
            let uu____111 =
              let uu____116 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____116
                umods in
            FStar_All.pipe_left FStar_Pervasives.snd uu____111 in
          let mllibs1 = FStar_List.flatten mllibs in
          let ext =
            match opt with
            | Some "FSharp" -> ".fs"
            | Some "OCaml" -> ".ml"
            | Some "Kremlin" -> ".krml"
            | Some "JavaScript" -> ".flow"
            | uu____129 -> failwith "Unrecognized option" in
          (match opt with
           | Some "FSharp" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | Some "OCaml" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | Some "JavaScript" ->
               let newDocs =
                 FStar_List.collect
                   FStar_Extraction_JavaScript_Translate.translate mllibs1 in
               FStar_List.iter
                 (fun uu____139  ->
                    match uu____139 with
                    | (n1,d) ->
                        let res =
                          FStar_Extraction_JavaScript_PrintAst.pretty_print d in
                        let uu____145 =
                          FStar_Options.prepend_output_dir
                            (Prims.strcat n1 ext) in
                        FStar_Util.write_file uu____145
                          (FStar_Format.pretty (Prims.parse_int "120") res))
                 newDocs
           | Some "Kremlin" ->
               let programs =
                 let uu____148 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1 in
                 FStar_List.flatten uu____148 in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let uu____154 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____154 bin
           | uu____155 -> failwith "Unrecognized option")
        else ()
let go uu____164 =
  let uu____165 = process_args () in
  match uu____165 with
  | (res,filenames) ->
      (match res with
       | FStar_Getopt.Help  ->
           (FStar_Options.display_usage ();
            FStar_All.exit (Prims.parse_int "0"))
       | FStar_Getopt.Error msg -> FStar_Util.print_string msg
       | FStar_Getopt.Success  ->
           let uu____175 =
             let uu____176 = FStar_Options.dep () in uu____176 <> None in
           if uu____175
           then
             let uu____179 =
               FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames in
             FStar_Parser_Dep.print uu____179
           else
             (let uu____194 = FStar_Options.interactive () in
              if uu____194
              then
                ((let uu____196 = FStar_Options.explicit_deps () in
                  if uu____196
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
                  (let uu____206 =
                     let uu____207 = FStar_Options.verify_module () in
                     uu____207 <> [] in
                   if uu____206
                   then
                     FStar_Util.print_warning
                       "Interactive mode; ignoring --verify_module"
                   else ());
                  (let uu____211 = FStar_Options.legacy_interactive () in
                   if uu____211
                   then FStar_Legacy_Interactive.interactive_mode filename
                   else FStar_Interactive.interactive_mode filename)))
              else
                (let uu____214 = FStar_Options.doc () in
                 if uu____214
                 then FStar_Fsdoc_Generator.generate filenames
                 else
                   (let uu____216 = FStar_Options.indent () in
                    if uu____216
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
                           let uu____223 = FStar_Options.verify_all () in
                           if uu____223
                           then
                             ((let uu____225 =
                                 let uu____226 =
                                   FStar_Options.verify_module () in
                                 uu____226 <> [] in
                               if uu____225
                               then
                                 (FStar_Util.print_error
                                    "--verify_module is incompatible with --verify_all";
                                  FStar_All.exit (Prims.parse_int "1"))
                               else ());
                              FStar_Parser_Dep.VerifyAll)
                           else
                             (let uu____232 =
                                let uu____233 =
                                  FStar_Options.verify_module () in
                                uu____233 <> [] in
                              if uu____232
                              then FStar_Parser_Dep.VerifyUserList
                              else FStar_Parser_Dep.VerifyFigureItOut) in
                         let filenames1 =
                           FStar_Dependencies.find_deps_if_needed verify_mode
                             filenames in
                         let uu____239 =
                           FStar_Universal.batch_mode_tc filenames1 in
                         match uu____239 with
                         | (fmods,dsenv,env) ->
                             let module_names_and_times =
                               FStar_All.pipe_right fmods
                                 (FStar_List.map
                                    (fun uu____275  ->
                                       match uu____275 with
                                       | (x,t) ->
                                           ((FStar_Universal.module_or_interface_name
                                               x), t))) in
                             (report_errors module_names_and_times;
                              (let uu____288 =
                                 let uu____292 =
                                   FStar_All.pipe_right fmods
                                     (FStar_List.map FStar_Pervasives.fst) in
                                 (uu____292, env) in
                               codegen uu____288);
                              finished_message module_names_and_times
                                (Prims.parse_int "0")))
                      else FStar_Util.print_error "no file provided\n"))))
let main uu____308 =
  try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
  with
  | e ->
      let trace = FStar_Util.trace_of_exn e in
      (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
       (let uu____318 = FStar_Options.trace_error () in
        if uu____318
        then
          let uu____319 = FStar_Util.message_of_exn e in
          FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____319
            trace
        else
          if Prims.op_Negation (FStar_Errors.handleable e)
          then
            (let uu____321 = FStar_Util.message_of_exn e in
             FStar_Util.print1_error
               "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
               uu____321)
          else ());
       cleanup ();
       report_errors [];
       FStar_All.exit (Prims.parse_int "1"))