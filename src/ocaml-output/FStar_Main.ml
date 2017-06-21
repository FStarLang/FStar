open Prims
<<<<<<< HEAD
let uu___179: Prims.unit = FStar_Version.dummy ()
=======
let uu___260: Prims.unit = FStar_Version.dummy ()
>>>>>>> origin/guido_tactics
let process_args:
  Prims.unit -> (FStar_Getopt.parse_cmdline_res* Prims.string Prims.list) =
  fun uu____7  -> FStar_Options.parse_cmd_line ()
let cleanup: Prims.unit -> Prims.unit =
  fun uu____14  -> FStar_Util.kill_all ()
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
      let uu____39 =
        let uu____40 = FStar_Options.silent () in Prims.op_Negation uu____40 in
      if uu____39
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
<<<<<<< HEAD
              (fun uu____54  ->
                 match uu____54 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module" in
                     let uu____66 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____66
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____67 =
                            let uu____68 = FStar_Util.string_of_int time in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____68 in
                          print_to uu____67
                        else
                          (let uu____70 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name) in
                           print_to uu____70))
=======
              (fun uu____51  ->
                 match uu____51 with
                 | ((iface1,name),time) ->
                     let tag =
                       if iface1 then "i'face (or impl+i'face)" else "module" in
                     let uu____63 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____63
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____64 =
                            let uu____65 = FStar_Util.string_of_int time in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____65 in
                          print_to uu____64
                        else
                          (let uu____67 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name) in
                           print_to uu____67))
>>>>>>> origin/guido_tactics
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
<<<<<<< HEAD
              (let uu____73 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____73))
         else
           (let uu____75 =
              let uu____76 =
                FStar_Util.colorize_bold
                  "All verification conditions discharged successfully" in
              FStar_Util.format1 "%s\n" uu____76 in
            FStar_Util.print_string uu____75))
=======
              (let uu____70 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____70))
         else
           (let uu____72 =
              let uu____73 =
                FStar_Util.colorize_bold
                  "All verification conditions discharged successfully" in
              FStar_Util.format1 "%s\n" uu____73 in
            FStar_Util.print_string uu____72))
>>>>>>> origin/guido_tactics
      else ()
let report_errors:
  ((Prims.bool* FStar_Ident.lident)* Prims.int) Prims.list -> Prims.unit =
  fun fmods  ->
<<<<<<< HEAD
    (let uu____92 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____92 FStar_Pervasives.ignore);
=======
    (let uu____90 = FStar_Errors.report_all () in
     FStar_All.pipe_right uu____90 FStar_Pervasives.ignore);
>>>>>>> origin/guido_tactics
    (let nerrs = FStar_Errors.get_err_count () in
     if nerrs > (Prims.parse_int "0")
     then
       (finished_message fmods nerrs; FStar_All.exit (Prims.parse_int "1"))
     else ())
let codegen:
  (FStar_Syntax_Syntax.modul Prims.list* FStar_TypeChecker_Env.env) ->
    Prims.unit
  =
<<<<<<< HEAD
  fun uu____104  ->
    match uu____104 with
=======
  fun uu____103  ->
    match uu____103 with
>>>>>>> origin/guido_tactics
    | (umods,env) ->
        let opt = FStar_Options.codegen () in
        if opt <> None
        then
          let mllibs =
<<<<<<< HEAD
            let uu____118 =
              let uu____123 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____123
                umods in
            FStar_All.pipe_left FStar_Pervasives.snd uu____118 in
=======
            let uu____117 =
              let uu____122 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____122
                umods in
            FStar_All.pipe_left FStar_Pervasives.snd uu____117 in
>>>>>>> origin/guido_tactics
          let mllibs1 = FStar_List.flatten mllibs in
          let ext =
            match opt with
            | Some "FSharp" -> ".fs"
            | Some "OCaml" -> ".ml"
            | Some "Kremlin" -> ".krml"
<<<<<<< HEAD
            | uu____136 -> failwith "Unrecognized option" in
=======
            | uu____135 -> failwith "Unrecognized option" in
>>>>>>> origin/guido_tactics
          (match opt with
           | Some "FSharp" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | Some "OCaml" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | Some "Kremlin" ->
               let programs =
<<<<<<< HEAD
                 let uu____144 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1 in
                 FStar_List.flatten uu____144 in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let uu____150 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____150 bin
           | uu____151 -> failwith "Unrecognized option")
        else ()
let go uu____160 =
  let uu____161 = process_args () in
  match uu____161 with
=======
                 let uu____143 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1 in
                 FStar_List.flatten uu____143 in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let uu____149 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____149 bin
           | uu____150 -> failwith "Unrecognized option")
        else ()
let go uu____161 =
  let uu____162 = process_args () in
  match uu____162 with
>>>>>>> origin/guido_tactics
  | (res,filenames) ->
      (match res with
       | FStar_Getopt.Help  ->
           (FStar_Options.display_usage ();
            FStar_All.exit (Prims.parse_int "0"))
       | FStar_Getopt.Error msg -> FStar_Util.print_string msg
       | FStar_Getopt.Success  ->
<<<<<<< HEAD
           let uu____171 =
             let uu____172 = FStar_Options.dep () in uu____172 <> None in
           if uu____171
           then
             let uu____175 =
               FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames in
             FStar_Parser_Dep.print uu____175
           else
             (let uu____190 = FStar_Options.interactive () in
              if uu____190
              then
                ((let uu____192 = FStar_Options.explicit_deps () in
                  if uu____192
=======
           let uu____172 =
             let uu____173 = FStar_Options.dep () in uu____173 <> None in
           if uu____172
           then
             let uu____176 =
               FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames in
             FStar_Parser_Dep.print uu____176
           else
             (let uu____191 = FStar_Options.interactive () in
              if uu____191
              then
                ((let uu____193 = FStar_Options.explicit_deps () in
                  if uu____193
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                  (let uu____202 =
                     let uu____203 = FStar_Options.verify_module () in
                     uu____203 <> [] in
                   if uu____202
=======
                  (let uu____205 =
                     let uu____206 = FStar_Options.verify_module () in
                     uu____206 <> [] in
                   if uu____205
>>>>>>> origin/guido_tactics
                   then
                     FStar_Util.print_warning
                       "Interactive mode; ignoring --verify_module"
                   else ());
<<<<<<< HEAD
                  (let uu____207 = FStar_Options.legacy_interactive () in
                   if uu____207
                   then FStar_Legacy_Interactive.interactive_mode filename
                   else FStar_Interactive.interactive_mode filename)))
              else
                (let uu____210 = FStar_Options.doc () in
                 if uu____210
                 then FStar_Fsdoc_Generator.generate filenames
                 else
                   (let uu____212 = FStar_Options.indent () in
                    if uu____212
=======
                  (let uu____210 = FStar_Options.legacy_interactive () in
                   if uu____210
                   then FStar_Legacy_Interactive.interactive_mode filename
                   else FStar_Interactive.interactive_mode filename)))
              else
                (let uu____213 = FStar_Options.doc () in
                 if uu____213
                 then FStar_Fsdoc_Generator.generate filenames
                 else
                   (let uu____215 = FStar_Options.indent () in
                    if uu____215
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
                           let uu____219 = FStar_Options.verify_all () in
                           if uu____219
                           then
                             ((let uu____221 =
                                 let uu____222 =
                                   FStar_Options.verify_module () in
                                 uu____222 <> [] in
                               if uu____221
=======
                           let uu____225 = FStar_Options.verify_all () in
                           if uu____225
                           then
                             ((let uu____227 =
                                 let uu____228 =
                                   FStar_Options.verify_module () in
                                 uu____228 <> [] in
                               if uu____227
>>>>>>> origin/guido_tactics
                               then
                                 (FStar_Util.print_error
                                    "--verify_module is incompatible with --verify_all";
                                  FStar_All.exit (Prims.parse_int "1"))
                               else ());
                              FStar_Parser_Dep.VerifyAll)
                           else
<<<<<<< HEAD
                             (let uu____228 =
                                let uu____229 =
                                  FStar_Options.verify_module () in
                                uu____229 <> [] in
                              if uu____228
=======
                             (let uu____234 =
                                let uu____235 =
                                  FStar_Options.verify_module () in
                                uu____235 <> [] in
                              if uu____234
>>>>>>> origin/guido_tactics
                              then FStar_Parser_Dep.VerifyUserList
                              else FStar_Parser_Dep.VerifyFigureItOut) in
                         let filenames1 =
                           FStar_Dependencies.find_deps_if_needed verify_mode
                             filenames in
<<<<<<< HEAD
                         let uu____235 =
                           FStar_Universal.batch_mode_tc filenames1 in
                         match uu____235 with
                         | (fmods,dsenv,env) ->
                             let module_names_and_times =
                               FStar_All.pipe_right fmods
                                 (FStar_List.map
                                    (fun uu____274  ->
                                       match uu____274 with
                                       | (x,t) ->
                                           ((FStar_Universal.module_or_interface_name
                                               x), t))) in
                             (report_errors module_names_and_times;
                              (let uu____287 =
                                 let uu____291 =
                                   FStar_All.pipe_right fmods
                                     (FStar_List.map FStar_Pervasives.fst) in
                                 (uu____291, env) in
                               codegen uu____287);
                              finished_message module_names_and_times
                                (Prims.parse_int "0")))
                      else FStar_Util.print_error "no file provided\n"))))
let main uu____307 =
=======
                         (let uu____242 = FStar_Options.load () in
                          match uu____242 with
                          | Some s -> FStar_Tactics_Load.load_tactic s
                          | None  -> ());
                         (let uu____245 =
                            FStar_Universal.batch_mode_tc filenames1 in
                          match uu____245 with
                          | (fmods,dsenv,env) ->
                              let module_names_and_times =
                                FStar_All.pipe_right fmods
                                  (FStar_List.map
                                     (fun uu____281  ->
                                        match uu____281 with
                                        | (x,t) ->
                                            ((FStar_Universal.module_or_interface_name
                                                x), t))) in
                              (report_errors module_names_and_times;
                               (let uu____294 =
                                  let uu____298 =
                                    FStar_All.pipe_right fmods
                                      (FStar_List.map FStar_Pervasives.fst) in
                                  (uu____298, env) in
                                codegen uu____294);
                               finished_message module_names_and_times
                                 (Prims.parse_int "0"))))
                      else FStar_Util.print_error "no file provided\n"))))
let main uu____316 =
>>>>>>> origin/guido_tactics
  try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
  with
  | e ->
      let trace = FStar_Util.trace_of_exn e in
      (if FStar_Errors.handleable e then FStar_Errors.err_exn e else ();
       (let uu____326 = FStar_Options.trace_error () in
        if uu____326
        then
          let uu____327 = FStar_Util.message_of_exn e in
          FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____327
            trace
        else
          if Prims.op_Negation (FStar_Errors.handleable e)
          then
            (let uu____329 = FStar_Util.message_of_exn e in
             FStar_Util.print1_error
               "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
               uu____329)
          else ());
       cleanup ();
       report_errors [];
       FStar_All.exit (Prims.parse_int "1"))