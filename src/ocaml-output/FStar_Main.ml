open Prims
let uu___186: Prims.unit = FStar_Version.dummy ()
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
      let uu____35 = Prims.op_Negation (FStar_Options.silent ()) in
      if uu____35
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____46  ->
                 match uu____46 with
                 | ((iface,name),time) ->
                     let tag =
                       if iface then "i'face (or impl+i'face)" else "module" in
                     let uu____58 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str in
                     if uu____58
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          print_to
                            (let _0_832 = FStar_Util.string_of_int time in
                             FStar_Util.format3
                               "Verified %s: %s (%s milliseconds)\n" tag
                               (FStar_Ident.text_of_lid name) _0_833)
                        else
                          print_to
                            (FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name)))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let _0_833 = FStar_Util.string_of_int errs in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" _0_834))
         else
           FStar_Util.print_string
             (let _0_835 =
                FStar_Util.colorize_bold
                  "All verification conditions discharged successfully" in
              FStar_Util.format1 "%s\n" _0_834))
      else ()
let report_errors:
  ((Prims.bool* FStar_Ident.lident)* Prims.int) Prims.list -> Prims.unit =
  fun fmods  ->
    let errs = FStar_Errors.get_err_count () in
    if errs > (Prims.parse_int "0")
    then (finished_message fmods errs; FStar_All.exit (Prims.parse_int "1"))
    else ()
let codegen:
  (FStar_Syntax_Syntax.modul Prims.list* FStar_TypeChecker_Env.env) ->
    Prims.unit
  =
  fun uu____85  ->
    match uu____85 with
    | (umods,env) ->
        let opt = FStar_Options.codegen () in
        if opt <> None
        then
          let mllibs =
            let _0_836 =
              let _0_835 = FStar_Extraction_ML_UEnv.mkContext env in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract _0_835
                umods in
            FStar_All.pipe_left Prims.snd _0_836 in
          let mllibs = FStar_List.flatten mllibs in
          let ext =
            match opt with
            | Some "FSharp" -> ".fs"
            | Some "OCaml" -> ".ml"
            | Some "Kremlin" -> ".krml"
            | uu____111 -> failwith "Unrecognized option" in
          (match opt with
           | Some "FSharp"|Some "OCaml" ->
               let outdir = FStar_Options.output_dir () in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs
           | Some "Kremlin" ->
               let programs =
                 FStar_List.flatten
                   (FStar_List.map FStar_Extraction_Kremlin.translate mllibs) in
               let bin = (FStar_Extraction_Kremlin.current_version, programs) in
               let _0_837 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file _0_837 bin
           | uu____120 -> failwith "Unrecognized option")
        else ()
let go uu____129 =
  let uu____130 = process_args () in
  match uu____130 with
  | (res,filenames) ->
      (match res with
       | FStar_Getopt.Help  ->
           (FStar_Options.display_usage ();
            FStar_All.exit (Prims.parse_int "0"))
       | FStar_Getopt.Error msg -> FStar_Util.print_string msg
       | FStar_Getopt.Success  ->
           let uu____140 =
             let _0_838 = FStar_Options.dep () in _0_838 <> None in
           if uu____140
           then
             FStar_Parser_Dep.print
               (FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames)
           else
             (let uu____144 = FStar_Options.interactive () in
              if uu____144
              then
                ((let uu____146 = FStar_Options.explicit_deps () in
                  if uu____146
                  then
                    (FStar_Util.print_error
                       "--explicit_deps incompatible with --in|n";
                     FStar_All.exit (Prims.parse_int "1"))
                  else ());
                 if (FStar_List.length filenames) <> (Prims.parse_int "1")
                 then
                   (FStar_Util.print_error
                      "fstar-mode.el should pass the current filename to F*\n";
                    FStar_All.exit (Prims.parse_int "1"))
                 else ();
                 (let filename = FStar_List.hd filenames in
                  let filename =
                    FStar_Parser_Dep.try_convert_file_name_to_windows
                      filename in
                  (let uu____157 =
                     let _0_839 = FStar_Options.verify_module () in
                     _0_839 <> [] in
                   if uu____157
                   then
                     FStar_Util.print_warning
                       "Interactive mode; ignoring --verify_module"
                   else ());
                  FStar_Interactive.interactive_mode filename))
              else
                (let uu____161 = FStar_Options.doc () in
                 if uu____161
                 then FStar_Fsdoc_Generator.generate filenames
                 else
                   (let uu____163 = FStar_Options.indent () in
                    if uu____163
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
                           let uu____170 = FStar_Options.verify_all () in
                           if uu____170
                           then
                             ((let uu____172 =
                                 let _0_840 = FStar_Options.verify_module () in
                                 _0_840 <> [] in
                               if uu____172
                               then
                                 (FStar_Util.print_error
                                    "--verify_module is incompatible with --verify_all";
                                  FStar_All.exit (Prims.parse_int "1"))
                               else ());
                              FStar_Parser_Dep.VerifyAll)
                           else
                             (let uu____177 =
                                let _0_841 = FStar_Options.verify_module () in
                                _0_841 <> [] in
                              if uu____177
                              then FStar_Parser_Dep.VerifyUserList
                              else FStar_Parser_Dep.VerifyFigureItOut) in
                         let filenames =
                           FStar_Dependencies.find_deps_if_needed verify_mode
                             filenames in
                         let uu____182 =
                           FStar_Universal.batch_mode_tc filenames in
                         match uu____182 with
                         | (fmods,dsenv,env) ->
                             let module_names_and_times =
                               FStar_All.pipe_right fmods
                                 (FStar_List.map
                                    (fun uu____218  ->
                                       match uu____218 with
                                       | (x,t) ->
                                           ((FStar_Universal.module_or_interface_name
                                               x), t))) in
                             (report_errors module_names_and_times;
                              codegen
                                (let _0_843 =
                                   FStar_All.pipe_right fmods
                                     (FStar_List.map Prims.fst) in
                                 (_0_842, env));
                              finished_message module_names_and_times
                                (Prims.parse_int "0")))
                      else FStar_Util.print_error "no file provided\n"))))
let main uu____245 =
  try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
  with
  | e ->
      (if FStar_Errors.handleable e
       then FStar_Errors.handle_err false e
       else ();
       (let uu____254 = FStar_Options.trace_error () in
        if uu____254
        then
          let _0_844 = FStar_Util.message_of_exn e in
          let _0_843 = FStar_Util.trace_of_exn e in
          FStar_Util.print2_error "Unexpected error\n%s\n%s\n" _0_844 _0_843
        else
          if Prims.op_Negation (FStar_Errors.handleable e)
          then
            (let _0_845 = FStar_Util.message_of_exn e in
             FStar_Util.print1_error
               "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
               _0_846)
          else ());
       cleanup ();
       (let _0_846 = FStar_Errors.report_all () in
        FStar_All.pipe_right _0_846 Prims.ignore);
       report_errors [];
       FStar_All.exit (Prims.parse_int "1"))