open Prims
let uu___221 : Prims.unit = FStar_Version.dummy () 
let process_args :
  Prims.unit -> (FStar_Getopt.parse_cmdline_res * Prims.string Prims.list) =
  fun uu____6  -> FStar_Options.parse_cmd_line () 
let cleanup : Prims.unit -> Prims.unit =
  fun uu____12  -> FStar_Util.kill_all () 
let finished_message :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list ->
    Prims.int -> Prims.unit
  =
  fun fmods  ->
    fun errs  ->
      let print_to =
        if errs > (Prims.parse_int "0")
        then FStar_Util.print_error
        else FStar_Util.print_string  in
      let uu____35 =
        let uu____36 = FStar_Options.silent ()  in Prims.op_Negation uu____36
         in
      if uu____35
      then
        (FStar_All.pipe_right fmods
           (FStar_List.iter
              (fun uu____47  ->
                 match uu____47 with
                 | ((iface,name),time) ->
                     let tag =
                       if iface then "i'face (or impl+i'face)" else "module"
                        in
                     let uu____59 =
                       FStar_Options.should_print_message
                         name.FStar_Ident.str
                        in
                     if uu____59
                     then
                       (if time >= (Prims.parse_int "0")
                        then
                          let uu____60 =
                            let uu____61 = FStar_Util.string_of_int time  in
                            FStar_Util.format3
                              "Verified %s: %s (%s milliseconds)\n" tag
                              (FStar_Ident.text_of_lid name) uu____61
                             in
                          print_to uu____60
                        else
                          (let uu____63 =
                             FStar_Util.format2 "Verified %s: %s\n" tag
                               (FStar_Ident.text_of_lid name)
                              in
                           print_to uu____63))
                     else ()));
         if errs > (Prims.parse_int "0")
         then
           (if errs = (Prims.parse_int "1")
            then FStar_Util.print_error "1 error was reported (see above)\n"
            else
              (let uu____66 = FStar_Util.string_of_int errs  in
               FStar_Util.print1_error
                 "%s errors were reported (see above)\n" uu____66))
         else
           (let uu____68 =
              let uu____69 =
                FStar_Util.colorize_bold
                  "All verification conditions discharged successfully"
                 in
              FStar_Util.format1 "%s\n" uu____69  in
            FStar_Util.print_string uu____68))
      else ()
  
let report_errors :
  ((Prims.bool * FStar_Ident.lident) * Prims.int) Prims.list -> Prims.unit =
  fun fmods  ->
    let errs = FStar_Errors.get_err_count ()  in
    if errs > (Prims.parse_int "0")
    then (finished_message fmods errs; FStar_All.exit (Prims.parse_int "1"))
    else ()
  
let codegen :
  (FStar_Syntax_Syntax.modul Prims.list * FStar_TypeChecker_Env.env) ->
    Prims.unit
  =
  fun uu____92  ->
    match uu____92 with
    | (umods,env) ->
        let opt = FStar_Options.codegen ()  in
        if opt <> None
        then
          let mllibs =
            let uu____106 =
              let uu____111 = FStar_Extraction_ML_UEnv.mkContext env  in
              FStar_Util.fold_map FStar_Extraction_ML_Modul.extract uu____111
                umods
               in
            FStar_All.pipe_left Prims.snd uu____106  in
          let mllibs1 = FStar_List.flatten mllibs  in
          let ext =
            match opt with
            | Some "FSharp" -> ".fs"
            | Some "OCaml" -> ".ml"
            | Some "Kremlin" -> ".krml"
            | uu____124 -> failwith "Unrecognized option"  in
          (match opt with
           | Some "FSharp"|Some "OCaml" ->
               let outdir = FStar_Options.output_dir ()  in
               FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
                 mllibs1
           | Some "Kremlin" ->
               let programs =
                 let uu____130 =
                   FStar_List.map FStar_Extraction_Kremlin.translate mllibs1
                    in
                 FStar_List.flatten uu____130  in
               let bin = (FStar_Extraction_Kremlin.current_version, programs)
                  in
               let uu____136 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____136 bin
           | uu____137 -> failwith "Unrecognized option")
        else ()
  
let go uu____146 =
  let uu____147 = process_args ()  in
  match uu____147 with
  | (res,filenames) ->
      (match res with
       | FStar_Getopt.Help  ->
           (FStar_Options.display_usage ();
            FStar_All.exit (Prims.parse_int "0"))
       | FStar_Getopt.Error msg -> FStar_Util.print_string msg
       | FStar_Getopt.Success  ->
           let uu____157 =
             let uu____158 = FStar_Options.dep ()  in uu____158 <> None  in
           if uu____157
           then
             let uu____161 =
               FStar_Parser_Dep.collect FStar_Parser_Dep.VerifyAll filenames
                in
             FStar_Parser_Dep.print uu____161
           else
             (let uu____176 = FStar_Options.interactive ()  in
              if uu____176
              then
                ((let uu____178 = FStar_Options.explicit_deps ()  in
                  if uu____178
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
                 (let filename = FStar_List.hd filenames  in
                  (let uu____188 =
                     let uu____189 = FStar_Options.verify_module ()  in
                     uu____189 <> []  in
                   if uu____188
                   then
                     FStar_Util.print_warning
                       "Interactive mode; ignoring --verify_module"
                   else ());
                  FStar_Interactive.interactive_mode filename))
              else
                (let uu____194 = FStar_Options.doc ()  in
                 if uu____194
                 then FStar_Fsdoc_Generator.generate filenames
                 else
                   (let uu____196 = FStar_Options.indent ()  in
                    if uu____196
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
                           let uu____203 = FStar_Options.verify_all ()  in
                           if uu____203
                           then
                             ((let uu____205 =
                                 let uu____206 =
                                   FStar_Options.verify_module ()  in
                                 uu____206 <> []  in
                               if uu____205
                               then
                                 (FStar_Util.print_error
                                    "--verify_module is incompatible with --verify_all";
                                  FStar_All.exit (Prims.parse_int "1"))
                               else ());
                              FStar_Parser_Dep.VerifyAll)
                           else
                             (let uu____212 =
                                let uu____213 =
                                  FStar_Options.verify_module ()  in
                                uu____213 <> []  in
                              if uu____212
                              then FStar_Parser_Dep.VerifyUserList
                              else FStar_Parser_Dep.VerifyFigureItOut)
                            in
                         let filenames1 =
                           FStar_Dependencies.find_deps_if_needed verify_mode
                             filenames
                            in
                         let uu____219 =
                           FStar_Universal.batch_mode_tc filenames1  in
                         match uu____219 with
                         | (fmods,dsenv,env) ->
                             let module_names_and_times =
                               FStar_All.pipe_right fmods
                                 (FStar_List.map
                                    (fun uu____255  ->
                                       match uu____255 with
                                       | (x,t) ->
                                           ((FStar_Universal.module_or_interface_name
                                               x), t)))
                                in
                             (report_errors module_names_and_times;
                              (let uu____268 =
                                 let uu____272 =
                                   FStar_All.pipe_right fmods
                                     (FStar_List.map Prims.fst)
                                    in
                                 (uu____272, env)  in
                               codegen uu____268);
                              finished_message module_names_and_times
                                (Prims.parse_int "0")))
                      else FStar_Util.print_error "no file provided\n"))))
  
let main uu____288 =
  try go (); cleanup (); FStar_All.exit (Prims.parse_int "0")
  with
  | e ->
      let trace = FStar_Util.trace_of_exn e  in
      (if FStar_Errors.handleable e
       then FStar_Errors.handle_err false e
       else ();
       (let uu____298 = FStar_Options.trace_error ()  in
        if uu____298
        then
          let uu____299 = FStar_Util.message_of_exn e  in
          FStar_Util.print2_error "Unexpected error\n%s\n%s\n" uu____299
            trace
        else
          if Prims.op_Negation (FStar_Errors.handleable e)
          then
            (let uu____301 = FStar_Util.message_of_exn e  in
             FStar_Util.print1_error
               "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n"
               uu____301)
          else ());
       cleanup ();
       (let uu____305 = FStar_Errors.report_all ()  in
        FStar_All.pipe_right uu____305 Prims.ignore);
       report_errors [];
       FStar_All.exit (Prims.parse_int "1"))
  