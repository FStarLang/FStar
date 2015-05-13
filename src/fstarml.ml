(* Code auto-generated from Fstar and hand-modified *)
    let process_args _20038 =
      match _20038 with
      | () ->
          let file_list = Support.Microsoft.FStar.Util.mk_ref [] in
          let res =
            Support.Microsoft.FStar.Getopt.parse_cmdline
              (Microsoft_FStar_Options.specs ())
              (fun i ->
                 file_list :=
                   Support.List.append
                     (Support.ST.read file_list) [ i ]) in
          let _20044 =
            (match res with
             | Support.Microsoft.FStar.Getopt.GoOn ->
                 Support.Prims.ignore
                   (Microsoft_FStar_Options.set_fstar_home ())
             | _ -> ())
          in (res, (Support.ST.read file_list))
      
    let cleanup _20045 =
      match _20045 with
      | () -> Support.Microsoft.FStar.Util.kill_all ()
      
    let has_prims_cache l = Support.List.mem "Prims.cache" l
      
    let go _20048 =
      let finished mods =
        if Support.ST.read Microsoft_FStar_Options.silent
        then ()
        else
          (let msg =
             if Support.ST.read Microsoft_FStar_Options.verify
             then "Verified"
             else
               if Support.ST.read Microsoft_FStar_Options.pretype
               then "Lax type-checked"
               else "Parsed and desugared"
           in
             Support.List.iter
               (fun m ->
                  Support.Microsoft.FStar.Util.print_string
                    (Support.Microsoft.FStar.Util.format2
                       "%s module: %s\n" msg
                       (Microsoft_FStar_Absyn_Syntax.text_of_lid
                          m.Microsoft_FStar_Absyn_Syntax.name)))
               mods) in
      let _20055 = process_args ()
      in
        match _20055 with
        | (res, filenames) ->
            (match res with
             | Support.Microsoft.FStar.Getopt.Help ->
                 Microsoft_FStar_Options.display_usage
                   (Microsoft_FStar_Options.specs ())
             | Support.Microsoft.FStar.Getopt.Die msg ->
                 Support.Microsoft.FStar.Util.print_string msg
             | Support.Microsoft.FStar.Getopt.GoOn ->
                if !Microsoft_FStar_Options.interactive
                then (Support.Microsoft.FStar.Util.print_string "This version (OCaml) does not yet support interactive mode"; exit 1);
                let filenames = 
                  if !Microsoft_FStar_Options.use_build_config  (* if the user explicitly requested it *)
                     || (Array.length Sys.argv = 2     (* or, if there is only a single file on the command line *)
                         && List.length filenames = 1)
                  then match filenames with 
                       | [f] -> Microsoft_FStar_Parser_Driver.read_build_config f (* then, try to read a build config from the header of the file *)
                       | _ -> Support.Microsoft.FStar.Util.print_string "--use_build_config expects just a single file on the command line and no other arguments"; exit 1
                  else filenames in
                 let _20060 =
                   if
                     not
                       (Support.Option.isNone
                          (Support.ST.read Microsoft_FStar_Options.
                             codegen))
                   then Microsoft_FStar_Options.pretype := true
                   else () in
                 let filenames =
                   if has_prims_cache filenames
                   then filenames
                   else (Microsoft_FStar_Options.prims ()) :: filenames in
                 let fmods =
                   Microsoft_FStar_Parser_Driver.parse_files filenames in
                 let solver =
                   if Support.ST.read Microsoft_FStar_Options.verify
                   then Microsoft_FStar_ToSMT_Encode.solver
                   else Microsoft_FStar_ToSMT_Encode.dummy in
                 let fmods =
                   if Support.ST.read Microsoft_FStar_Options.pretype
                   then
                     Microsoft_FStar_Tc_Tc.check_modules solver fmods
                   else fmods in
                solver.finish();


             let _20222 =
               if
                 (Support.ST.read Microsoft_FStar_Options.codegen) =
                   (Some "OCaml")
               then
                 Support.Prims.try_with
                   (fun _20211 ->
                      match _20211 with
                      | () ->
                          let mllib =
                            Microsoft_FStar_Backends_OCaml_ASTTrans.mlmod_of_fstars
                              (Support.List.tail fmods) in
                          let doc =
                            Microsoft_FStar_Backends_OCaml_Code.doc_of_mllib mllib
                          in 
                            List.iter (fun (n,d) -> Support.Microsoft.FStar.Util.write_file (Microsoft_FStar_Options.prependOutputDir (n^".ml")) (FSharp_Format.pretty 120 d)) doc)
                   (fun _20210 ->
                      match _20210 with
                      | Microsoft_FStar_Backends_OCaml_ASTTrans.OCamlFailure (rg, error) ->
                          let _20217 =
                            Support.Microsoft.FStar.Util.print_string
                              (Support.Microsoft.FStar.Util.format2
                                 "OCaml Backend Error: %s %s\n"
                                 (Support.Microsoft.FStar.Range.
                                    string_of_range rg)
                                 (Microsoft_FStar_Backends_OCaml_ASTTrans.string_of_error error))
                          in exit 1)
               else () in


                 let _20065 = finished fmods in
                 let errs = Microsoft_FStar_Tc_Errors.get_err_count ()
                 in
                   if Support.ST.read Microsoft_FStar_Options.verify
                   then
                     if errs > 0
                     then
                       (let _20067 =
                          Support.Microsoft.FStar.Util.fprint1
                            "Error: %s errors were reported (see above)\n"
                            (Support.Microsoft.FStar.Util.string_of_int
                               errs)
                        in exit 1)
                     else
                       if
                         not
                           (Support.ST.read Microsoft_FStar_Options.
                              silent)
                       then
                         Support.Microsoft.FStar.Util.print_string
                           "All verification conditions discharged successfully\n"
                       else ()
                   else ())
      
    let x =
      Printexc.record_backtrace true;
      Gc.set { (Gc.get()) with Gc.minor_heap_size = 1048576; Gc.major_heap_increment = 4194304; Gc.space_overhead = 150; };
      Support.Prims.try_with
        (fun _20069 ->
           match _20069 with
           | () -> let _20077 = go () in let _20078 = cleanup () in exit 0)
        (fun _20068 ->
           match _20068 with
           | e ->
               
               let _20072 =
                 if Microsoft_FStar_Absyn_Util.handleable e
                 then Microsoft_FStar_Absyn_Util.handle_err false () e
                 else () in
               let _20073 =
                 if
                   not
                     ((Microsoft_FStar_Absyn_Util.handleable e) ||
                        (Support.ST.read Microsoft_FStar_Options.
                           trace_error))
                 then
                   Printf.printf "Unexpected error %s:\n%s\n" (Printexc.to_string e) (Printexc.get_backtrace())
                 else () in
               let _20074 = cleanup () in exit 1)
