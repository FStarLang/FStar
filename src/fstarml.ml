(* Code auto-generated from Fstar and hand-modified *)
    let process_args _20038 =
      match _20038 with
      | () ->
          let file_list = Fstar.Support.Microsoft.FStar.Util.mk_ref [] in
          let res =
            Fstar.Support.Microsoft.FStar.Getopt.parse_cmdline
              (Microsoft_FStar_Options.specs ())
              (fun i ->
                 file_list :=
                   Fstar.Support.List.append
                     (Fstar.Support.ST.read file_list) [ i ]) in
          let _20044 =
            (match res with
             | Fstar.Support.Microsoft.FStar.Getopt.GoOn ->
                 Fstar.Support.Prims.ignore
                   (Microsoft_FStar_Options.set_fstar_home ())
             | _ -> ())
          in (res, (Fstar.Support.ST.read file_list))
      
    let cleanup _20045 =
      match _20045 with
      | () ->
          let _20046 = Microsoft_FStar_ToSMT_Z3.cleanup ()
          in Fstar.Support.Microsoft.FStar.Util.kill_all ()
      
    let has_prims_cache l = Fstar.Support.List.mem "Prims.cache" l
      
    let go _20048 =
      let finished mods =
        if Fstar.Support.ST.read Microsoft_FStar_Options.silent
        then ()
        else
          (let msg =
             if Fstar.Support.ST.read Microsoft_FStar_Options.verify
             then "Verified"
             else
               if Fstar.Support.ST.read Microsoft_FStar_Options.pretype
               then "Lax type-checked"
               else "Parsed and desugared"
           in
             Fstar.Support.List.iter
               (fun m ->
                  Fstar.Support.Microsoft.FStar.Util.print_string
                    (Fstar.Support.Microsoft.FStar.Util.format2
                       "%s module: %s\n" msg
                       (Microsoft_FStar_Absyn_Syntax.text_of_lid
                          m.Microsoft_FStar_Absyn_Syntax.name)))
               mods) in
      let _20055 = process_args ()
      in
        match _20055 with
        | (res, filenames) ->
            (match res with
             | Fstar.Support.Microsoft.FStar.Getopt.Help ->
                 Microsoft_FStar_Options.display_usage
                   (Microsoft_FStar_Options.specs ())
             | Fstar.Support.Microsoft.FStar.Getopt.Die msg ->
                 Fstar.Support.Microsoft.FStar.Util.print_string msg
             | Fstar.Support.Microsoft.FStar.Getopt.GoOn ->
                 let _20060 =
                   if
                     not
                       (Fstar.Support.Option.isNone
                          (Fstar.Support.ST.read Microsoft_FStar_Options.
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
                   if Fstar.Support.ST.read Microsoft_FStar_Options.verify
                   then Microsoft_FStar_ToSMT_Encode.solver
                   else Microsoft_FStar_ToSMT_Encode.dummy in
                 let fmods =
                   if Fstar.Support.ST.read Microsoft_FStar_Options.pretype
                   then
                     Microsoft_FStar_Tc_Tc.check_modules solver
                       Microsoft_FStar_ToSMT_Encode.dummy fmods
                   else fmods in
                 let _20065 = finished fmods in
                 let errs = Microsoft_FStar_Tc_Errors.get_err_count ()
                 in
                   if Fstar.Support.ST.read Microsoft_FStar_Options.verify
                   then
                     if errs > 0
                     then
                       (let _20067 =
                          Fstar.Support.Microsoft.FStar.Util.fprint1
                            "Error: %s errors were reported (see above)\n"
                            (Fstar.Support.Microsoft.FStar.Util.string_of_int
                               errs)
                        in exit 1)
                     else
                       if
                         not
                           (Fstar.Support.ST.read Microsoft_FStar_Options.
                              silent)
                       then
                         Fstar.Support.Microsoft.FStar.Util.print_string
                           "All verification conditions discharged successfully\n"
                       else ()
                   else ())
      
    let x =
      Printexc.record_backtrace true;
      Gc.set { (Gc.get()) with Gc.minor_heap_size = 1048576; Gc.major_heap_increment = 4194304; Gc.space_overhead = 150; };
      Fstar.Support.Prims.try_with
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
                        (Fstar.Support.ST.read Microsoft_FStar_Options.
                           trace_error))
                 then
                   Printf.printf "Unexpected error %s:\n%s\n" (Printexc.to_string e) (Printexc.get_backtrace())
                 else () in
               let _20074 = cleanup () in exit 1)
