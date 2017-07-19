open Prims
let id_eq_lid: FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
let is_val: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____14) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____15 -> false
let is_type: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____22,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____54  ->
                  match uu____54 with
                  | (t,uu____62) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____67 -> false
let definition_lids: FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____75,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____89,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___195_123  ->
                match uu___195_123 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id,uu____133,uu____134,uu____135),uu____136) ->
                    let uu____149 = FStar_Ident.lid_of_ids [id] in
                    [uu____149]
                | uu____150 -> []))
    | uu____157 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____164 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____164
let rec prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match iface1 with
      | [] -> ([], [impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____217,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___196_249  ->
                       match uu___196_249 with
                       | (FStar_Parser_AST.TyconAbstract uu____256,uu____257)
                           -> true
                       | uu____272 -> false))
               ->
               raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (impl.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let def_ids = definition_lids impl in
               let defines_x = FStar_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 let uu____301 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____301
                  then
                    let uu____315 =
                      let uu____316 =
                        let uu____321 =
                          let uu____322 =
                            let uu____323 =
                              FStar_All.pipe_right def_ids
                                (FStar_List.map FStar_Ident.string_of_lid) in
                            FStar_All.pipe_right uu____323
                              (FStar_String.concat ", ") in
                          FStar_Util.format2
                            "Expected the definition of %s to precede %s"
                            x.FStar_Ident.idText uu____322 in
                        (uu____321, (impl.FStar_Parser_AST.drange)) in
                      FStar_Errors.Error uu____316 in
                    raise uu____315
                  else (iface1, [impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____389) -> ([], iface2)
                    | (uu____400::uu____401,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____432 = aux ys iface_tl1 in
                          (match uu____432 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____464 =
                             let uu____465 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____465 in
                           if uu____464
                           then
                             let uu____478 =
                               let uu____479 =
                                 let uu____484 =
                                   let uu____485 =
                                     FStar_Parser_AST.decl_to_string
                                       iface_hd1 in
                                   let uu____486 =
                                     FStar_Ident.string_of_lid y in
                                   FStar_Util.format2
                                     "%s is out of order with the definition of %s"
                                     uu____485 uu____486 in
                                 (uu____484,
                                   (iface_hd1.FStar_Parser_AST.drange)) in
                               FStar_Errors.Error uu____479 in
                             raise uu____478
                           else aux ys iface2) in
                  let uu____496 = aux mutually_defined_with_x iface_tl in
                  match uu____496 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____527 ->
               let uu____528 = prefix_with_iface_decls iface_tl impl in
               (match uu____528 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____580,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___197_612  ->
                       match uu___197_612 with
                       | (FStar_Parser_AST.TyconAbstract uu____619,uu____620)
                           -> true
                       | uu____635 -> false))
               ->
               raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (hd1.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let uu____644 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____644
               then
                 let uu____645 =
                   let uu____646 =
                     let uu____651 =
                       FStar_Util.format2
                         "'val %s' and 'let %s' cannot both be provided in an interface"
                         x.FStar_Ident.idText x.FStar_Ident.idText in
                     (uu____651, (hd1.FStar_Parser_AST.drange)) in
                   FStar_Errors.Error uu____646 in
                 raise uu____645
               else
                 (let uu____653 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____653
                  then
                    raise
                      (FStar_Errors.Error
                         ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead",
                           (hd1.FStar_Parser_AST.drange)))
                  else ())
           | uu____655 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____662 -> false
            | uu____663 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____698,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____715 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____715 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____750 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____769 -> true
            | uu____774 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____801 -> (iface1, [impl])
      | uu____806 ->
          let uu____807 = FStar_Options.ml_ish () in
          if uu____807
          then ml_mode_prefix_with_iface_decls iface1 impl
          else prefix_with_iface_decls iface1 impl
let initialize_interface:
  FStar_Ident.lid ->
    FStar_Parser_AST.decl Prims.list ->
      FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun mname  ->
    fun l  ->
      fun env  ->
        let decls =
          let uu____833 = FStar_Options.ml_ish () in
          if uu____833
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____837 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____837 with
        | FStar_Pervasives_Native.Some uu____842 ->
            let uu____847 =
              let uu____848 =
                let uu____853 =
                  let uu____854 = FStar_Ident.string_of_lid mname in
                  FStar_Util.format1
                    "Interface %s has already been processed" uu____854 in
                (uu____853, (FStar_Ident.range_of_lid mname)) in
              FStar_Errors.Error uu____848 in
            raise uu____847
        | FStar_Pervasives_Native.None  ->
            FStar_ToSyntax_Env.set_iface_decls env mname decls
let prefix_with_interface_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_ToSyntax_Env.env,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun impl  ->
      let uu____875 =
        let uu____880 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____880 in
      match uu____875 with
      | FStar_Pervasives_Native.None  -> (env, [impl])
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____896 = prefix_one_decl iface1 impl in
          (match uu____896 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____922 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____922 iface2 in
               (env1, impl1))
let interleave_module:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      Prims.bool ->
        (FStar_ToSyntax_Env.env,FStar_Parser_AST.modul)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      fun expect_complete_modul  ->
        match a with
        | FStar_Parser_AST.Interface uu____946 -> (env, a)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____961 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____961 with
             | FStar_Pervasives_Native.None  -> (env, a)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____977 =
                   FStar_List.fold_left
                     (fun uu____994  ->
                        fun impl  ->
                          match uu____994 with
                          | (iface2,impls1) ->
                              let uu____1022 = prefix_one_decl iface2 impl in
                              (match uu____1022 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____977 with
                  | (iface2,impls1) ->
                      let env1 =
                        FStar_ToSyntax_Env.set_iface_decls env l iface2 in
                      let a1 = FStar_Parser_AST.Module (l, impls1) in
                      (match iface2 with
                       | uu____1079::uu____1080 when expect_complete_modul ->
                           let err1 =
                             let uu____1084 =
                               FStar_List.map FStar_Parser_AST.decl_to_string
                                 iface2 in
                             FStar_All.pipe_right uu____1084
                               (FStar_String.concat "\n\t") in
                           let uu____1089 =
                             let uu____1090 =
                               let uu____1095 =
                                 let uu____1096 = FStar_Ident.string_of_lid l in
                                 FStar_Util.format2
                                   "Some interface elements were not implemented by module %s:\n\t%s"
                                   uu____1096 err1 in
                               (uu____1095, (FStar_Ident.range_of_lid l)) in
                             FStar_Errors.Error uu____1090 in
                           raise uu____1089
                       | uu____1101 -> (env1, a1))))