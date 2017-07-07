open Prims
let id_eq_lid: FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
let is_val: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____18) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____19 -> false
let is_type: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____28,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____48  ->
                  match uu____48 with
                  | (t,uu____53) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____56 -> false
let definition_lids: FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____63,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____71,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___197_96  ->
                match uu___197_96 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id,uu____102,uu____103,uu____104),uu____105) ->
                    let uu____112 = FStar_Ident.lid_of_ids [id] in
                    [uu____112]
                | uu____113 -> []))
    | uu____117 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____126 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____126
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
           | FStar_Parser_AST.Tycon (uu____155,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___198_175  ->
                       match uu___198_175 with
                       | (FStar_Parser_AST.TyconAbstract uu____179,uu____180)
                           -> true
                       | uu____188 -> false))
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
                 let uu____205 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____205
                  then
                    let uu____214 =
                      let uu____215 =
                        let uu____218 =
                          let uu____219 =
                            let uu____220 =
                              FStar_All.pipe_right def_ids
                                (FStar_List.map FStar_Ident.string_of_lid) in
                            FStar_All.pipe_right uu____220
                              (FStar_String.concat ", ") in
                          FStar_Util.format2
                            "Expected the definition of %s to precede %s"
                            x.FStar_Ident.idText uu____219 in
                        (uu____218, (impl.FStar_Parser_AST.drange)) in
                      FStar_Errors.Error uu____215 in
                    raise uu____214
                  else (iface1, [impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____260) -> ([], iface2)
                    | (uu____266::uu____267,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____285 = aux ys iface_tl1 in
                          (match uu____285 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____303 =
                             let uu____304 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____304 in
                           if uu____303
                           then
                             let uu____311 =
                               let uu____312 =
                                 let uu____315 =
                                   let uu____316 =
                                     FStar_Parser_AST.decl_to_string
                                       iface_hd1 in
                                   let uu____317 =
                                     FStar_Ident.string_of_lid y in
                                   FStar_Util.format2
                                     "%s is out of order with the definition of %s"
                                     uu____316 uu____317 in
                                 (uu____315,
                                   (iface_hd1.FStar_Parser_AST.drange)) in
                               FStar_Errors.Error uu____312 in
                             raise uu____311
                           else aux ys iface2) in
                  let uu____323 = aux mutually_defined_with_x iface_tl in
                  match uu____323 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____340 ->
               let uu____341 = prefix_with_iface_decls iface_tl impl in
               (match uu____341 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____374,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___199_394  ->
                       match uu___199_394 with
                       | (FStar_Parser_AST.TyconAbstract uu____398,uu____399)
                           -> true
                       | uu____407 -> false))
               ->
               raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (hd1.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let uu____413 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____413
               then
                 let uu____414 =
                   let uu____415 =
                     let uu____418 =
                       FStar_Util.format2
                         "'val %s' and 'let %s' cannot both be provided in an interface"
                         x.FStar_Ident.idText x.FStar_Ident.idText in
                     (uu____418, (hd1.FStar_Parser_AST.drange)) in
                   FStar_Errors.Error uu____415 in
                 raise uu____414
               else
                 (let uu____420 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____420
                  then
                    raise
                      (FStar_Errors.Error
                         ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead",
                           (hd1.FStar_Parser_AST.drange)))
                  else ())
           | uu____422 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____429 -> false
            | uu____430 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____449,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____459 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____459 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____481 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____496 -> true
            | uu____499 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____518 -> (iface1, [impl])
      | uu____521 ->
          let uu____522 = FStar_Options.ml_ish () in
          if uu____522
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
          let uu____544 = FStar_Options.ml_ish () in
          if uu____544
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____547 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____547 with
        | FStar_Pervasives_Native.Some uu____550 ->
            let uu____553 =
              let uu____554 =
                let uu____557 =
                  let uu____558 = FStar_Ident.string_of_lid mname in
                  FStar_Util.format1
                    "Interface %s has already been processed" uu____558 in
                (uu____557, (FStar_Ident.range_of_lid mname)) in
              FStar_Errors.Error uu____554 in
            raise uu____553
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
      let uu____574 =
        let uu____577 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____577 in
      match uu____574 with
      | FStar_Pervasives_Native.None  -> (env, [impl])
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____586 = prefix_one_decl iface1 impl in
          (match uu____586 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____601 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____601 iface2 in
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
        | FStar_Parser_AST.Interface uu____619 -> (env, a)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____628 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____628 with
             | FStar_Pervasives_Native.None  -> (env, a)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____637 =
                   FStar_List.fold_left
                     (fun uu____653  ->
                        fun impl  ->
                          match uu____653 with
                          | (iface2,impls1) ->
                              let uu____669 = prefix_one_decl iface2 impl in
                              (match uu____669 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____637 with
                  | (iface2,impls1) ->
                      let env1 =
                        FStar_ToSyntax_Env.set_iface_decls env l iface2 in
                      let a1 = FStar_Parser_AST.Module (l, impls1) in
                      (match iface2 with
                       | uu____701::uu____702 when expect_complete_modul ->
                           let err1 =
                             let uu____705 =
                               FStar_List.map FStar_Parser_AST.decl_to_string
                                 iface2 in
                             FStar_All.pipe_right uu____705
                               (FStar_String.concat "\n\t") in
                           let uu____708 =
                             let uu____709 =
                               let uu____712 =
                                 let uu____713 = FStar_Ident.string_of_lid l in
                                 FStar_Util.format2
                                   "Some interface elements were not implemented by module %s:\n\t%s"
                                   uu____713 err1 in
                               (uu____712, (FStar_Ident.range_of_lid l)) in
                             FStar_Errors.Error uu____709 in
                           raise uu____708
                       | uu____716 -> (env1, a1))))