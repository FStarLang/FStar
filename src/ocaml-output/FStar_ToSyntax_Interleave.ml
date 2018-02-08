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
               (fun uu____57  ->
                  match uu____57 with
                  | (t,uu____65) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____70 -> false
let definition_lids: FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____78,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____92,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___56_133  ->
                match uu___56_133 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____143,uu____144,uu____145),uu____146) ->
                    let uu____159 = FStar_Ident.lid_of_ids [id1] in
                    [uu____159]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____161,uu____162,uu____163),uu____164) ->
                    let uu____197 = FStar_Ident.lid_of_ids [id1] in
                    [uu____197]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____199,uu____200,uu____201),uu____202) ->
                    let uu____243 = FStar_Ident.lid_of_ids [id1] in
                    [uu____243]
                | uu____244 -> []))
    | uu____251 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____258 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____258
let rec prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      let qualify_kremlin_private impl1 =
        let krem_private =
          FStar_Parser_AST.mk_term
            (FStar_Parser_AST.Const
               (FStar_Const.Const_string
                  ("KremlinPrivate", (impl1.FStar_Parser_AST.drange))))
            impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr in
        let uu___60_292 = impl1 in
        {
          FStar_Parser_AST.d = (uu___60_292.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___60_292.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___60_292.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___60_292.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        } in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____317,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___57_352  ->
                       match uu___57_352 with
                       | (FStar_Parser_AST.TyconAbstract uu____359,uu____360)
                           -> true
                       | uu____375 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 impl.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let def_ids = definition_lids impl in
               let defines_x = FStar_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 let uu____404 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____404
                  then
                    let uu____419 =
                      let uu____424 =
                        let uu____425 =
                          let uu____426 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid) in
                          FStar_All.pipe_right uu____426
                            (FStar_String.concat ", ") in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____425 in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____424) in
                    FStar_Errors.raise_error uu____419
                      impl.FStar_Parser_AST.drange
                  else (iface1, [qualify_kremlin_private impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____493) -> ([], iface2)
                    | (uu____504::uu____505,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____536 = aux ys iface_tl1 in
                          (match uu____536 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____568 =
                             let uu____569 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____569 in
                           if uu____568
                           then
                             let uu____582 =
                               let uu____587 =
                                 let uu____588 =
                                   FStar_Parser_AST.decl_to_string iface_hd1 in
                                 let uu____589 = FStar_Ident.string_of_lid y in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____588 uu____589 in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____587) in
                             FStar_Errors.raise_error uu____582
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2) in
                  let uu____599 = aux mutually_defined_with_x iface_tl in
                  match uu____599 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____630 ->
               let uu____631 = prefix_with_iface_decls iface_tl impl in
               (match uu____631 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____683,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___58_718  ->
                       match uu___58_718 with
                       | (FStar_Parser_AST.TyconAbstract uu____725,uu____726)
                           -> true
                       | uu____741 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____750 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____750
               then
                 let uu____751 =
                   let uu____756 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____756) in
                 FStar_Errors.raise_error uu____751
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____758 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____758
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____760 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____769 -> false
            | uu____770 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____797,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____814 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____814 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____851 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____872 -> true
            | uu____877 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____904 -> (iface1, [impl])
      | uu____909 ->
          let uu____910 = FStar_Options.ml_ish () in
          if uu____910
          then ml_mode_prefix_with_iface_decls iface1 impl
          else prefix_with_iface_decls iface1 impl
let initialize_interface:
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list -> Prims.unit FStar_ToSyntax_Env.withenv
  =
  fun mname  ->
    fun l  ->
      fun env  ->
        let decls =
          let uu____942 = FStar_Options.ml_ish () in
          if uu____942
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____946 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____946 with
        | FStar_Pervasives_Native.Some uu____955 ->
            let uu____960 =
              let uu____965 =
                let uu____966 = FStar_Ident.string_of_lid mname in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____966 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____965) in
            FStar_Errors.raise_error uu____960
              (FStar_Ident.range_of_lid mname)
        | FStar_Pervasives_Native.None  ->
            let uu____973 =
              FStar_ToSyntax_Env.set_iface_decls env mname decls in
            ((), uu____973)
let prefix_with_interface_decls:
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_ToSyntax_Env.withenv
  =
  fun impl  ->
    fun env  ->
      let uu____990 =
        let uu____995 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____995 in
      match uu____990 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____1011 = prefix_one_decl iface1 impl in
          (match uu____1011 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1037 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____1037 iface2 in
               (impl1, env1))
let interleave_module:
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_ToSyntax_Env.withenv
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1059 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1074 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____1074 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1090 =
                   FStar_List.fold_left
                     (fun uu____1114  ->
                        fun impl  ->
                          match uu____1114 with
                          | (iface2,impls1) ->
                              let uu____1142 = prefix_one_decl iface2 impl in
                              (match uu____1142 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____1090 with
                  | (iface2,impls1) ->
                      let uu____1191 =
                        let uu____1200 =
                          FStar_Util.prefix_until
                            (fun uu___59_1219  ->
                               match uu___59_1219 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1220;
                                   FStar_Parser_AST.drange = uu____1221;
                                   FStar_Parser_AST.doc = uu____1222;
                                   FStar_Parser_AST.quals = uu____1223;
                                   FStar_Parser_AST.attrs = uu____1224;_} ->
                                   true
                               | uu____1231 -> false) iface2 in
                        match uu____1200 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest)) in
                      (match uu____1191 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets in
                           let env1 =
                             FStar_ToSyntax_Env.set_iface_decls env l
                               remaining_iface_vals in
                           let a1 = FStar_Parser_AST.Module (l, impls2) in
                           (match remaining_iface_vals with
                            | uu____1304::uu____1305 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1309 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals in
                                  FStar_All.pipe_right uu____1309
                                    (FStar_String.concat "\n\t") in
                                let uu____1314 =
                                  let uu____1319 =
                                    let uu____1320 =
                                      FStar_Ident.string_of_lid l in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1320 err in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1319) in
                                FStar_Errors.raise_error uu____1314
                                  (FStar_Ident.range_of_lid l)
                            | uu____1325 -> (a1, env1)))))