open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____26) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____28 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____43,uu____44,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____84  ->
                  match uu____84 with
                  | (t,uu____93) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____99 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____111,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____125,uu____126,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___0_171  ->
                match uu___0_171 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____181,uu____182,uu____183),uu____184) ->
                    let uu____197 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____197]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____199,uu____200,uu____201),uu____202) ->
                    let uu____235 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____235]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____237,uu____238,uu____239),uu____240) ->
                    let uu____283 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____283]
                | uu____284 -> []))
    | uu____291 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____304 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____304
  
let rec (prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      let qualify_kremlin_private impl1 =
        let krem_private =
          FStar_Parser_AST.mk_term
            (FStar_Parser_AST.Const
               (FStar_Const.Const_string
                  ("KremlinPrivate", (impl1.FStar_Parser_AST.drange))))
            impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr
           in
        let uu___66_347 = impl1  in
        {
          FStar_Parser_AST.d = (uu___66_347.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___66_347.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___66_347.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___66_347.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____372,uu____373,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___1_413  ->
                       match uu___1_413 with
                       | (FStar_Parser_AST.TyconAbstract uu____421,uu____422)
                           -> true
                       | uu____438 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 impl.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let def_ids = definition_lids impl  in
               let defines_x = FStar_Util.for_some (id_eq_lid x) def_ids  in
               if Prims.op_Negation defines_x
               then
                 let uu____472 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____472
                  then
                    let uu____491 =
                      let uu____497 =
                        let uu____499 =
                          let uu____501 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____501
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____499
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____497)
                       in
                    FStar_Errors.raise_error uu____491
                      impl.FStar_Parser_AST.drange
                  else (iface1, [qualify_kremlin_private impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y)))
                     in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____582) -> ([], iface2)
                    | (uu____593::uu____594,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____626 = aux ys iface_tl1  in
                          (match uu____626 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____659 =
                             let uu____661 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____661
                              in
                           if uu____659
                           then
                             let uu____676 =
                               let uu____682 =
                                 let uu____684 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____686 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____684 uu____686
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____682)
                                in
                             FStar_Errors.raise_error uu____676
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____700 = aux mutually_defined_with_x iface_tl  in
                  match uu____700 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____731 ->
               let uu____732 = prefix_with_iface_decls iface_tl impl  in
               (match uu____732 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____789,uu____790,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___2_830  ->
                       match uu___2_830 with
                       | (FStar_Parser_AST.TyconAbstract uu____838,uu____839)
                           -> true
                       | uu____855 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____867 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____867
               then
                 let uu____870 =
                   let uu____876 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____876)
                    in
                 FStar_Errors.raise_error uu____870
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____882 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____882
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____892 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____902 -> false
            | uu____904 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____937,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____954 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____954 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____992 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____1017 -> true
            | uu____1023 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1056 -> (iface1, [impl])
      | uu____1061 ->
          let uu____1062 = FStar_Options.ml_ish ()  in
          if uu____1062
          then ml_mode_prefix_with_iface_decls iface1 impl
          else prefix_with_iface_decls iface1 impl
  
let (initialize_interface :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list -> unit FStar_Syntax_DsEnv.withenv)
  =
  fun mname  ->
    fun l  ->
      fun env  ->
        let decls =
          let uu____1100 = FStar_Options.ml_ish ()  in
          if uu____1100
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____1107 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____1107 with
        | FStar_Pervasives_Native.Some uu____1116 ->
            let uu____1121 =
              let uu____1127 =
                let uu____1129 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____1129
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____1127)  in
            let uu____1133 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____1121 uu____1133
        | FStar_Pervasives_Native.None  ->
            let uu____1140 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____1140)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____1158 =
        let uu____1163 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____1163  in
      match uu____1158 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____1179 = prefix_one_decl iface1 impl  in
          (match uu____1179 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1205 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____1205 iface2  in
               (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1232 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1248 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1248 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1264 =
                   FStar_List.fold_left
                     (fun uu____1288  ->
                        fun impl  ->
                          match uu____1288 with
                          | (iface2,impls1) ->
                              let uu____1316 = prefix_one_decl iface2 impl
                                 in
                              (match uu____1316 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____1264 with
                  | (iface2,impls1) ->
                      let uu____1365 =
                        let uu____1374 =
                          FStar_Util.prefix_until
                            (fun uu___3_1393  ->
                               match uu___3_1393 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1395;
                                   FStar_Parser_AST.drange = uu____1396;
                                   FStar_Parser_AST.doc = uu____1397;
                                   FStar_Parser_AST.quals = uu____1398;
                                   FStar_Parser_AST.attrs = uu____1399;_} ->
                                   true
                               | uu____1407 -> false) iface2
                           in
                        match uu____1374 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1365 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____1474 = FStar_Options.interactive ()
                                in
                             if uu____1474
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1486::uu____1487 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1492 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1492
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1502 =
                                  let uu____1508 =
                                    let uu____1510 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1510 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1508)
                                   in
                                let uu____1514 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1502
                                  uu____1514
                            | uu____1519 -> (a1, env1)))))
  