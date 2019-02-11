open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____27) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____29 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____44,uu____45,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____85  ->
                  match uu____85 with
                  | (t,uu____94) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____100 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____112,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____126,uu____127,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___176_172  ->
                match uu___176_172 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____182,uu____183,uu____184),uu____185) ->
                    let uu____198 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____198]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____200,uu____201,uu____202),uu____203) ->
                    let uu____236 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____236]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____238,uu____239,uu____240),uu____241) ->
                    let uu____284 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____284]
                | uu____285 -> []))
    | uu____292 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____305 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____305
  
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
        let uu___180_348 = impl1  in
        {
          FStar_Parser_AST.d = (uu___180_348.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___180_348.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___180_348.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___180_348.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____373,uu____374,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___177_414  ->
                       match uu___177_414 with
                       | (FStar_Parser_AST.TyconAbstract uu____422,uu____423)
                           -> true
                       | uu____439 -> false))
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
                 let uu____473 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____473
                  then
                    let uu____492 =
                      let uu____498 =
                        let uu____500 =
                          let uu____502 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____502
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____500
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____498)
                       in
                    FStar_Errors.raise_error uu____492
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
                    | ([],uu____583) -> ([], iface2)
                    | (uu____594::uu____595,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____627 = aux ys iface_tl1  in
                          (match uu____627 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____660 =
                             let uu____662 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____662
                              in
                           if uu____660
                           then
                             let uu____677 =
                               let uu____683 =
                                 let uu____685 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____687 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____685 uu____687
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____683)
                                in
                             FStar_Errors.raise_error uu____677
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____701 = aux mutually_defined_with_x iface_tl  in
                  match uu____701 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____732 ->
               let uu____733 = prefix_with_iface_decls iface_tl impl  in
               (match uu____733 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____790,uu____791,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___178_831  ->
                       match uu___178_831 with
                       | (FStar_Parser_AST.TyconAbstract uu____839,uu____840)
                           -> true
                       | uu____856 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____868 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____868
               then
                 let uu____871 =
                   let uu____877 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____877)
                    in
                 FStar_Errors.raise_error uu____871
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____883 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____883
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____893 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____903 -> false
            | uu____905 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____938,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____955 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____955 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____993 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____1018 -> true
            | uu____1024 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1057 -> (iface1, [impl])
      | uu____1062 ->
          let uu____1063 = FStar_Options.ml_ish ()  in
          if uu____1063
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
          let uu____1105 = FStar_Options.ml_ish ()  in
          if uu____1105
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____1112 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____1112 with
        | FStar_Pervasives_Native.Some uu____1121 ->
            let uu____1126 =
              let uu____1132 =
                let uu____1134 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____1134
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____1132)  in
            let uu____1138 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____1126 uu____1138
        | FStar_Pervasives_Native.None  ->
            let uu____1145 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____1145)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____1167 =
        let uu____1172 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____1172  in
      match uu____1167 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____1188 = prefix_one_decl iface1 impl  in
          (match uu____1188 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1214 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____1214 iface2  in
               (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1245 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1261 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1261 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1277 =
                   FStar_List.fold_left
                     (fun uu____1301  ->
                        fun impl  ->
                          match uu____1301 with
                          | (iface2,impls1) ->
                              let uu____1329 = prefix_one_decl iface2 impl
                                 in
                              (match uu____1329 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____1277 with
                  | (iface2,impls1) ->
                      let uu____1378 =
                        let uu____1387 =
                          FStar_Util.prefix_until
                            (fun uu___179_1406  ->
                               match uu___179_1406 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1408;
                                   FStar_Parser_AST.drange = uu____1409;
                                   FStar_Parser_AST.doc = uu____1410;
                                   FStar_Parser_AST.quals = uu____1411;
                                   FStar_Parser_AST.attrs = uu____1412;_} ->
                                   true
                               | uu____1420 -> false) iface2
                           in
                        match uu____1387 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1378 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____1487 = FStar_Options.interactive ()
                                in
                             if uu____1487
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1499::uu____1500 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1505 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1505
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1515 =
                                  let uu____1521 =
                                    let uu____1523 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1523 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1521)
                                   in
                                let uu____1527 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1515
                                  uu____1527
                            | uu____1532 -> (a1, env1)))))
  