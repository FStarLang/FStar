open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____22) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____23 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____34,uu____35,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____70  ->
                  match uu____70 with
                  | (t,uu____78) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____83 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____93,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____107,uu____108,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___176_149  ->
                match uu___176_149 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____159,uu____160,uu____161),uu____162) ->
                    let uu____175 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____175]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____177,uu____178,uu____179),uu____180) ->
                    let uu____213 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____213]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____215,uu____216,uu____217),uu____218) ->
                    let uu____259 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____259]
                | uu____260 -> []))
    | uu____267 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____278 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____278
  
let rec (prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
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
        let uu___180_318 = impl1  in
        {
          FStar_Parser_AST.d = (uu___180_318.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___180_318.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___180_318.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___180_318.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____343,uu____344,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___177_379  ->
                       match uu___177_379 with
                       | (FStar_Parser_AST.TyconAbstract uu____386,uu____387)
                           -> true
                       | uu____402 -> false))
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
                 let uu____431 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____431
                  then
                    let uu____446 =
                      let uu____451 =
                        let uu____452 =
                          let uu____453 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____453
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____452
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____451)
                       in
                    FStar_Errors.raise_error uu____446
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
                    | ([],uu____524) -> ([], iface2)
                    | (uu____535::uu____536,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____567 = aux ys iface_tl1  in
                          (match uu____567 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____599 =
                             let uu____600 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____600
                              in
                           if uu____599
                           then
                             let uu____613 =
                               let uu____618 =
                                 let uu____619 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____620 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____619 uu____620
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____618)
                                in
                             FStar_Errors.raise_error uu____613
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____630 = aux mutually_defined_with_x iface_tl  in
                  match uu____630 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____661 ->
               let uu____662 = prefix_with_iface_decls iface_tl impl  in
               (match uu____662 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____718,uu____719,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___178_754  ->
                       match uu___178_754 with
                       | (FStar_Parser_AST.TyconAbstract uu____761,uu____762)
                           -> true
                       | uu____777 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____786 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____786
               then
                 let uu____787 =
                   let uu____792 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____792)
                    in
                 FStar_Errors.raise_error uu____787
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____794 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____794
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____798 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____807 -> false
            | uu____808 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____839,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____856 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____856 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____893 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____916 -> true
            | uu____921 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____952 -> (iface1, [impl])
      | uu____957 ->
          let uu____958 = FStar_Options.ml_ish ()  in
          if uu____958
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
          let uu____996 = FStar_Options.ml_ish ()  in
          if uu____996
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____1000 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____1000 with
        | FStar_Pervasives_Native.Some uu____1009 ->
            let uu____1014 =
              let uu____1019 =
                let uu____1020 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____1020
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____1019)  in
            let uu____1021 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____1014 uu____1021
        | FStar_Pervasives_Native.None  ->
            let uu____1028 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____1028)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____1049 =
        let uu____1054 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____1054  in
      match uu____1049 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____1070 = prefix_one_decl iface1 impl  in
          (match uu____1070 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1096 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____1096 iface2  in
               (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1124 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1139 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1139 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1155 =
                   FStar_List.fold_left
                     (fun uu____1179  ->
                        fun impl  ->
                          match uu____1179 with
                          | (iface2,impls1) ->
                              let uu____1207 = prefix_one_decl iface2 impl
                                 in
                              (match uu____1207 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____1155 with
                  | (iface2,impls1) ->
                      let uu____1256 =
                        let uu____1265 =
                          FStar_Util.prefix_until
                            (fun uu___179_1284  ->
                               match uu___179_1284 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1285;
                                   FStar_Parser_AST.drange = uu____1286;
                                   FStar_Parser_AST.doc = uu____1287;
                                   FStar_Parser_AST.quals = uu____1288;
                                   FStar_Parser_AST.attrs = uu____1289;_} ->
                                   true
                               | uu____1296 -> false) iface2
                           in
                        match uu____1265 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1256 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             FStar_Syntax_DsEnv.set_iface_decls env l
                               remaining_iface_vals
                              in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1369::uu____1370 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1374 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1374
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1379 =
                                  let uu____1384 =
                                    let uu____1385 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1385 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1384)
                                   in
                                let uu____1386 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1379
                                  uu____1386
                            | uu____1391 -> (a1, env1)))))
  