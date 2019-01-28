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
             (fun uu___175_172  ->
                match uu___175_172 with
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
  
let (wrap_iface_decl_with_admit_smt :
  FStar_Parser_AST.decl -> FStar_Parser_AST.decl Prims.list) =
  fun d  ->
    let mk_decl1 d1 = FStar_Parser_AST.mk_decl d1 FStar_Range.dummyRange []
       in
    let admit_smt_queries1 = "--admit_smt_queries true"  in
    let push_admit_smt_queries =
      mk_decl1
        (FStar_Parser_AST.Pragma
           (FStar_Parser_AST.PushOptions
              (FStar_Pervasives_Native.Some admit_smt_queries1)))
       in
    let pop1 = mk_decl1 (FStar_Parser_AST.Pragma FStar_Parser_AST.PopOptions)
       in
    [push_admit_smt_queries; d; pop1]
  
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
        let uu___179_370 = impl1  in
        {
          FStar_Parser_AST.d = (uu___179_370.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___179_370.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___179_370.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___179_370.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____395,uu____396,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___176_436  ->
                       match uu___176_436 with
                       | (FStar_Parser_AST.TyconAbstract uu____444,uu____445)
                           -> true
                       | uu____461 -> false))
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
                 let uu____495 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____495
                  then
                    let uu____514 =
                      let uu____520 =
                        let uu____522 =
                          let uu____524 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____524
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____522
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____520)
                       in
                    FStar_Errors.raise_error uu____514
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
                    | ([],uu____605) -> ([], iface2)
                    | (uu____616::uu____617,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____649 = aux ys iface_tl1  in
                          (match uu____649 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____682 =
                             let uu____684 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____684
                              in
                           if uu____682
                           then
                             let uu____699 =
                               let uu____705 =
                                 let uu____707 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____709 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____707 uu____709
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____705)
                                in
                             FStar_Errors.raise_error uu____699
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____723 = aux mutually_defined_with_x iface_tl  in
                  match uu____723 with
                  | (take_iface,rest_iface) ->
                      let uu____750 =
                        let uu____753 =
                          wrap_iface_decl_with_admit_smt iface_hd  in
                        FStar_List.append uu____753
                          (FStar_List.append take_iface [impl])
                         in
                      (rest_iface, uu____750))
           | uu____760 ->
               let uu____761 = prefix_with_iface_decls iface_tl impl  in
               (match uu____761 with
                | (iface2,ds) ->
                    let uu____788 =
                      let uu____791 = wrap_iface_decl_with_admit_smt iface_hd
                         in
                      FStar_List.append uu____791 ds  in
                    (iface2, uu____788)))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____824,uu____825,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___177_865  ->
                       match uu___177_865 with
                       | (FStar_Parser_AST.TyconAbstract uu____873,uu____874)
                           -> true
                       | uu____890 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____902 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____902
               then
                 let uu____905 =
                   let uu____911 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____911)
                    in
                 FStar_Errors.raise_error uu____905
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____917 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____917
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____927 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____937 -> false
            | uu____939 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____972,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____989 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____989 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____1027 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____1052 -> true
            | uu____1058 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____1091 -> (iface1, [impl])
      | uu____1096 ->
          let uu____1097 = FStar_Options.ml_ish ()  in
          if uu____1097
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
          let uu____1139 = FStar_Options.ml_ish ()  in
          if uu____1139
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____1146 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____1146 with
        | FStar_Pervasives_Native.Some uu____1155 ->
            let uu____1160 =
              let uu____1166 =
                let uu____1168 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____1168
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____1166)  in
            let uu____1172 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____1160 uu____1172
        | FStar_Pervasives_Native.None  ->
            let uu____1179 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____1179)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____1201 =
        let uu____1206 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____1206  in
      match uu____1201 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____1222 = prefix_one_decl iface1 impl  in
          (match uu____1222 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1248 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____1248 iface2  in
               (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1279 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1295 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1295 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1311 =
                   FStar_List.fold_left
                     (fun uu____1335  ->
                        fun impl  ->
                          match uu____1335 with
                          | (iface2,impls1) ->
                              let uu____1363 = prefix_one_decl iface2 impl
                                 in
                              (match uu____1363 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____1311 with
                  | (iface2,impls1) ->
                      let uu____1412 =
                        let uu____1421 =
                          FStar_Util.prefix_until
                            (fun uu___178_1440  ->
                               match uu___178_1440 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1442;
                                   FStar_Parser_AST.drange = uu____1443;
                                   FStar_Parser_AST.doc = uu____1444;
                                   FStar_Parser_AST.quals = uu____1445;
                                   FStar_Parser_AST.attrs = uu____1446;_} ->
                                   true
                               | uu____1454 -> false) iface2
                           in
                        match uu____1421 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1412 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 =
                             let uu____1520 =
                               FStar_List.fold_left
                                 (fun accum  ->
                                    fun iface_let  ->
                                      let uu____1532 =
                                        wrap_iface_decl_with_admit_smt
                                          iface_let
                                         in
                                      FStar_List.append accum uu____1532) []
                                 iface_lets
                                in
                             FStar_List.append impls1 uu____1520  in
                           let env1 =
                             let uu____1536 = FStar_Options.interactive ()
                                in
                             if uu____1536
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1548::uu____1549 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1554 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1554
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1564 =
                                  let uu____1570 =
                                    let uu____1572 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1572 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1570)
                                   in
                                let uu____1576 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1564
                                  uu____1576
                            | uu____1581 -> (a1, env1)))))
  