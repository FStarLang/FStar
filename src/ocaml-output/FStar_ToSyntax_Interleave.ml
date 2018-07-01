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
      | FStar_Parser_AST.Tycon (uu____34,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____69  ->
                  match uu____69 with
                  | (t,uu____77) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____82 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____92,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____106,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___166_147  ->
                match uu___166_147 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____157,uu____158,uu____159),uu____160) ->
                    let uu____173 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____173]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____175,uu____176,uu____177),uu____178) ->
                    let uu____211 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____211]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____213,uu____214,uu____215),uu____216) ->
                    let uu____257 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____257]
                | uu____258 -> []))
    | uu____265 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____276 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____276
  
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
        let uu___170_316 = impl1  in
        {
          FStar_Parser_AST.d = (uu___170_316.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___170_316.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___170_316.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___170_316.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____341,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___167_376  ->
                       match uu___167_376 with
                       | (FStar_Parser_AST.TyconAbstract uu____383,uu____384)
                           -> true
                       | uu____399 -> false))
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
                 let uu____428 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____428
                  then
                    let uu____443 =
                      let uu____448 =
                        let uu____449 =
                          let uu____450 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____450
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____449
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____448)
                       in
                    FStar_Errors.raise_error uu____443
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
                    | ([],uu____521) -> ([], iface2)
                    | (uu____532::uu____533,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____564 = aux ys iface_tl1  in
                          (match uu____564 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____596 =
                             let uu____597 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____597
                              in
                           if uu____596
                           then
                             let uu____610 =
                               let uu____615 =
                                 let uu____616 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____617 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____616 uu____617
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____615)
                                in
                             FStar_Errors.raise_error uu____610
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____627 = aux mutually_defined_with_x iface_tl  in
                  match uu____627 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____658 ->
               let uu____659 = prefix_with_iface_decls iface_tl impl  in
               (match uu____659 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____715,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___168_750  ->
                       match uu___168_750 with
                       | (FStar_Parser_AST.TyconAbstract uu____757,uu____758)
                           -> true
                       | uu____773 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____782 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____782
               then
                 let uu____783 =
                   let uu____788 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____788)
                    in
                 FStar_Errors.raise_error uu____783
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____790 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____790
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____794 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____803 -> false
            | uu____804 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____835,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____852 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____852 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____889 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____912 -> true
            | uu____917 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____948 -> (iface1, [impl])
      | uu____953 ->
          let uu____954 = FStar_Options.ml_ish ()  in
          if uu____954
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
          let uu____992 = FStar_Options.ml_ish ()  in
          if uu____992
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____996 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____996 with
        | FStar_Pervasives_Native.Some uu____1005 ->
            let uu____1010 =
              let uu____1015 =
                let uu____1016 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____1016
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____1015)  in
            let uu____1017 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____1010 uu____1017
        | FStar_Pervasives_Native.None  ->
            let uu____1024 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____1024)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____1045 =
        let uu____1050 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____1050  in
      match uu____1045 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____1066 = prefix_one_decl iface1 impl  in
          (match uu____1066 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1092 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____1092 iface2  in
               (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1120 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1135 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1135 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1151 =
                   FStar_List.fold_left
                     (fun uu____1175  ->
                        fun impl  ->
                          match uu____1175 with
                          | (iface2,impls1) ->
                              let uu____1203 = prefix_one_decl iface2 impl
                                 in
                              (match uu____1203 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____1151 with
                  | (iface2,impls1) ->
                      let uu____1252 =
                        let uu____1261 =
                          FStar_Util.prefix_until
                            (fun uu___169_1280  ->
                               match uu___169_1280 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1281;
                                   FStar_Parser_AST.drange = uu____1282;
                                   FStar_Parser_AST.doc = uu____1283;
                                   FStar_Parser_AST.quals = uu____1284;
                                   FStar_Parser_AST.attrs = uu____1285;_} ->
                                   true
                               | uu____1292 -> false) iface2
                           in
                        match uu____1261 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1252 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             FStar_Syntax_DsEnv.set_iface_decls env l
                               remaining_iface_vals
                              in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1365::uu____1366 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1370 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1370
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1375 =
                                  let uu____1380 =
                                    let uu____1381 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1381 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1380)
                                   in
                                let uu____1382 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1375
                                  uu____1382
                            | uu____1387 -> (a1, env1)))))
  