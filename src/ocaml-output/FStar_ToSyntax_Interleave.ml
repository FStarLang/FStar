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
               (fun t  ->
                  (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____60 -> false
  
let rec (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____72,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____86,uu____87,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___0_107  ->
                match uu___0_107 with
                | FStar_Parser_AST.TyconAbbrev
                    (id1,uu____111,uu____112,uu____113) ->
                    let uu____122 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____122]
                | FStar_Parser_AST.TyconRecord
                    (id1,uu____124,uu____125,uu____126) ->
                    let uu____147 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____147]
                | FStar_Parser_AST.TyconVariant
                    (id1,uu____149,uu____150,uu____151) ->
                    let uu____182 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____182]
                | uu____183 -> []))
    | FStar_Parser_AST.Fail (uu____184,uu____185,se) -> definition_lids se
    | uu____195 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____208 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____208
  
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
        let uu___63_251 = impl1  in
        {
          FStar_Parser_AST.d = (uu___63_251.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___63_251.FStar_Parser_AST.drange);
          FStar_Parser_AST.quals = (uu___63_251.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____276,uu____277,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___1_292  ->
                       match uu___1_292 with
                       | FStar_Parser_AST.TyconAbstract uu____294 -> true
                       | uu____306 -> false))
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
                 let uu____334 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____334
                  then
                    let uu____353 =
                      let uu____359 =
                        let uu____361 =
                          let uu____363 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____363
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____361
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____359)
                       in
                    FStar_Errors.raise_error uu____353
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
                    | ([],uu____444) -> ([], iface2)
                    | (uu____455::uu____456,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____488 = aux ys iface_tl1  in
                          (match uu____488 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____521 =
                             let uu____523 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____523
                              in
                           if uu____521
                           then
                             let uu____538 =
                               let uu____544 =
                                 let uu____546 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____548 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____546 uu____548
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____544)
                                in
                             FStar_Errors.raise_error uu____538
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____562 = aux mutually_defined_with_x iface_tl  in
                  match uu____562 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | FStar_Parser_AST.Pragma uu____593 ->
               prefix_with_iface_decls iface_tl impl
           | uu____594 ->
               let uu____595 = prefix_with_iface_decls iface_tl impl  in
               (match uu____595 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____652,uu____653,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___2_668  ->
                       match uu___2_668 with
                       | FStar_Parser_AST.TyconAbstract uu____670 -> true
                       | uu____682 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____688 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____688
               then
                 let uu____691 =
                   let uu____697 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____697)
                    in
                 FStar_Errors.raise_error uu____691
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____703 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____703
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____713 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____723 -> false
            | uu____725 -> true))
  
let (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____758,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____775 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____775 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____813 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____838 -> true
            | uu____844 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____877 -> (iface1, [impl])
      | uu____882 ->
          let uu____883 = FStar_Options.ml_ish ()  in
          if uu____883
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
          let uu____921 = FStar_Options.ml_ish ()  in
          if uu____921
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____928 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____928 with
        | FStar_Pervasives_Native.Some uu____937 ->
            let uu____942 =
              let uu____948 =
                let uu____950 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____950
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____948)  in
            let uu____954 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____942 uu____954
        | FStar_Pervasives_Native.None  ->
            let uu____961 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____961)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____979 =
        let uu____984 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____984  in
      match uu____979 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____1000 = prefix_one_decl iface1 impl  in
          (match uu____1000 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____1026 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____1026 iface2  in
               (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1053 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1069 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1069 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1085 =
                   FStar_List.fold_left
                     (fun uu____1109  ->
                        fun impl  ->
                          match uu____1109 with
                          | (iface2,impls1) ->
                              let uu____1137 = prefix_one_decl iface2 impl
                                 in
                              (match uu____1137 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____1085 with
                  | (iface2,impls1) ->
                      let uu____1186 =
                        let uu____1195 =
                          FStar_Util.prefix_until
                            (fun uu___3_1213  ->
                               match uu___3_1213 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1215;
                                   FStar_Parser_AST.drange = uu____1216;
                                   FStar_Parser_AST.quals = uu____1217;
                                   FStar_Parser_AST.attrs = uu____1218;_} ->
                                   true
                               | uu____1224 -> false) iface2
                           in
                        match uu____1195 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1186 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____1291 = FStar_Options.interactive ()
                                in
                             if uu____1291
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1303::uu____1304 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1309 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1309
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1319 =
                                  let uu____1325 =
                                    let uu____1327 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1327 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1325)
                                   in
                                let uu____1331 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1319
                                  uu____1331
                            | uu____1336 -> (a1, env1)))))
  