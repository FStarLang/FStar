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
  
let (definition_lids :
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
    | uu____184 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____197 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____197
  
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
        let uu___58_240 = impl1  in
        {
          FStar_Parser_AST.d = (uu___58_240.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___58_240.FStar_Parser_AST.drange);
          FStar_Parser_AST.quals = (uu___58_240.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____265,uu____266,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___1_281  ->
                       match uu___1_281 with
                       | FStar_Parser_AST.TyconAbstract uu____283 -> true
                       | uu____295 -> false))
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
                 let uu____323 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____323
                  then
                    let uu____342 =
                      let uu____348 =
                        let uu____350 =
                          let uu____352 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____352
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____350
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____348)
                       in
                    FStar_Errors.raise_error uu____342
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
                    | ([],uu____433) -> ([], iface2)
                    | (uu____444::uu____445,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____477 = aux ys iface_tl1  in
                          (match uu____477 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____510 =
                             let uu____512 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____512
                              in
                           if uu____510
                           then
                             let uu____527 =
                               let uu____533 =
                                 let uu____535 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____537 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____535 uu____537
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____533)
                                in
                             FStar_Errors.raise_error uu____527
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____551 = aux mutually_defined_with_x iface_tl  in
                  match uu____551 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | FStar_Parser_AST.Pragma uu____582 ->
               prefix_with_iface_decls iface_tl impl
           | uu____583 ->
               let uu____584 = prefix_with_iface_decls iface_tl impl  in
               (match uu____584 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____641,uu____642,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___2_657  ->
                       match uu___2_657 with
                       | FStar_Parser_AST.TyconAbstract uu____659 -> true
                       | uu____671 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____677 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____677
               then
                 let uu____680 =
                   let uu____686 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____686)
                    in
                 FStar_Errors.raise_error uu____680
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____692 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____692
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____702 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____712 -> false
            | uu____714 -> true))
  
let (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____747,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____764 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____764 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____802 -> (iface1, [impl])
  
let ml_mode_check_initial_interface :
  'uuuuuu814 .
    'uuuuuu814 ->
      FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list
  =
  fun mname  ->
    fun iface1  ->
      FStar_All.pipe_right iface1
        (FStar_List.filter
           (fun d  ->
              match d.FStar_Parser_AST.d with
              | FStar_Parser_AST.Val uu____839 -> true
              | uu____845 -> false))
  
let (ulib_modules : Prims.string Prims.list) =
  ["FStar.TSet";
  "FStar.Seq.Base";
  "FStar.Seq.Properties";
  "FStar.UInt";
  "FStar.UInt8";
  "FStar.UInt16";
  "FStar.UInt32";
  "FStar.UInt64";
  "FStar.Int";
  "FStar.Int8";
  "FStar.Int16";
  "FStar.Int32";
  "FStar.Int64"] 
let (apply_ml_mode_optimizations : FStar_Ident.lident -> Prims.bool) =
  fun mname  ->
    ((FStar_Options.ml_ish ()) &&
       (let uu____887 =
          let uu____889 = FStar_Ident.string_of_lid mname  in
          FStar_List.contains uu____889 FStar_Parser_Dep.core_modules  in
        Prims.op_Negation uu____887))
      &&
      (let uu____893 =
         let uu____895 = FStar_Ident.string_of_lid mname  in
         FStar_List.contains uu____895 ulib_modules  in
       Prims.op_Negation uu____893)
  
let (prefix_one_decl :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list ->
      FStar_Parser_AST.decl ->
        (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun mname  ->
    fun iface1  ->
      fun impl  ->
        match impl.FStar_Parser_AST.d with
        | FStar_Parser_AST.TopLevelModule uu____934 -> (iface1, [impl])
        | uu____939 ->
            let uu____940 = apply_ml_mode_optimizations mname  in
            if uu____940
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
          let uu____978 = apply_ml_mode_optimizations mname  in
          if uu____978
          then ml_mode_check_initial_interface mname l
          else check_initial_interface l  in
        let uu____985 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____985 with
        | FStar_Pervasives_Native.Some uu____994 ->
            let uu____999 =
              let uu____1005 =
                let uu____1007 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____1007
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____1005)  in
            let uu____1011 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____999 uu____1011
        | FStar_Pervasives_Native.None  ->
            let uu____1018 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____1018)
  
let (prefix_with_interface_decls :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun mname  ->
    fun impl  ->
      fun env  ->
        let uu____1041 =
          let uu____1046 = FStar_Syntax_DsEnv.current_module env  in
          FStar_Syntax_DsEnv.iface_decls env uu____1046  in
        match uu____1041 with
        | FStar_Pervasives_Native.None  -> ([impl], env)
        | FStar_Pervasives_Native.Some iface1 ->
            let uu____1062 = prefix_one_decl mname iface1 impl  in
            (match uu____1062 with
             | (iface2,impl1) ->
                 let env1 =
                   let uu____1088 = FStar_Syntax_DsEnv.current_module env  in
                   FStar_Syntax_DsEnv.set_iface_decls env uu____1088 iface2
                    in
                 (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____1115 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1131 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1131 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1147 =
                   FStar_List.fold_left
                     (fun uu____1171  ->
                        fun impl  ->
                          match uu____1171 with
                          | (iface2,impls1) ->
                              let uu____1199 = prefix_one_decl l iface2 impl
                                 in
                              (match uu____1199 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____1147 with
                  | (iface2,impls1) ->
                      let uu____1248 =
                        let uu____1257 =
                          FStar_Util.prefix_until
                            (fun uu___3_1275  ->
                               match uu___3_1275 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1277;
                                   FStar_Parser_AST.drange = uu____1278;
                                   FStar_Parser_AST.quals = uu____1279;
                                   FStar_Parser_AST.attrs = uu____1280;_} ->
                                   true
                               | uu____1286 -> false) iface2
                           in
                        match uu____1257 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1248 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____1353 = FStar_Options.interactive ()
                                in
                             if uu____1353
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1365::uu____1366 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1371 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1371
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1381 =
                                  let uu____1387 =
                                    let uu____1389 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1389 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1387)
                                   in
                                let uu____1393 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1381
                                  uu____1393
                            | uu____1398 -> (a1, env1)))))
  