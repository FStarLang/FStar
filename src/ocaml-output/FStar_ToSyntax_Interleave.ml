open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____54987) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____54989 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____55004,uu____55005,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____55045  ->
                  match uu____55045 with
                  | (t,uu____55054) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____55060 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____55072,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____55086,uu____55087,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_55132  ->
                match uu___429_55132 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____55142,uu____55143,uu____55144),uu____55145) ->
                    let uu____55158 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55158]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____55160,uu____55161,uu____55162),uu____55163) ->
                    let uu____55196 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55196]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____55198,uu____55199,uu____55200),uu____55201) ->
                    let uu____55244 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55244]
                | uu____55245 -> []))
    | uu____55252 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____55265 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____55265
  
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
        let uu___495_55308 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_55308.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_55308.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_55308.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_55308.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55333,uu____55334,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_55374  ->
                       match uu___430_55374 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55382,uu____55383) -> true
                       | uu____55399 -> false))
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
                 let uu____55433 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____55433
                  then
                    let uu____55452 =
                      let uu____55458 =
                        let uu____55460 =
                          let uu____55462 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____55462
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____55460
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____55458)
                       in
                    FStar_Errors.raise_error uu____55452
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
                    | ([],uu____55543) -> ([], iface2)
                    | (uu____55554::uu____55555,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____55587 = aux ys iface_tl1  in
                          (match uu____55587 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____55620 =
                             let uu____55622 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____55622
                              in
                           if uu____55620
                           then
                             let uu____55637 =
                               let uu____55643 =
                                 let uu____55645 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____55647 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____55645 uu____55647
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____55643)
                                in
                             FStar_Errors.raise_error uu____55637
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____55661 = aux mutually_defined_with_x iface_tl  in
                  match uu____55661 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____55692 ->
               let uu____55693 = prefix_with_iface_decls iface_tl impl  in
               (match uu____55693 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55750,uu____55751,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_55791  ->
                       match uu___431_55791 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55799,uu____55800) -> true
                       | uu____55816 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____55828 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____55828
               then
                 let uu____55831 =
                   let uu____55837 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____55837)
                    in
                 FStar_Errors.raise_error uu____55831
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____55843 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____55843
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____55853 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____55863 -> false
            | uu____55865 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____55898,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____55915 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____55915 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____55953 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____55978 -> true
            | uu____55984 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____56017 -> (iface1, [impl])
      | uu____56022 ->
          let uu____56023 = FStar_Options.ml_ish ()  in
          if uu____56023
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
          let uu____56065 = FStar_Options.ml_ish ()  in
          if uu____56065
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____56072 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____56072 with
        | FStar_Pervasives_Native.Some uu____56081 ->
            let uu____56086 =
              let uu____56092 =
                let uu____56094 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____56094
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____56092)  in
            let uu____56098 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____56086 uu____56098
        | FStar_Pervasives_Native.None  ->
            let uu____56105 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____56105)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____56127 =
        let uu____56132 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____56132  in
      match uu____56127 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____56148 = prefix_one_decl iface1 impl  in
          (match uu____56148 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____56174 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____56174 iface2
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
        | FStar_Parser_AST.Interface uu____56205 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____56221 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____56221 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____56237 =
                   FStar_List.fold_left
                     (fun uu____56261  ->
                        fun impl  ->
                          match uu____56261 with
                          | (iface2,impls1) ->
                              let uu____56289 = prefix_one_decl iface2 impl
                                 in
                              (match uu____56289 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____56237 with
                  | (iface2,impls1) ->
                      let uu____56338 =
                        let uu____56347 =
                          FStar_Util.prefix_until
                            (fun uu___432_56366  ->
                               match uu___432_56366 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____56368;
                                   FStar_Parser_AST.drange = uu____56369;
                                   FStar_Parser_AST.doc = uu____56370;
                                   FStar_Parser_AST.quals = uu____56371;
                                   FStar_Parser_AST.attrs = uu____56372;_} ->
                                   true
                               | uu____56380 -> false) iface2
                           in
                        match uu____56347 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____56338 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____56447 = FStar_Options.interactive ()
                                in
                             if uu____56447
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____56459::uu____56460 when
                                expect_complete_modul ->
                                let err =
                                  let uu____56465 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____56465
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____56475 =
                                  let uu____56481 =
                                    let uu____56483 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____56483 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____56481)
                                   in
                                let uu____56487 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____56475
                                  uu____56487
                            | uu____56492 -> (a1, env1)))))
  