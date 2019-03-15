open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____50361) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____50363 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____50378,uu____50379,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____50419  ->
                  match uu____50419 with
                  | (t,uu____50428) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____50434 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____50446,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____50460,uu____50461,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_50506  ->
                match uu___429_50506 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____50516,uu____50517,uu____50518),uu____50519) ->
                    let uu____50532 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50532]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____50534,uu____50535,uu____50536),uu____50537) ->
                    let uu____50570 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50570]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____50572,uu____50573,uu____50574),uu____50575) ->
                    let uu____50618 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50618]
                | uu____50619 -> []))
    | uu____50626 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____50639 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____50639
  
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
        let uu___495_50682 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_50682.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_50682.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_50682.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_50682.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____50707,uu____50708,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_50748  ->
                       match uu___430_50748 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____50756,uu____50757) -> true
                       | uu____50773 -> false))
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
                 let uu____50807 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____50807
                  then
                    let uu____50826 =
                      let uu____50832 =
                        let uu____50834 =
                          let uu____50836 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____50836
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____50834
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____50832)
                       in
                    FStar_Errors.raise_error uu____50826
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
                    | ([],uu____50917) -> ([], iface2)
                    | (uu____50928::uu____50929,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____50961 = aux ys iface_tl1  in
                          (match uu____50961 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____50994 =
                             let uu____50996 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____50996
                              in
                           if uu____50994
                           then
                             let uu____51011 =
                               let uu____51017 =
                                 let uu____51019 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____51021 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____51019 uu____51021
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____51017)
                                in
                             FStar_Errors.raise_error uu____51011
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____51035 = aux mutually_defined_with_x iface_tl  in
                  match uu____51035 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____51066 ->
               let uu____51067 = prefix_with_iface_decls iface_tl impl  in
               (match uu____51067 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____51124,uu____51125,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_51165  ->
                       match uu___431_51165 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____51173,uu____51174) -> true
                       | uu____51190 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____51202 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____51202
               then
                 let uu____51205 =
                   let uu____51211 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____51211)
                    in
                 FStar_Errors.raise_error uu____51205
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____51217 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____51217
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____51227 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____51237 -> false
            | uu____51239 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____51272,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____51289 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____51289 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____51327 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____51352 -> true
            | uu____51358 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____51391 -> (iface1, [impl])
      | uu____51396 ->
          let uu____51397 = FStar_Options.ml_ish ()  in
          if uu____51397
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
          let uu____51435 = FStar_Options.ml_ish ()  in
          if uu____51435
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____51442 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____51442 with
        | FStar_Pervasives_Native.Some uu____51451 ->
            let uu____51456 =
              let uu____51462 =
                let uu____51464 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____51464
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____51462)  in
            let uu____51468 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____51456 uu____51468
        | FStar_Pervasives_Native.None  ->
            let uu____51475 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____51475)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____51493 =
        let uu____51498 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____51498  in
      match uu____51493 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____51514 = prefix_one_decl iface1 impl  in
          (match uu____51514 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____51540 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____51540 iface2
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
        | FStar_Parser_AST.Interface uu____51567 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____51583 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____51583 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____51599 =
                   FStar_List.fold_left
                     (fun uu____51623  ->
                        fun impl  ->
                          match uu____51623 with
                          | (iface2,impls1) ->
                              let uu____51651 = prefix_one_decl iface2 impl
                                 in
                              (match uu____51651 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____51599 with
                  | (iface2,impls1) ->
                      let uu____51700 =
                        let uu____51709 =
                          FStar_Util.prefix_until
                            (fun uu___432_51728  ->
                               match uu___432_51728 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____51730;
                                   FStar_Parser_AST.drange = uu____51731;
                                   FStar_Parser_AST.doc = uu____51732;
                                   FStar_Parser_AST.quals = uu____51733;
                                   FStar_Parser_AST.attrs = uu____51734;_} ->
                                   true
                               | uu____51742 -> false) iface2
                           in
                        match uu____51709 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____51700 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____51809 = FStar_Options.interactive ()
                                in
                             if uu____51809
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____51821::uu____51822 when
                                expect_complete_modul ->
                                let err =
                                  let uu____51827 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____51827
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____51837 =
                                  let uu____51843 =
                                    let uu____51845 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____51845 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____51843)
                                   in
                                let uu____51849 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____51837
                                  uu____51849
                            | uu____51854 -> (a1, env1)))))
  