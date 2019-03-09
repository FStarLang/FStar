open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____50374) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____50376 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____50391,uu____50392,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____50432  ->
                  match uu____50432 with
                  | (t,uu____50441) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____50447 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____50459,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____50473,uu____50474,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_50519  ->
                match uu___429_50519 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____50529,uu____50530,uu____50531),uu____50532) ->
                    let uu____50545 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50545]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____50547,uu____50548,uu____50549),uu____50550) ->
                    let uu____50583 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50583]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____50585,uu____50586,uu____50587),uu____50588) ->
                    let uu____50631 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50631]
                | uu____50632 -> []))
    | uu____50639 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____50652 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____50652
  
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
        let uu___495_50695 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_50695.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_50695.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_50695.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_50695.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____50720,uu____50721,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_50761  ->
                       match uu___430_50761 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____50769,uu____50770) -> true
                       | uu____50786 -> false))
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
                 let uu____50820 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____50820
                  then
                    let uu____50839 =
                      let uu____50845 =
                        let uu____50847 =
                          let uu____50849 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____50849
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____50847
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____50845)
                       in
                    FStar_Errors.raise_error uu____50839
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
                    | ([],uu____50930) -> ([], iface2)
                    | (uu____50941::uu____50942,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____50974 = aux ys iface_tl1  in
                          (match uu____50974 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____51007 =
                             let uu____51009 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____51009
                              in
                           if uu____51007
                           then
                             let uu____51024 =
                               let uu____51030 =
                                 let uu____51032 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____51034 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____51032 uu____51034
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____51030)
                                in
                             FStar_Errors.raise_error uu____51024
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____51048 = aux mutually_defined_with_x iface_tl  in
                  match uu____51048 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____51079 ->
               let uu____51080 = prefix_with_iface_decls iface_tl impl  in
               (match uu____51080 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____51137,uu____51138,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_51178  ->
                       match uu___431_51178 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____51186,uu____51187) -> true
                       | uu____51203 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____51215 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____51215
               then
                 let uu____51218 =
                   let uu____51224 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____51224)
                    in
                 FStar_Errors.raise_error uu____51218
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____51230 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____51230
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____51240 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____51250 -> false
            | uu____51252 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____51285,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____51302 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____51302 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____51340 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____51365 -> true
            | uu____51371 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____51404 -> (iface1, [impl])
      | uu____51409 ->
          let uu____51410 = FStar_Options.ml_ish ()  in
          if uu____51410
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
          let uu____51448 = FStar_Options.ml_ish ()  in
          if uu____51448
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____51455 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____51455 with
        | FStar_Pervasives_Native.Some uu____51464 ->
            let uu____51469 =
              let uu____51475 =
                let uu____51477 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____51477
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____51475)  in
            let uu____51481 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____51469 uu____51481
        | FStar_Pervasives_Native.None  ->
            let uu____51488 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____51488)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____51506 =
        let uu____51511 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____51511  in
      match uu____51506 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____51527 = prefix_one_decl iface1 impl  in
          (match uu____51527 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____51553 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____51553 iface2
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
        | FStar_Parser_AST.Interface uu____51580 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____51596 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____51596 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____51612 =
                   FStar_List.fold_left
                     (fun uu____51636  ->
                        fun impl  ->
                          match uu____51636 with
                          | (iface2,impls1) ->
                              let uu____51664 = prefix_one_decl iface2 impl
                                 in
                              (match uu____51664 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____51612 with
                  | (iface2,impls1) ->
                      let uu____51713 =
                        let uu____51722 =
                          FStar_Util.prefix_until
                            (fun uu___432_51741  ->
                               match uu___432_51741 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____51743;
                                   FStar_Parser_AST.drange = uu____51744;
                                   FStar_Parser_AST.doc = uu____51745;
                                   FStar_Parser_AST.quals = uu____51746;
                                   FStar_Parser_AST.attrs = uu____51747;_} ->
                                   true
                               | uu____51755 -> false) iface2
                           in
                        match uu____51722 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____51713 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____51822 = FStar_Options.interactive ()
                                in
                             if uu____51822
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____51834::uu____51835 when
                                expect_complete_modul ->
                                let err =
                                  let uu____51840 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____51840
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____51850 =
                                  let uu____51856 =
                                    let uu____51858 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____51858 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____51856)
                                   in
                                let uu____51862 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____51850
                                  uu____51862
                            | uu____51867 -> (a1, env1)))))
  