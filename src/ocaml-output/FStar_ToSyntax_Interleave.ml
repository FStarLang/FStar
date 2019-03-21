open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____50394) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____50396 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____50411,uu____50412,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____50452  ->
                  match uu____50452 with
                  | (t,uu____50461) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____50467 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____50479,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____50493,uu____50494,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_50539  ->
                match uu___429_50539 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____50549,uu____50550,uu____50551),uu____50552) ->
                    let uu____50565 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50565]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____50567,uu____50568,uu____50569),uu____50570) ->
                    let uu____50603 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50603]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____50605,uu____50606,uu____50607),uu____50608) ->
                    let uu____50651 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50651]
                | uu____50652 -> []))
    | uu____50659 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____50672 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____50672
  
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
        let uu___495_50715 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_50715.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_50715.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_50715.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_50715.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____50740,uu____50741,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_50781  ->
                       match uu___430_50781 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____50789,uu____50790) -> true
                       | uu____50806 -> false))
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
                 let uu____50840 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____50840
                  then
                    let uu____50859 =
                      let uu____50865 =
                        let uu____50867 =
                          let uu____50869 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____50869
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____50867
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____50865)
                       in
                    FStar_Errors.raise_error uu____50859
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
                    | ([],uu____50950) -> ([], iface2)
                    | (uu____50961::uu____50962,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____50994 = aux ys iface_tl1  in
                          (match uu____50994 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____51027 =
                             let uu____51029 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____51029
                              in
                           if uu____51027
                           then
                             let uu____51044 =
                               let uu____51050 =
                                 let uu____51052 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____51054 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____51052 uu____51054
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____51050)
                                in
                             FStar_Errors.raise_error uu____51044
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____51068 = aux mutually_defined_with_x iface_tl  in
                  match uu____51068 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____51099 ->
               let uu____51100 = prefix_with_iface_decls iface_tl impl  in
               (match uu____51100 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____51157,uu____51158,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_51198  ->
                       match uu___431_51198 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____51206,uu____51207) -> true
                       | uu____51223 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____51235 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____51235
               then
                 let uu____51238 =
                   let uu____51244 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____51244)
                    in
                 FStar_Errors.raise_error uu____51238
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____51250 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____51250
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____51260 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____51270 -> false
            | uu____51272 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____51305,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____51322 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____51322 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____51360 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____51385 -> true
            | uu____51391 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____51424 -> (iface1, [impl])
      | uu____51429 ->
          let uu____51430 = FStar_Options.ml_ish ()  in
          if uu____51430
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
          let uu____51468 = FStar_Options.ml_ish ()  in
          if uu____51468
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____51475 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____51475 with
        | FStar_Pervasives_Native.Some uu____51484 ->
            let uu____51489 =
              let uu____51495 =
                let uu____51497 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____51497
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____51495)  in
            let uu____51501 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____51489 uu____51501
        | FStar_Pervasives_Native.None  ->
            let uu____51508 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____51508)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____51526 =
        let uu____51531 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____51531  in
      match uu____51526 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____51547 = prefix_one_decl iface1 impl  in
          (match uu____51547 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____51573 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____51573 iface2
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
        | FStar_Parser_AST.Interface uu____51600 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____51616 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____51616 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____51632 =
                   FStar_List.fold_left
                     (fun uu____51656  ->
                        fun impl  ->
                          match uu____51656 with
                          | (iface2,impls1) ->
                              let uu____51684 = prefix_one_decl iface2 impl
                                 in
                              (match uu____51684 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____51632 with
                  | (iface2,impls1) ->
                      let uu____51733 =
                        let uu____51742 =
                          FStar_Util.prefix_until
                            (fun uu___432_51761  ->
                               match uu___432_51761 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____51763;
                                   FStar_Parser_AST.drange = uu____51764;
                                   FStar_Parser_AST.doc = uu____51765;
                                   FStar_Parser_AST.quals = uu____51766;
                                   FStar_Parser_AST.attrs = uu____51767;_} ->
                                   true
                               | uu____51775 -> false) iface2
                           in
                        match uu____51742 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____51733 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____51842 = FStar_Options.interactive ()
                                in
                             if uu____51842
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____51854::uu____51855 when
                                expect_complete_modul ->
                                let err =
                                  let uu____51860 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____51860
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____51870 =
                                  let uu____51876 =
                                    let uu____51878 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____51878 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____51876)
                                   in
                                let uu____51882 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____51870
                                  uu____51882
                            | uu____51887 -> (a1, env1)))))
  