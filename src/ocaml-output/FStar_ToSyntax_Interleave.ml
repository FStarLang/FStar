open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____50393) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____50395 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____50410,uu____50411,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____50451  ->
                  match uu____50451 with
                  | (t,uu____50460) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____50466 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____50478,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____50492,uu____50493,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_50538  ->
                match uu___429_50538 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____50548,uu____50549,uu____50550),uu____50551) ->
                    let uu____50564 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50564]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____50566,uu____50567,uu____50568),uu____50569) ->
                    let uu____50602 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50602]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____50604,uu____50605,uu____50606),uu____50607) ->
                    let uu____50650 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50650]
                | uu____50651 -> []))
    | uu____50658 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____50671 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____50671
  
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
        let uu___495_50714 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_50714.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_50714.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_50714.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_50714.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____50739,uu____50740,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_50780  ->
                       match uu___430_50780 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____50788,uu____50789) -> true
                       | uu____50805 -> false))
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
                 let uu____50839 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____50839
                  then
                    let uu____50858 =
                      let uu____50864 =
                        let uu____50866 =
                          let uu____50868 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____50868
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____50866
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____50864)
                       in
                    FStar_Errors.raise_error uu____50858
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
                    | ([],uu____50949) -> ([], iface2)
                    | (uu____50960::uu____50961,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____50993 = aux ys iface_tl1  in
                          (match uu____50993 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____51026 =
                             let uu____51028 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____51028
                              in
                           if uu____51026
                           then
                             let uu____51043 =
                               let uu____51049 =
                                 let uu____51051 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____51053 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____51051 uu____51053
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____51049)
                                in
                             FStar_Errors.raise_error uu____51043
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____51067 = aux mutually_defined_with_x iface_tl  in
                  match uu____51067 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____51098 ->
               let uu____51099 = prefix_with_iface_decls iface_tl impl  in
               (match uu____51099 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____51156,uu____51157,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_51197  ->
                       match uu___431_51197 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____51205,uu____51206) -> true
                       | uu____51222 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____51234 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____51234
               then
                 let uu____51237 =
                   let uu____51243 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____51243)
                    in
                 FStar_Errors.raise_error uu____51237
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____51249 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____51249
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____51259 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____51269 -> false
            | uu____51271 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____51304,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____51321 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____51321 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____51359 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____51384 -> true
            | uu____51390 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____51423 -> (iface1, [impl])
      | uu____51428 ->
          let uu____51429 = FStar_Options.ml_ish ()  in
          if uu____51429
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
          let uu____51467 = FStar_Options.ml_ish ()  in
          if uu____51467
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____51474 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____51474 with
        | FStar_Pervasives_Native.Some uu____51483 ->
            let uu____51488 =
              let uu____51494 =
                let uu____51496 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____51496
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____51494)  in
            let uu____51500 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____51488 uu____51500
        | FStar_Pervasives_Native.None  ->
            let uu____51507 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____51507)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____51525 =
        let uu____51530 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____51530  in
      match uu____51525 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____51546 = prefix_one_decl iface1 impl  in
          (match uu____51546 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____51572 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____51572 iface2
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
        | FStar_Parser_AST.Interface uu____51599 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____51615 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____51615 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____51631 =
                   FStar_List.fold_left
                     (fun uu____51655  ->
                        fun impl  ->
                          match uu____51655 with
                          | (iface2,impls1) ->
                              let uu____51683 = prefix_one_decl iface2 impl
                                 in
                              (match uu____51683 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____51631 with
                  | (iface2,impls1) ->
                      let uu____51732 =
                        let uu____51741 =
                          FStar_Util.prefix_until
                            (fun uu___432_51760  ->
                               match uu___432_51760 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____51762;
                                   FStar_Parser_AST.drange = uu____51763;
                                   FStar_Parser_AST.doc = uu____51764;
                                   FStar_Parser_AST.quals = uu____51765;
                                   FStar_Parser_AST.attrs = uu____51766;_} ->
                                   true
                               | uu____51774 -> false) iface2
                           in
                        match uu____51741 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____51732 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____51841 = FStar_Options.interactive ()
                                in
                             if uu____51841
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____51853::uu____51854 when
                                expect_complete_modul ->
                                let err =
                                  let uu____51859 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____51859
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____51869 =
                                  let uu____51875 =
                                    let uu____51877 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____51877 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____51875)
                                   in
                                let uu____51881 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____51869
                                  uu____51881
                            | uu____51886 -> (a1, env1)))))
  