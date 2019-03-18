open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____50360) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____50362 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____50377,uu____50378,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____50418  ->
                  match uu____50418 with
                  | (t,uu____50427) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____50433 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____50445,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____50459,uu____50460,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_50505  ->
                match uu___429_50505 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____50515,uu____50516,uu____50517),uu____50518) ->
                    let uu____50531 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50531]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____50533,uu____50534,uu____50535),uu____50536) ->
                    let uu____50569 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50569]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____50571,uu____50572,uu____50573),uu____50574) ->
                    let uu____50617 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____50617]
                | uu____50618 -> []))
    | uu____50625 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____50638 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____50638
  
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
        let uu___495_50681 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_50681.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_50681.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_50681.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_50681.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____50706,uu____50707,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_50747  ->
                       match uu___430_50747 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____50755,uu____50756) -> true
                       | uu____50772 -> false))
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
                 let uu____50806 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____50806
                  then
                    let uu____50825 =
                      let uu____50831 =
                        let uu____50833 =
                          let uu____50835 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____50835
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____50833
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____50831)
                       in
                    FStar_Errors.raise_error uu____50825
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
                    | ([],uu____50916) -> ([], iface2)
                    | (uu____50927::uu____50928,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____50960 = aux ys iface_tl1  in
                          (match uu____50960 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____50993 =
                             let uu____50995 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____50995
                              in
                           if uu____50993
                           then
                             let uu____51010 =
                               let uu____51016 =
                                 let uu____51018 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____51020 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____51018 uu____51020
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____51016)
                                in
                             FStar_Errors.raise_error uu____51010
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____51034 = aux mutually_defined_with_x iface_tl  in
                  match uu____51034 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____51065 ->
               let uu____51066 = prefix_with_iface_decls iface_tl impl  in
               (match uu____51066 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____51123,uu____51124,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_51164  ->
                       match uu___431_51164 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____51172,uu____51173) -> true
                       | uu____51189 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____51201 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____51201
               then
                 let uu____51204 =
                   let uu____51210 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____51210)
                    in
                 FStar_Errors.raise_error uu____51204
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____51216 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____51216
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____51226 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____51236 -> false
            | uu____51238 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____51271,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____51288 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____51288 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____51326 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____51351 -> true
            | uu____51357 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____51390 -> (iface1, [impl])
      | uu____51395 ->
          let uu____51396 = FStar_Options.ml_ish ()  in
          if uu____51396
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
          let uu____51434 = FStar_Options.ml_ish ()  in
          if uu____51434
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____51441 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____51441 with
        | FStar_Pervasives_Native.Some uu____51450 ->
            let uu____51455 =
              let uu____51461 =
                let uu____51463 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____51463
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____51461)  in
            let uu____51467 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____51455 uu____51467
        | FStar_Pervasives_Native.None  ->
            let uu____51474 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____51474)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____51492 =
        let uu____51497 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____51497  in
      match uu____51492 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____51513 = prefix_one_decl iface1 impl  in
          (match uu____51513 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____51539 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____51539 iface2
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
        | FStar_Parser_AST.Interface uu____51566 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____51582 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____51582 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____51598 =
                   FStar_List.fold_left
                     (fun uu____51622  ->
                        fun impl  ->
                          match uu____51622 with
                          | (iface2,impls1) ->
                              let uu____51650 = prefix_one_decl iface2 impl
                                 in
                              (match uu____51650 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____51598 with
                  | (iface2,impls1) ->
                      let uu____51699 =
                        let uu____51708 =
                          FStar_Util.prefix_until
                            (fun uu___432_51727  ->
                               match uu___432_51727 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____51729;
                                   FStar_Parser_AST.drange = uu____51730;
                                   FStar_Parser_AST.doc = uu____51731;
                                   FStar_Parser_AST.quals = uu____51732;
                                   FStar_Parser_AST.attrs = uu____51733;_} ->
                                   true
                               | uu____51741 -> false) iface2
                           in
                        match uu____51708 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____51699 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____51808 = FStar_Options.interactive ()
                                in
                             if uu____51808
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____51820::uu____51821 when
                                expect_complete_modul ->
                                let err =
                                  let uu____51826 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____51826
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____51836 =
                                  let uu____51842 =
                                    let uu____51844 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____51844 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____51842)
                                   in
                                let uu____51848 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____51836
                                  uu____51848
                            | uu____51853 -> (a1, env1)))))
  