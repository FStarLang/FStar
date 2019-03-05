open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____54996) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____54998 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____55013,uu____55014,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____55054  ->
                  match uu____55054 with
                  | (t,uu____55063) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____55069 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____55081,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____55095,uu____55096,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_55141  ->
                match uu___429_55141 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____55151,uu____55152,uu____55153),uu____55154) ->
                    let uu____55167 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55167]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____55169,uu____55170,uu____55171),uu____55172) ->
                    let uu____55205 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55205]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____55207,uu____55208,uu____55209),uu____55210) ->
                    let uu____55253 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55253]
                | uu____55254 -> []))
    | uu____55261 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____55274 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____55274
  
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
        let uu___495_55317 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_55317.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_55317.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_55317.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_55317.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55342,uu____55343,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_55383  ->
                       match uu___430_55383 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55391,uu____55392) -> true
                       | uu____55408 -> false))
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
                 let uu____55442 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____55442
                  then
                    let uu____55461 =
                      let uu____55467 =
                        let uu____55469 =
                          let uu____55471 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____55471
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____55469
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____55467)
                       in
                    FStar_Errors.raise_error uu____55461
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
                    | ([],uu____55552) -> ([], iface2)
                    | (uu____55563::uu____55564,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____55596 = aux ys iface_tl1  in
                          (match uu____55596 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____55629 =
                             let uu____55631 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____55631
                              in
                           if uu____55629
                           then
                             let uu____55646 =
                               let uu____55652 =
                                 let uu____55654 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____55656 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____55654 uu____55656
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____55652)
                                in
                             FStar_Errors.raise_error uu____55646
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____55670 = aux mutually_defined_with_x iface_tl  in
                  match uu____55670 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____55701 ->
               let uu____55702 = prefix_with_iface_decls iface_tl impl  in
               (match uu____55702 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55759,uu____55760,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_55800  ->
                       match uu___431_55800 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55808,uu____55809) -> true
                       | uu____55825 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____55837 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____55837
               then
                 let uu____55840 =
                   let uu____55846 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____55846)
                    in
                 FStar_Errors.raise_error uu____55840
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____55852 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____55852
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____55862 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____55872 -> false
            | uu____55874 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____55907,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____55924 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____55924 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____55962 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____55987 -> true
            | uu____55993 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____56026 -> (iface1, [impl])
      | uu____56031 ->
          let uu____56032 = FStar_Options.ml_ish ()  in
          if uu____56032
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
          let uu____56074 = FStar_Options.ml_ish ()  in
          if uu____56074
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____56081 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____56081 with
        | FStar_Pervasives_Native.Some uu____56090 ->
            let uu____56095 =
              let uu____56101 =
                let uu____56103 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____56103
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____56101)  in
            let uu____56107 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____56095 uu____56107
        | FStar_Pervasives_Native.None  ->
            let uu____56114 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____56114)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____56136 =
        let uu____56141 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____56141  in
      match uu____56136 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____56157 = prefix_one_decl iface1 impl  in
          (match uu____56157 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____56183 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____56183 iface2
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
        | FStar_Parser_AST.Interface uu____56214 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____56230 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____56230 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____56246 =
                   FStar_List.fold_left
                     (fun uu____56270  ->
                        fun impl  ->
                          match uu____56270 with
                          | (iface2,impls1) ->
                              let uu____56298 = prefix_one_decl iface2 impl
                                 in
                              (match uu____56298 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____56246 with
                  | (iface2,impls1) ->
                      let uu____56347 =
                        let uu____56356 =
                          FStar_Util.prefix_until
                            (fun uu___432_56375  ->
                               match uu___432_56375 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____56377;
                                   FStar_Parser_AST.drange = uu____56378;
                                   FStar_Parser_AST.doc = uu____56379;
                                   FStar_Parser_AST.quals = uu____56380;
                                   FStar_Parser_AST.attrs = uu____56381;_} ->
                                   true
                               | uu____56389 -> false) iface2
                           in
                        match uu____56356 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____56347 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____56456 = FStar_Options.interactive ()
                                in
                             if uu____56456
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____56468::uu____56469 when
                                expect_complete_modul ->
                                let err =
                                  let uu____56474 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____56474
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____56484 =
                                  let uu____56490 =
                                    let uu____56492 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____56492 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____56490)
                                   in
                                let uu____56496 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____56484
                                  uu____56496
                            | uu____56501 -> (a1, env1)))))
  