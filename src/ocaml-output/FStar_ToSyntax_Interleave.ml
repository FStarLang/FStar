open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____55001) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____55003 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____55018,uu____55019,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____55059  ->
                  match uu____55059 with
                  | (t,uu____55068) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____55074 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____55086,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____55100,uu____55101,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_55146  ->
                match uu___429_55146 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____55156,uu____55157,uu____55158),uu____55159) ->
                    let uu____55172 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55172]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____55174,uu____55175,uu____55176),uu____55177) ->
                    let uu____55210 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55210]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____55212,uu____55213,uu____55214),uu____55215) ->
                    let uu____55258 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55258]
                | uu____55259 -> []))
    | uu____55266 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____55279 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____55279
  
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
        let uu___495_55322 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_55322.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_55322.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_55322.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_55322.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55347,uu____55348,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_55388  ->
                       match uu___430_55388 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55396,uu____55397) -> true
                       | uu____55413 -> false))
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
                 let uu____55447 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____55447
                  then
                    let uu____55466 =
                      let uu____55472 =
                        let uu____55474 =
                          let uu____55476 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____55476
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____55474
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____55472)
                       in
                    FStar_Errors.raise_error uu____55466
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
                    | ([],uu____55557) -> ([], iface2)
                    | (uu____55568::uu____55569,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____55601 = aux ys iface_tl1  in
                          (match uu____55601 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____55634 =
                             let uu____55636 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____55636
                              in
                           if uu____55634
                           then
                             let uu____55651 =
                               let uu____55657 =
                                 let uu____55659 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____55661 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____55659 uu____55661
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____55657)
                                in
                             FStar_Errors.raise_error uu____55651
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____55675 = aux mutually_defined_with_x iface_tl  in
                  match uu____55675 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____55706 ->
               let uu____55707 = prefix_with_iface_decls iface_tl impl  in
               (match uu____55707 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55764,uu____55765,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_55805  ->
                       match uu___431_55805 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55813,uu____55814) -> true
                       | uu____55830 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____55842 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____55842
               then
                 let uu____55845 =
                   let uu____55851 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____55851)
                    in
                 FStar_Errors.raise_error uu____55845
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____55857 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____55857
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____55867 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____55877 -> false
            | uu____55879 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____55912,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____55929 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____55929 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____55967 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____55992 -> true
            | uu____55998 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____56031 -> (iface1, [impl])
      | uu____56036 ->
          let uu____56037 = FStar_Options.ml_ish ()  in
          if uu____56037
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
          let uu____56079 = FStar_Options.ml_ish ()  in
          if uu____56079
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____56086 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____56086 with
        | FStar_Pervasives_Native.Some uu____56095 ->
            let uu____56100 =
              let uu____56106 =
                let uu____56108 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____56108
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____56106)  in
            let uu____56112 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____56100 uu____56112
        | FStar_Pervasives_Native.None  ->
            let uu____56119 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____56119)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____56141 =
        let uu____56146 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____56146  in
      match uu____56141 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____56162 = prefix_one_decl iface1 impl  in
          (match uu____56162 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____56188 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____56188 iface2
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
        | FStar_Parser_AST.Interface uu____56219 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____56235 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____56235 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____56251 =
                   FStar_List.fold_left
                     (fun uu____56275  ->
                        fun impl  ->
                          match uu____56275 with
                          | (iface2,impls1) ->
                              let uu____56303 = prefix_one_decl iface2 impl
                                 in
                              (match uu____56303 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____56251 with
                  | (iface2,impls1) ->
                      let uu____56352 =
                        let uu____56361 =
                          FStar_Util.prefix_until
                            (fun uu___432_56380  ->
                               match uu___432_56380 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____56382;
                                   FStar_Parser_AST.drange = uu____56383;
                                   FStar_Parser_AST.doc = uu____56384;
                                   FStar_Parser_AST.quals = uu____56385;
                                   FStar_Parser_AST.attrs = uu____56386;_} ->
                                   true
                               | uu____56394 -> false) iface2
                           in
                        match uu____56361 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____56352 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____56461 = FStar_Options.interactive ()
                                in
                             if uu____56461
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____56473::uu____56474 when
                                expect_complete_modul ->
                                let err =
                                  let uu____56479 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____56479
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____56489 =
                                  let uu____56495 =
                                    let uu____56497 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____56497 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____56495)
                                   in
                                let uu____56501 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____56489
                                  uu____56501
                            | uu____56506 -> (a1, env1)))))
  