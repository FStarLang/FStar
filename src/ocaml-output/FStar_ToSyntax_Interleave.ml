open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____54923) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____54925 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____54940,uu____54941,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____54981  ->
                  match uu____54981 with
                  | (t,uu____54990) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____54996 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____55008,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____55022,uu____55023,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_55068  ->
                match uu___429_55068 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____55078,uu____55079,uu____55080),uu____55081) ->
                    let uu____55094 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55094]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____55096,uu____55097,uu____55098),uu____55099) ->
                    let uu____55132 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55132]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____55134,uu____55135,uu____55136),uu____55137) ->
                    let uu____55180 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55180]
                | uu____55181 -> []))
    | uu____55188 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____55201 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____55201
  
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
        let uu___495_55244 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_55244.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_55244.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_55244.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_55244.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55269,uu____55270,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_55310  ->
                       match uu___430_55310 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55318,uu____55319) -> true
                       | uu____55335 -> false))
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
                 let uu____55369 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____55369
                  then
                    let uu____55388 =
                      let uu____55394 =
                        let uu____55396 =
                          let uu____55398 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____55398
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____55396
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____55394)
                       in
                    FStar_Errors.raise_error uu____55388
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
                    | ([],uu____55479) -> ([], iface2)
                    | (uu____55490::uu____55491,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____55523 = aux ys iface_tl1  in
                          (match uu____55523 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____55556 =
                             let uu____55558 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____55558
                              in
                           if uu____55556
                           then
                             let uu____55573 =
                               let uu____55579 =
                                 let uu____55581 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____55583 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____55581 uu____55583
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____55579)
                                in
                             FStar_Errors.raise_error uu____55573
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____55597 = aux mutually_defined_with_x iface_tl  in
                  match uu____55597 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____55628 ->
               let uu____55629 = prefix_with_iface_decls iface_tl impl  in
               (match uu____55629 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55686,uu____55687,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_55727  ->
                       match uu___431_55727 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55735,uu____55736) -> true
                       | uu____55752 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____55764 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____55764
               then
                 let uu____55767 =
                   let uu____55773 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____55773)
                    in
                 FStar_Errors.raise_error uu____55767
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____55779 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____55779
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____55789 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____55799 -> false
            | uu____55801 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____55834,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____55851 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____55851 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____55889 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____55914 -> true
            | uu____55920 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____55953 -> (iface1, [impl])
      | uu____55958 ->
          let uu____55959 = FStar_Options.ml_ish ()  in
          if uu____55959
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
          let uu____56001 = FStar_Options.ml_ish ()  in
          if uu____56001
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____56008 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____56008 with
        | FStar_Pervasives_Native.Some uu____56017 ->
            let uu____56022 =
              let uu____56028 =
                let uu____56030 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____56030
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____56028)  in
            let uu____56034 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____56022 uu____56034
        | FStar_Pervasives_Native.None  ->
            let uu____56041 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____56041)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____56063 =
        let uu____56068 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____56068  in
      match uu____56063 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____56084 = prefix_one_decl iface1 impl  in
          (match uu____56084 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____56110 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____56110 iface2
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
        | FStar_Parser_AST.Interface uu____56141 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____56157 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____56157 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____56173 =
                   FStar_List.fold_left
                     (fun uu____56197  ->
                        fun impl  ->
                          match uu____56197 with
                          | (iface2,impls1) ->
                              let uu____56225 = prefix_one_decl iface2 impl
                                 in
                              (match uu____56225 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____56173 with
                  | (iface2,impls1) ->
                      let uu____56274 =
                        let uu____56283 =
                          FStar_Util.prefix_until
                            (fun uu___432_56302  ->
                               match uu___432_56302 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____56304;
                                   FStar_Parser_AST.drange = uu____56305;
                                   FStar_Parser_AST.doc = uu____56306;
                                   FStar_Parser_AST.quals = uu____56307;
                                   FStar_Parser_AST.attrs = uu____56308;_} ->
                                   true
                               | uu____56316 -> false) iface2
                           in
                        match uu____56283 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____56274 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____56383 = FStar_Options.interactive ()
                                in
                             if uu____56383
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____56395::uu____56396 when
                                expect_complete_modul ->
                                let err =
                                  let uu____56401 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____56401
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____56411 =
                                  let uu____56417 =
                                    let uu____56419 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____56419 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____56417)
                                   in
                                let uu____56423 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____56411
                                  uu____56423
                            | uu____56428 -> (a1, env1)))))
  