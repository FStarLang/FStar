open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____54918) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____54920 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____54935,uu____54936,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____54976  ->
                  match uu____54976 with
                  | (t,uu____54985) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____54991 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____55003,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____55017,uu____55018,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_55063  ->
                match uu___429_55063 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____55073,uu____55074,uu____55075),uu____55076) ->
                    let uu____55089 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55089]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____55091,uu____55092,uu____55093),uu____55094) ->
                    let uu____55127 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55127]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____55129,uu____55130,uu____55131),uu____55132) ->
                    let uu____55175 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____55175]
                | uu____55176 -> []))
    | uu____55183 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____55196 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____55196
  
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
        let uu___495_55239 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_55239.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_55239.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_55239.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_55239.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55264,uu____55265,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_55305  ->
                       match uu___430_55305 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55313,uu____55314) -> true
                       | uu____55330 -> false))
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
                 let uu____55364 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____55364
                  then
                    let uu____55383 =
                      let uu____55389 =
                        let uu____55391 =
                          let uu____55393 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____55393
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____55391
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____55389)
                       in
                    FStar_Errors.raise_error uu____55383
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
                    | ([],uu____55474) -> ([], iface2)
                    | (uu____55485::uu____55486,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____55518 = aux ys iface_tl1  in
                          (match uu____55518 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____55551 =
                             let uu____55553 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____55553
                              in
                           if uu____55551
                           then
                             let uu____55568 =
                               let uu____55574 =
                                 let uu____55576 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____55578 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____55576 uu____55578
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____55574)
                                in
                             FStar_Errors.raise_error uu____55568
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____55592 = aux mutually_defined_with_x iface_tl  in
                  match uu____55592 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____55623 ->
               let uu____55624 = prefix_with_iface_decls iface_tl impl  in
               (match uu____55624 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____55681,uu____55682,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_55722  ->
                       match uu___431_55722 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____55730,uu____55731) -> true
                       | uu____55747 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____55759 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____55759
               then
                 let uu____55762 =
                   let uu____55768 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____55768)
                    in
                 FStar_Errors.raise_error uu____55762
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____55774 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____55774
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____55784 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____55794 -> false
            | uu____55796 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____55829,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____55846 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____55846 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____55884 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____55909 -> true
            | uu____55915 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____55948 -> (iface1, [impl])
      | uu____55953 ->
          let uu____55954 = FStar_Options.ml_ish ()  in
          if uu____55954
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
          let uu____55996 = FStar_Options.ml_ish ()  in
          if uu____55996
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____56003 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____56003 with
        | FStar_Pervasives_Native.Some uu____56012 ->
            let uu____56017 =
              let uu____56023 =
                let uu____56025 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____56025
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____56023)  in
            let uu____56029 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____56017 uu____56029
        | FStar_Pervasives_Native.None  ->
            let uu____56036 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____56036)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____56058 =
        let uu____56063 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____56063  in
      match uu____56058 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____56079 = prefix_one_decl iface1 impl  in
          (match uu____56079 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____56105 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____56105 iface2
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
        | FStar_Parser_AST.Interface uu____56136 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____56152 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____56152 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____56168 =
                   FStar_List.fold_left
                     (fun uu____56192  ->
                        fun impl  ->
                          match uu____56192 with
                          | (iface2,impls1) ->
                              let uu____56220 = prefix_one_decl iface2 impl
                                 in
                              (match uu____56220 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____56168 with
                  | (iface2,impls1) ->
                      let uu____56269 =
                        let uu____56278 =
                          FStar_Util.prefix_until
                            (fun uu___432_56297  ->
                               match uu___432_56297 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____56299;
                                   FStar_Parser_AST.drange = uu____56300;
                                   FStar_Parser_AST.doc = uu____56301;
                                   FStar_Parser_AST.quals = uu____56302;
                                   FStar_Parser_AST.attrs = uu____56303;_} ->
                                   true
                               | uu____56311 -> false) iface2
                           in
                        match uu____56278 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____56269 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____56378 = FStar_Options.interactive ()
                                in
                             if uu____56378
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____56390::uu____56391 when
                                expect_complete_modul ->
                                let err =
                                  let uu____56396 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____56396
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____56406 =
                                  let uu____56412 =
                                    let uu____56414 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____56414 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____56412)
                                   in
                                let uu____56418 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____56406
                                  uu____56418
                            | uu____56423 -> (a1, env1)))))
  