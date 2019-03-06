open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____51092) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____51094 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____51109,uu____51110,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____51150  ->
                  match uu____51150 with
                  | (t,uu____51159) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____51165 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____51177,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____51191,uu____51192,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___429_51237  ->
                match uu___429_51237 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____51247,uu____51248,uu____51249),uu____51250) ->
                    let uu____51263 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____51263]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____51265,uu____51266,uu____51267),uu____51268) ->
                    let uu____51301 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____51301]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____51303,uu____51304,uu____51305),uu____51306) ->
                    let uu____51349 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____51349]
                | uu____51350 -> []))
    | uu____51357 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____51370 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____51370
  
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
        let uu___495_51413 = impl1  in
        {
          FStar_Parser_AST.d = (uu___495_51413.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___495_51413.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___495_51413.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___495_51413.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____51438,uu____51439,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___430_51479  ->
                       match uu___430_51479 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____51487,uu____51488) -> true
                       | uu____51504 -> false))
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
                 let uu____51538 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____51538
                  then
                    let uu____51557 =
                      let uu____51563 =
                        let uu____51565 =
                          let uu____51567 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____51567
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____51565
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____51563)
                       in
                    FStar_Errors.raise_error uu____51557
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
                    | ([],uu____51648) -> ([], iface2)
                    | (uu____51659::uu____51660,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____51692 = aux ys iface_tl1  in
                          (match uu____51692 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____51725 =
                             let uu____51727 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____51727
                              in
                           if uu____51725
                           then
                             let uu____51742 =
                               let uu____51748 =
                                 let uu____51750 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____51752 =
                                   FStar_Ident.string_of_lid y  in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____51750 uu____51752
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____51748)
                                in
                             FStar_Errors.raise_error uu____51742
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____51766 = aux mutually_defined_with_x iface_tl  in
                  match uu____51766 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____51797 ->
               let uu____51798 = prefix_with_iface_decls iface_tl impl  in
               (match uu____51798 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____51855,uu____51856,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___431_51896  ->
                       match uu___431_51896 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____51904,uu____51905) -> true
                       | uu____51921 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____51933 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____51933
               then
                 let uu____51936 =
                   let uu____51942 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____51942)
                    in
                 FStar_Errors.raise_error uu____51936
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____51948 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____51948
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____51958 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____51968 -> false
            | uu____51970 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____52003,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____52020 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____52020 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____52058 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____52083 -> true
            | uu____52089 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____52122 -> (iface1, [impl])
      | uu____52127 ->
          let uu____52128 = FStar_Options.ml_ish ()  in
          if uu____52128
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
          let uu____52166 = FStar_Options.ml_ish ()  in
          if uu____52166
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____52173 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____52173 with
        | FStar_Pervasives_Native.Some uu____52182 ->
            let uu____52187 =
              let uu____52193 =
                let uu____52195 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____52195
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____52193)  in
            let uu____52199 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____52187 uu____52199
        | FStar_Pervasives_Native.None  ->
            let uu____52206 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____52206)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____52224 =
        let uu____52229 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____52229  in
      match uu____52224 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____52245 = prefix_one_decl iface1 impl  in
          (match uu____52245 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____52271 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____52271 iface2
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
        | FStar_Parser_AST.Interface uu____52298 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____52314 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____52314 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____52330 =
                   FStar_List.fold_left
                     (fun uu____52354  ->
                        fun impl  ->
                          match uu____52354 with
                          | (iface2,impls1) ->
                              let uu____52382 = prefix_one_decl iface2 impl
                                 in
                              (match uu____52382 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____52330 with
                  | (iface2,impls1) ->
                      let uu____52431 =
                        let uu____52440 =
                          FStar_Util.prefix_until
                            (fun uu___432_52459  ->
                               match uu___432_52459 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____52461;
                                   FStar_Parser_AST.drange = uu____52462;
                                   FStar_Parser_AST.doc = uu____52463;
                                   FStar_Parser_AST.quals = uu____52464;
                                   FStar_Parser_AST.attrs = uu____52465;_} ->
                                   true
                               | uu____52473 -> false) iface2
                           in
                        match uu____52440 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____52431 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____52540 = FStar_Options.interactive ()
                                in
                             if uu____52540
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____52552::uu____52553 when
                                expect_complete_modul ->
                                let err =
                                  let uu____52558 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____52558
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____52568 =
                                  let uu____52574 =
                                    let uu____52576 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____52576 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____52574)
                                   in
                                let uu____52580 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____52568
                                  uu____52580
                            | uu____52585 -> (a1, env1)))))
  