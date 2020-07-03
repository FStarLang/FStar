open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i ->
    fun l ->
      let uu____10 = FStar_Ident.string_of_id i in
      let uu____11 =
        let uu____12 = FStar_Ident.ident_of_lid l in
        FStar_Ident.string_of_id uu____12 in
      uu____10 = uu____11
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x ->
    fun d ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y, uu____24) ->
          let uu____25 = FStar_Ident.string_of_id x in
          let uu____26 = FStar_Ident.string_of_id y in uu____25 = uu____26
      | uu____27 -> false
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x ->
    fun d ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____38, uu____39, tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun t ->
                  let uu____51 = FStar_Parser_AST.id_of_tycon t in
                  let uu____52 = FStar_Ident.string_of_id x in
                  uu____51 = uu____52))
      | uu____53 -> false
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____63, defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____77, uu____78, tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___0_94 ->
                match uu___0_94 with
                | FStar_Parser_AST.TyconAbbrev
                    (id, uu____98, uu____99, uu____100) ->
                    let uu____109 = FStar_Ident.lid_of_ids [id] in
                    [uu____109]
                | FStar_Parser_AST.TyconRecord
                    (id, uu____111, uu____112, uu____113) ->
                    let uu____134 = FStar_Ident.lid_of_ids [id] in
                    [uu____134]
                | FStar_Parser_AST.TyconVariant
                    (id, uu____136, uu____137, uu____138) ->
                    let uu____167 = FStar_Ident.lid_of_ids [id] in
                    [uu____167]
                | uu____168 -> []))
    | uu____169 -> []
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x ->
    fun d ->
      let uu____180 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____180
let rec (prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface ->
    fun impl ->
      let qualify_kremlin_private impl1 =
        let krem_private =
          FStar_Parser_AST.mk_term
            (FStar_Parser_AST.Const
               (FStar_Const.Const_string
                  ("KremlinPrivate", (impl1.FStar_Parser_AST.drange))))
            impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr in
        let uu___58_220 = impl1 in
        {
          FStar_Parser_AST.d = (uu___58_220.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___58_220.FStar_Parser_AST.drange);
          FStar_Parser_AST.quals = (uu___58_220.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        } in
      match iface with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____245, uu____246, tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___1_256 ->
                       match uu___1_256 with
                       | FStar_Parser_AST.TyconAbstract uu____257 -> true
                       | uu____268 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 impl.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x, t) ->
               let def_ids = definition_lids impl in
               let defines_x = FStar_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 let uu____291 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y ->
                           let uu____297 =
                             let uu____304 =
                               let uu____309 = FStar_Ident.ident_of_lid y in
                               is_val uu____309 in
                             FStar_Util.for_some uu____304 in
                           FStar_All.pipe_right iface_tl uu____297)) in
                 (if uu____291
                  then
                    let uu____320 =
                      let uu____325 =
                        let uu____326 = FStar_Ident.string_of_id x in
                        let uu____327 =
                          let uu____328 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid) in
                          FStar_All.pipe_right uu____328
                            (FStar_String.concat ", ") in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          uu____326 uu____327 in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____325) in
                    FStar_Errors.raise_error uu____320
                      impl.FStar_Parser_AST.drange
                  else (iface, [qualify_kremlin_private impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y ->
                            let uu____361 = id_eq_lid x y in
                            Prims.op_Negation uu____361)) in
                  let rec aux mutuals iface1 =
                    match (mutuals, iface1) with
                    | ([], uu____401) -> ([], iface1)
                    | (uu____412::uu____413, []) -> ([], [])
                    | (y::ys, iface_hd1::iface_tl1) ->
                        let uu____436 =
                          let uu____437 = FStar_Ident.ident_of_lid y in
                          is_val uu____437 iface_hd1 in
                        if uu____436
                        then
                          let uu____446 = aux ys iface_tl1 in
                          (match uu____446 with
                           | (val_ys, iface2) ->
                               ((iface_hd1 :: val_ys), iface2))
                        else
                          (let uu____478 =
                             let uu____479 =
                               let uu____482 =
                                 let uu____487 = FStar_Ident.ident_of_lid y in
                                 is_val uu____487 in
                               FStar_List.tryFind uu____482 iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____479 in
                           if uu____478
                           then
                             let uu____498 =
                               let uu____503 =
                                 let uu____504 =
                                   FStar_Parser_AST.decl_to_string iface_hd1 in
                                 let uu____505 = FStar_Ident.string_of_lid y in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____504 uu____505 in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____503) in
                             FStar_Errors.raise_error uu____498
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface1) in
                  let uu____515 = aux mutually_defined_with_x iface_tl in
                  match uu____515 with
                  | (take_iface, rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | FStar_Parser_AST.Pragma uu____546 ->
               prefix_with_iface_decls iface_tl impl
           | uu____547 ->
               let uu____548 = prefix_with_iface_decls iface_tl impl in
               (match uu____548 with
                | (iface1, ds) -> (iface1, (iface_hd :: ds))))
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface ->
    let rec aux iface1 =
      match iface1 with
      | [] -> ()
      | hd::tl ->
          (match hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____604, uu____605, tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___2_615 ->
                       match uu___2_615 with
                       | FStar_Parser_AST.TyconAbstract uu____616 -> true
                       | uu____627 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x, t) ->
               let uu____630 = FStar_Util.for_some (is_definition_of x) tl in
               if uu____630
               then
                 let uu____631 =
                   let uu____636 =
                     let uu____637 = FStar_Ident.string_of_id x in
                     let uu____638 = FStar_Ident.string_of_id x in
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       uu____637 uu____638 in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____636) in
                 FStar_Errors.raise_error uu____631
                   hd.FStar_Parser_AST.drange
               else
                 (let uu____640 =
                    FStar_All.pipe_right hd.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____640
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd.FStar_Parser_AST.drange
                  else ())
           | uu____644 -> ()) in
    aux iface;
    FStar_All.pipe_right iface
      (FStar_List.filter
         (fun d ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____653 -> false
            | uu____654 -> true))
let (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface ->
    fun impl ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____685, defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____702 =
            FStar_List.partition
              (fun d ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x ->
                         let uu____718 = FStar_Ident.ident_of_lid x in
                         is_val uu____718 d))) iface in
          (match uu____702 with
           | (val_xs, rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____741 -> (iface, [impl])
let ml_mode_check_initial_interface :
  'uuuuuu752 .
    'uuuuuu752 ->
      FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list
  =
  fun mname ->
    fun iface ->
      FStar_All.pipe_right iface
        (FStar_List.filter
           (fun d ->
              match d.FStar_Parser_AST.d with
              | FStar_Parser_AST.Val uu____776 -> true
              | uu____781 -> false))
let (ulib_modules : Prims.string Prims.list) =
  ["FStar.TSet";
  "FStar.Seq.Base";
  "FStar.Seq.Properties";
  "FStar.UInt";
  "FStar.UInt8";
  "FStar.UInt16";
  "FStar.UInt32";
  "FStar.UInt64";
  "FStar.Int";
  "FStar.Int8";
  "FStar.Int16";
  "FStar.Int32";
  "FStar.Int64"]
let (apply_ml_mode_optimizations : FStar_Ident.lident -> Prims.bool) =
  fun mname ->
    ((FStar_Options.ml_ish ()) &&
       (let uu____790 =
          let uu____791 = FStar_Ident.string_of_lid mname in
          FStar_List.contains uu____791 FStar_Parser_Dep.core_modules in
        Prims.op_Negation uu____790))
      &&
      (let uu____793 =
         let uu____794 = FStar_Ident.string_of_lid mname in
         FStar_List.contains uu____794 ulib_modules in
       Prims.op_Negation uu____793)
let (prefix_one_decl :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list ->
      FStar_Parser_AST.decl ->
        (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun mname ->
    fun iface ->
      fun impl ->
        match impl.FStar_Parser_AST.d with
        | FStar_Parser_AST.TopLevelModule uu____830 -> (iface, [impl])
        | uu____835 ->
            let uu____836 = apply_ml_mode_optimizations mname in
            if uu____836
            then ml_mode_prefix_with_iface_decls iface impl
            else prefix_with_iface_decls iface impl
let (initialize_interface :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list -> unit FStar_Syntax_DsEnv.withenv)
  =
  fun mname ->
    fun l ->
      fun env ->
        let decls =
          let uu____870 = apply_ml_mode_optimizations mname in
          if uu____870
          then ml_mode_check_initial_interface mname l
          else check_initial_interface l in
        let uu____874 = FStar_Syntax_DsEnv.iface_decls env mname in
        match uu____874 with
        | FStar_Pervasives_Native.Some uu____883 ->
            let uu____888 =
              let uu____893 =
                let uu____894 = FStar_Ident.string_of_lid mname in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____894 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____893) in
            let uu____895 = FStar_Ident.range_of_lid mname in
            FStar_Errors.raise_error uu____888 uu____895
        | FStar_Pervasives_Native.None ->
            let uu____902 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls in
            ((), uu____902)
let (prefix_with_interface_decls :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun mname ->
    fun impl ->
      fun env ->
        let uu____924 =
          let uu____929 = FStar_Syntax_DsEnv.current_module env in
          FStar_Syntax_DsEnv.iface_decls env uu____929 in
        match uu____924 with
        | FStar_Pervasives_Native.None -> ([impl], env)
        | FStar_Pervasives_Native.Some iface ->
            let uu____945 = prefix_one_decl mname iface impl in
            (match uu____945 with
             | (iface1, impl1) ->
                 let env1 =
                   let uu____971 = FStar_Syntax_DsEnv.current_module env in
                   FStar_Syntax_DsEnv.set_iface_decls env uu____971 iface1 in
                 (impl1, env1))
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a ->
    fun expect_complete_modul ->
      fun env ->
        match a with
        | FStar_Parser_AST.Interface uu____995 -> (a, env)
        | FStar_Parser_AST.Module (l, impls) ->
            let uu____1010 = FStar_Syntax_DsEnv.iface_decls env l in
            (match uu____1010 with
             | FStar_Pervasives_Native.None -> (a, env)
             | FStar_Pervasives_Native.Some iface ->
                 let uu____1026 =
                   FStar_List.fold_left
                     (fun uu____1050 ->
                        fun impl ->
                          match uu____1050 with
                          | (iface1, impls1) ->
                              let uu____1078 = prefix_one_decl l iface1 impl in
                              (match uu____1078 with
                               | (iface2, impls') ->
                                   (iface2,
                                     (FStar_List.append impls1 impls'))))
                     (iface, []) impls in
                 (match uu____1026 with
                  | (iface1, impls1) ->
                      let uu____1127 =
                        let uu____1136 =
                          FStar_Util.prefix_until
                            (fun uu___3_1154 ->
                               match uu___3_1154 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1155;
                                   FStar_Parser_AST.drange = uu____1156;
                                   FStar_Parser_AST.quals = uu____1157;
                                   FStar_Parser_AST.attrs = uu____1158;_} ->
                                   true
                               | uu____1163 -> false) iface1 in
                        match uu____1136 with
                        | FStar_Pervasives_Native.None -> (iface1, [])
                        | FStar_Pervasives_Native.Some (lets, one_val, rest)
                            -> (lets, (one_val :: rest)) in
                      (match uu____1127 with
                       | (iface_lets, remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets in
                           let env1 =
                             let uu____1229 = FStar_Options.interactive () in
                             if uu____1229
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env in
                           let a1 = FStar_Parser_AST.Module (l, impls2) in
                           (match remaining_iface_vals with
                            | uu____1238::uu____1239 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1243 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals in
                                  FStar_All.pipe_right uu____1243
                                    (FStar_String.concat "\n\t") in
                                let uu____1248 =
                                  let uu____1253 =
                                    let uu____1254 =
                                      FStar_Ident.string_of_lid l in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1254 err in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1253) in
                                let uu____1255 = FStar_Ident.range_of_lid l in
                                FStar_Errors.raise_error uu____1248
                                  uu____1255
                            | uu____1260 -> (a1, env1)))))