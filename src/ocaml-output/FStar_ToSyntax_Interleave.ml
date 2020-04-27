open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  ->
      let uu____11 = FStar_Ident.text_of_id i  in
      let uu____13 =
        let uu____15 = FStar_Ident.ident_of_lid l  in
        FStar_Ident.text_of_id uu____15  in
      uu____11 = uu____13
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____31) ->
          let uu____32 = FStar_Ident.text_of_id x  in
          let uu____34 = FStar_Ident.text_of_id y  in uu____32 = uu____34
      | uu____37 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____52,uu____53,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun t  ->
                  let uu____70 = FStar_Parser_AST.id_of_tycon t  in
                  let uu____72 = FStar_Ident.text_of_id x  in
                  uu____70 = uu____72))
      | uu____75 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____87,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____101,uu____102,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___0_122  ->
                match uu___0_122 with
                | FStar_Parser_AST.TyconAbbrev
                    (id,uu____126,uu____127,uu____128) ->
                    let uu____137 = FStar_Ident.lid_of_ids [id]  in
                    [uu____137]
                | FStar_Parser_AST.TyconRecord
                    (id,uu____139,uu____140,uu____141) ->
                    let uu____162 = FStar_Ident.lid_of_ids [id]  in
                    [uu____162]
                | FStar_Parser_AST.TyconVariant
                    (id,uu____164,uu____165,uu____166) ->
                    let uu____197 = FStar_Ident.lid_of_ids [id]  in
                    [uu____197]
                | uu____198 -> []))
    | uu____199 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____212 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____212
  
let rec (prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface  ->
    fun impl  ->
      let qualify_kremlin_private impl1 =
        let krem_private =
          FStar_Parser_AST.mk_term
            (FStar_Parser_AST.Const
               (FStar_Const.Const_string
                  ("KremlinPrivate", (impl1.FStar_Parser_AST.drange))))
            impl1.FStar_Parser_AST.drange FStar_Parser_AST.Expr
           in
        let uu___58_255 = impl1  in
        {
          FStar_Parser_AST.d = (uu___58_255.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___58_255.FStar_Parser_AST.drange);
          FStar_Parser_AST.quals = (uu___58_255.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____280,uu____281,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___1_296  ->
                       match uu___1_296 with
                       | FStar_Parser_AST.TyconAbstract uu____298 -> true
                       | uu____310 -> false))
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
                 let uu____338 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           let uu____346 =
                             let uu____354 =
                               let uu____360 = FStar_Ident.ident_of_lid y  in
                               is_val uu____360  in
                             FStar_Util.for_some uu____354  in
                           FStar_All.pipe_right iface_tl uu____346))
                    in
                 (if uu____338
                  then
                    let uu____373 =
                      let uu____379 =
                        let uu____381 = FStar_Ident.text_of_id x  in
                        let uu____383 =
                          let uu____385 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____385
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          uu____381 uu____383
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____379)
                       in
                    FStar_Errors.raise_error uu____373
                      impl.FStar_Parser_AST.drange
                  else (iface, [qualify_kremlin_private impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  ->
                            let uu____428 = id_eq_lid x y  in
                            Prims.op_Negation uu____428))
                     in
                  let rec aux mutuals iface1 =
                    match (mutuals, iface1) with
                    | ([],uu____469) -> ([], iface1)
                    | (uu____480::uu____481,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        let uu____504 =
                          let uu____506 = FStar_Ident.ident_of_lid y  in
                          is_val uu____506 iface_hd1  in
                        if uu____504
                        then
                          let uu____516 = aux ys iface_tl1  in
                          (match uu____516 with
                           | (val_ys,iface2) ->
                               ((iface_hd1 :: val_ys), iface2))
                        else
                          (let uu____549 =
                             let uu____551 =
                               let uu____554 =
                                 let uu____560 = FStar_Ident.ident_of_lid y
                                    in
                                 is_val uu____560  in
                               FStar_List.tryFind uu____554 iface_tl1  in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____551
                              in
                           if uu____549
                           then
                             let uu____573 =
                               let uu____579 =
                                 let uu____581 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____583 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____581 uu____583
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____579)
                                in
                             FStar_Errors.raise_error uu____573
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface1)
                     in
                  let uu____597 = aux mutually_defined_with_x iface_tl  in
                  match uu____597 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | FStar_Parser_AST.Pragma uu____628 ->
               prefix_with_iface_decls iface_tl impl
           | uu____629 ->
               let uu____630 = prefix_with_iface_decls iface_tl impl  in
               (match uu____630 with
                | (iface1,ds) -> (iface1, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface  ->
    let rec aux iface1 =
      match iface1 with
      | [] -> ()
      | hd::tl ->
          (match hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____687,uu____688,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___2_703  ->
                       match uu___2_703 with
                       | FStar_Parser_AST.TyconAbstract uu____705 -> true
                       | uu____717 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____723 = FStar_Util.for_some (is_definition_of x) tl
                  in
               if uu____723
               then
                 let uu____726 =
                   let uu____732 =
                     let uu____734 = FStar_Ident.text_of_id x  in
                     let uu____736 = FStar_Ident.text_of_id x  in
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       uu____734 uu____736
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____732)
                    in
                 FStar_Errors.raise_error uu____726
                   hd.FStar_Parser_AST.drange
               else
                 (let uu____742 =
                    FStar_All.pipe_right hd.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____742
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd.FStar_Parser_AST.drange
                  else ())
           | uu____752 -> ())
       in
    aux iface;
    FStar_All.pipe_right iface
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____762 -> false
            | uu____764 -> true))
  
let (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____797,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____814 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  ->
                         let uu____831 = FStar_Ident.ident_of_lid x  in
                         is_val uu____831 d))) iface
             in
          (match uu____814 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____854 -> (iface, [impl])
  
let ml_mode_check_initial_interface :
  'uuuuuu866 .
    'uuuuuu866 ->
      FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list
  =
  fun mname  ->
    fun iface  ->
      FStar_All.pipe_right iface
        (FStar_List.filter
           (fun d  ->
              match d.FStar_Parser_AST.d with
              | FStar_Parser_AST.Val uu____891 -> true
              | uu____897 -> false))
  
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
  fun mname  ->
    ((FStar_Options.ml_ish ()) &&
       (let uu____939 =
          let uu____941 = FStar_Ident.string_of_lid mname  in
          FStar_List.contains uu____941 FStar_Parser_Dep.core_modules  in
        Prims.op_Negation uu____939))
      &&
      (let uu____945 =
         let uu____947 = FStar_Ident.string_of_lid mname  in
         FStar_List.contains uu____947 ulib_modules  in
       Prims.op_Negation uu____945)
  
let (prefix_one_decl :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list ->
      FStar_Parser_AST.decl ->
        (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun mname  ->
    fun iface  ->
      fun impl  ->
        match impl.FStar_Parser_AST.d with
        | FStar_Parser_AST.TopLevelModule uu____986 -> (iface, [impl])
        | uu____991 ->
            let uu____992 = apply_ml_mode_optimizations mname  in
            if uu____992
            then ml_mode_prefix_with_iface_decls iface impl
            else prefix_with_iface_decls iface impl
  
let (initialize_interface :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list -> unit FStar_Syntax_DsEnv.withenv)
  =
  fun mname  ->
    fun l  ->
      fun env  ->
        let decls =
          let uu____1030 = apply_ml_mode_optimizations mname  in
          if uu____1030
          then ml_mode_check_initial_interface mname l
          else check_initial_interface l  in
        let uu____1037 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____1037 with
        | FStar_Pervasives_Native.Some uu____1046 ->
            let uu____1051 =
              let uu____1057 =
                let uu____1059 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____1059
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____1057)  in
            let uu____1063 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____1051 uu____1063
        | FStar_Pervasives_Native.None  ->
            let uu____1070 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____1070)
  
let (prefix_with_interface_decls :
  FStar_Ident.lident ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun mname  ->
    fun impl  ->
      fun env  ->
        let uu____1093 =
          let uu____1098 = FStar_Syntax_DsEnv.current_module env  in
          FStar_Syntax_DsEnv.iface_decls env uu____1098  in
        match uu____1093 with
        | FStar_Pervasives_Native.None  -> ([impl], env)
        | FStar_Pervasives_Native.Some iface ->
            let uu____1114 = prefix_one_decl mname iface impl  in
            (match uu____1114 with
             | (iface1,impl1) ->
                 let env1 =
                   let uu____1140 = FStar_Syntax_DsEnv.current_module env  in
                   FStar_Syntax_DsEnv.set_iface_decls env uu____1140 iface1
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
        | FStar_Parser_AST.Interface uu____1167 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____1183 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____1183 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface ->
                 let uu____1199 =
                   FStar_List.fold_left
                     (fun uu____1223  ->
                        fun impl  ->
                          match uu____1223 with
                          | (iface1,impls1) ->
                              let uu____1251 = prefix_one_decl l iface1 impl
                                 in
                              (match uu____1251 with
                               | (iface2,impls') ->
                                   (iface2,
                                     (FStar_List.append impls1 impls'))))
                     (iface, []) impls
                    in
                 (match uu____1199 with
                  | (iface1,impls1) ->
                      let uu____1300 =
                        let uu____1309 =
                          FStar_Util.prefix_until
                            (fun uu___3_1327  ->
                               match uu___3_1327 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____1329;
                                   FStar_Parser_AST.drange = uu____1330;
                                   FStar_Parser_AST.quals = uu____1331;
                                   FStar_Parser_AST.attrs = uu____1332;_} ->
                                   true
                               | uu____1338 -> false) iface1
                           in
                        match uu____1309 with
                        | FStar_Pervasives_Native.None  -> (iface1, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____1300 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____1405 = FStar_Options.interactive ()
                                in
                             if uu____1405
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____1417::uu____1418 when
                                expect_complete_modul ->
                                let err =
                                  let uu____1423 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____1423
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____1433 =
                                  let uu____1439 =
                                    let uu____1441 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____1441 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____1439)
                                   in
                                let uu____1445 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____1433
                                  uu____1445
                            | uu____1450 -> (a1, env1)))))
  