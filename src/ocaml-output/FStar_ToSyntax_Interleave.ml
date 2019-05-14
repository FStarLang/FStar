open Prims
let (id_eq_lid : FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool) =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
  
let (is_val : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____52) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____64 -> false
  
let (is_type : FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____93,uu____94,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____134  ->
                  match uu____134 with
                  | (t,uu____143) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____149 -> false
  
let (definition_lids :
  FStar_Parser_AST.decl -> FStar_Ident.lident Prims.list) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____179,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____206,uu____207,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___0_260  ->
                match uu___0_260 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id1,uu____274,uu____275,uu____276),uu____277) ->
                    let uu____314 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____314]
                | (FStar_Parser_AST.TyconRecord
                   (id1,uu____336,uu____337,uu____338),uu____339) ->
                    let uu____400 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____400]
                | (FStar_Parser_AST.TyconVariant
                   (id1,uu____422,uu____423,uu____424),uu____425) ->
                    let uu____496 = FStar_Ident.lid_of_ids [id1]  in
                    [uu____496]
                | uu____517 -> []))
    | uu____528 -> []
  
let (is_definition_of :
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool) =
  fun x  ->
    fun d  ->
      let uu____559 = definition_lids d  in
      FStar_Util.for_some (id_eq_lid x) uu____559
  
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
        let uu___66_681 = impl1  in
        {
          FStar_Parser_AST.d = (uu___66_681.FStar_Parser_AST.d);
          FStar_Parser_AST.drange = (uu___66_681.FStar_Parser_AST.drange);
          FStar_Parser_AST.doc = (uu___66_681.FStar_Parser_AST.doc);
          FStar_Parser_AST.quals = (uu___66_681.FStar_Parser_AST.quals);
          FStar_Parser_AST.attrs = (krem_private ::
            (impl1.FStar_Parser_AST.attrs))
        }  in
      match iface1 with
      | [] -> ([], [qualify_kremlin_private impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____784,uu____785,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___1_825  ->
                       match uu___1_825 with
                       | (FStar_Parser_AST.TyconAbstract uu____833,uu____834)
                           -> true
                       | uu____859 -> false))
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
                 let uu____931 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident))))
                    in
                 (if uu____931
                  then
                    let uu____982 =
                      let uu____988 =
                        let uu____990 =
                          let uu____992 =
                            FStar_All.pipe_right def_ids
                              (FStar_List.map FStar_Ident.string_of_lid)
                             in
                          FStar_All.pipe_right uu____992
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.format2
                          "Expected the definition of %s to precede %s"
                          x.FStar_Ident.idText uu____990
                         in
                      (FStar_Errors.Fatal_WrongDefinitionOrder, uu____988)
                       in
                    FStar_Errors.raise_error uu____982
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
                    | ([],uu____1178) -> ([], iface2)
                    | (uu____1222::uu____1223,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____1347 = aux ys iface_tl1  in
                          (match uu____1347 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____1435 =
                             let uu____1437 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1
                                in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____1437
                              in
                           if uu____1435
                           then
                             let uu____1482 =
                               let uu____1488 =
                                 let uu____1490 =
                                   FStar_Parser_AST.decl_to_string iface_hd1
                                    in
                                 let uu____1492 = FStar_Ident.string_of_lid y
                                    in
                                 FStar_Util.format2
                                   "%s is out of order with the definition of %s"
                                   uu____1490 uu____1492
                                  in
                               (FStar_Errors.Fatal_WrongDefinitionOrder,
                                 uu____1488)
                                in
                             FStar_Errors.raise_error uu____1482
                               iface_hd1.FStar_Parser_AST.drange
                           else aux ys iface2)
                     in
                  let uu____1516 = aux mutually_defined_with_x iface_tl  in
                  match uu____1516 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____1617 ->
               let uu____1618 = prefix_with_iface_decls iface_tl impl  in
               (match uu____1618 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
  
let (check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____1775,uu____1776,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___2_1816  ->
                       match uu___2_1816 with
                       | (FStar_Parser_AST.TyconAbstract
                          uu____1824,uu____1825) -> true
                       | uu____1850 -> false))
               ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_AbstractTypeDeclarationInInterface,
                   "Interface contains an abstract 'type' declaration; use 'val' instead")
                 hd1.FStar_Parser_AST.drange
           | FStar_Parser_AST.Val (x,t) ->
               let uu____1872 = FStar_Util.for_some (is_definition_of x) tl1
                  in
               if uu____1872
               then
                 let uu____1880 =
                   let uu____1886 =
                     FStar_Util.format2
                       "'val %s' and 'let %s' cannot both be provided in an interface"
                       x.FStar_Ident.idText x.FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_BothValAndLetInInterface, uu____1886)
                    in
                 FStar_Errors.raise_error uu____1880
                   hd1.FStar_Parser_AST.drange
               else
                 (let uu____1892 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption)
                     in
                  if uu____1892
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_AssumeValInInterface,
                        "Interfaces cannot use `assume val x : t`; just write `val x : t` instead")
                      hd1.FStar_Parser_AST.drange
                  else ())
           | uu____1902 -> ())
       in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____1932 -> false
            | uu____1938 -> true))
  
let rec (ml_mode_prefix_with_iface_decls :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____2011,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs  in
          let uu____2045 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1
             in
          (match uu____2045 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____2170 -> (iface1, [impl])
  
let (ml_mode_check_initial_interface :
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list) =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____2250 -> true
            | uu____2261 -> false))
  
let (prefix_one_decl :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list * FStar_Parser_AST.decl Prims.list))
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____2334 -> (iface1, [impl])
      | uu____2363 ->
          let uu____2364 = FStar_Options.ml_ish ()  in
          if uu____2364
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
          let uu____2435 = FStar_Options.ml_ish ()  in
          if uu____2435
          then ml_mode_check_initial_interface l
          else check_initial_interface l  in
        let uu____2447 = FStar_Syntax_DsEnv.iface_decls env mname  in
        match uu____2447 with
        | FStar_Pervasives_Native.Some uu____2461 ->
            let uu____2476 =
              let uu____2482 =
                let uu____2484 = FStar_Ident.string_of_lid mname  in
                FStar_Util.format1 "Interface %s has already been processed"
                  uu____2484
                 in
              (FStar_Errors.Fatal_InterfaceAlreadyProcessed, uu____2482)  in
            let uu____2488 = FStar_Ident.range_of_lid mname  in
            FStar_Errors.raise_error uu____2476 uu____2488
        | FStar_Pervasives_Native.None  ->
            let uu____2500 =
              FStar_Syntax_DsEnv.set_iface_decls env mname decls  in
            ((), uu____2500)
  
let (prefix_with_interface_decls :
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_Syntax_DsEnv.withenv)
  =
  fun impl  ->
    fun env  ->
      let uu____2538 =
        let uu____2548 = FStar_Syntax_DsEnv.current_module env  in
        FStar_Syntax_DsEnv.iface_decls env uu____2548  in
      match uu____2538 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____2607 = prefix_one_decl iface1 impl  in
          (match uu____2607 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____2668 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Syntax_DsEnv.set_iface_decls env uu____2668 iface2  in
               (impl1, env1))
  
let (interleave_module :
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_Syntax_DsEnv.withenv)
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____2708 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____2751 = FStar_Syntax_DsEnv.iface_decls env l  in
            (match uu____2751 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____2787 =
                   FStar_List.fold_left
                     (fun uu____2836  ->
                        fun impl  ->
                          match uu____2836 with
                          | (iface2,impls1) ->
                              let uu____2909 = prefix_one_decl iface2 impl
                                 in
                              (match uu____2909 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls
                    in
                 (match uu____2787 with
                  | (iface2,impls1) ->
                      let uu____3048 =
                        let uu____3067 =
                          FStar_Util.prefix_until
                            (fun uu___3_3106  ->
                               match uu___3_3106 with
                               | {
                                   FStar_Parser_AST.d = FStar_Parser_AST.Val
                                     uu____3113;
                                   FStar_Parser_AST.drange = uu____3114;
                                   FStar_Parser_AST.doc = uu____3115;
                                   FStar_Parser_AST.quals = uu____3116;
                                   FStar_Parser_AST.attrs = uu____3117;_} ->
                                   true
                               | uu____3130 -> false) iface2
                           in
                        match uu____3067 with
                        | FStar_Pervasives_Native.None  -> (iface2, [])
                        | FStar_Pervasives_Native.Some (lets,one_val,rest) ->
                            (lets, (one_val :: rest))
                         in
                      (match uu____3048 with
                       | (iface_lets,remaining_iface_vals) ->
                           let impls2 = FStar_List.append impls1 iface_lets
                              in
                           let env1 =
                             let uu____3332 = FStar_Options.interactive ()
                                in
                             if uu____3332
                             then
                               FStar_Syntax_DsEnv.set_iface_decls env l
                                 remaining_iface_vals
                             else env  in
                           let a1 = FStar_Parser_AST.Module (l, impls2)  in
                           (match remaining_iface_vals with
                            | uu____3353::uu____3354 when
                                expect_complete_modul ->
                                let err =
                                  let uu____3374 =
                                    FStar_List.map
                                      FStar_Parser_AST.decl_to_string
                                      remaining_iface_vals
                                     in
                                  FStar_All.pipe_right uu____3374
                                    (FStar_String.concat "\n\t")
                                   in
                                let uu____3389 =
                                  let uu____3395 =
                                    let uu____3397 =
                                      FStar_Ident.string_of_lid l  in
                                    FStar_Util.format2
                                      "Some interface elements were not implemented by module %s:\n\t%s"
                                      uu____3397 err
                                     in
                                  (FStar_Errors.Fatal_InterfaceNotImplementedByModule,
                                    uu____3395)
                                   in
                                let uu____3401 = FStar_Ident.range_of_lid l
                                   in
                                FStar_Errors.raise_error uu____3389
                                  uu____3401
                            | uu____3406 -> (a1, env1)))))
  