open Prims
let id_eq_lid: FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
let is_val: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____14) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____15 -> false
let is_type: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____22,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____42  ->
                  match uu____42 with
                  | (t,uu____47) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____50 -> false
let definition_lids: FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____56,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____64,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___193_89  ->
                match uu___193_89 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id,uu____95,uu____96,uu____97),uu____98) ->
                    let uu____105 = FStar_Ident.lid_of_ids [id] in
                    [uu____105]
                | uu____106 -> []))
    | uu____110 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____117 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____117
let rec prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list* FStar_Parser_AST.decl Prims.list)
  =
  fun iface1  ->
    fun impl  ->
      match iface1 with
      | [] -> ([], [impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____144,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___194_164  ->
                       match uu___194_164 with
                       | (FStar_Parser_AST.TyconAbstract uu____168,uu____169)
                           -> true
                       | uu____177 -> false))
               ->
               raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (impl.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let def_ids = definition_lids impl in
               let defines_x = FStar_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 let uu____194 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____194
                  then
                    let uu____203 =
                      let uu____204 =
                        let uu____207 =
                          let uu____208 =
                            let uu____209 =
                              FStar_All.pipe_right def_ids
                                (FStar_List.map FStar_Ident.string_of_lid) in
                            FStar_All.pipe_right uu____209
                              (FStar_String.concat ", ") in
                          FStar_Util.format2
                            "Expected the definition of %s to precede %s"
                            x.FStar_Ident.idText uu____208 in
                        (uu____207, (impl.FStar_Parser_AST.drange)) in
                      FStar_Errors.Error uu____204 in
                    raise uu____203
                  else (iface1, [impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____249) -> ([], iface2)
                    | (uu____255::uu____256,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____274 = aux ys iface_tl1 in
                          (match uu____274 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____292 =
                             let uu____293 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____293 in
                           if uu____292
                           then
                             let uu____300 =
                               let uu____301 =
                                 let uu____304 =
                                   let uu____305 =
                                     FStar_Parser_AST.decl_to_string
                                       iface_hd1 in
                                   let uu____306 =
                                     FStar_Ident.string_of_lid y in
                                   FStar_Util.format2
                                     "%s is out of order with the definition of %s"
                                     uu____305 uu____306 in
                                 (uu____304,
                                   (iface_hd1.FStar_Parser_AST.drange)) in
                               FStar_Errors.Error uu____301 in
                             raise uu____300
                           else aux ys iface2) in
                  let uu____312 = aux mutually_defined_with_x iface_tl in
                  match uu____312 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____329 ->
               let uu____330 = prefix_with_iface_decls iface_tl impl in
               (match uu____330 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____362,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___195_382  ->
                       match uu___195_382 with
                       | (FStar_Parser_AST.TyconAbstract uu____386,uu____387)
                           -> true
                       | uu____395 -> false))
               ->
               raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (hd1.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let uu____401 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____401
               then
                 let uu____402 =
                   let uu____403 =
                     let uu____406 =
                       FStar_Util.format2
                         "'val %s' and 'let %s' cannot both be provided in an interface"
                         x.FStar_Ident.idText x.FStar_Ident.idText in
                     (uu____406, (hd1.FStar_Parser_AST.drange)) in
                   FStar_Errors.Error uu____403 in
                 raise uu____402
               else
                 (let uu____408 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____408
                  then
                    raise
                      (FStar_Errors.Error
                         ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead",
                           (hd1.FStar_Parser_AST.drange)))
                  else ())
           | uu____410 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____417 -> false
            | uu____418 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list* FStar_Parser_AST.decl Prims.list)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____435,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____445 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____445 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____467 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____481 -> true
            | uu____484 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list* FStar_Parser_AST.decl Prims.list)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____501 -> (iface1, [impl])
      | uu____504 ->
          let uu____505 = FStar_Options.ml_ish () in
          if uu____505
          then ml_mode_prefix_with_iface_decls iface1 impl
          else prefix_with_iface_decls iface1 impl
let initialize_interface:
  FStar_Ident.lid ->
    FStar_Parser_AST.decl Prims.list ->
      FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun mname  ->
    fun l  ->
      fun env  ->
        let decls =
          let uu____524 = FStar_Options.ml_ish () in
          if uu____524
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____527 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____527 with
        | Some uu____530 ->
            let uu____533 =
              let uu____534 =
                let uu____537 =
                  let uu____538 = FStar_Ident.string_of_lid mname in
                  FStar_Util.format1
                    "Interface %s has already been processed" uu____538 in
                (uu____537, (FStar_Ident.range_of_lid mname)) in
              FStar_Errors.Error uu____534 in
            raise uu____533
        | None  -> FStar_ToSyntax_Env.set_iface_decls env mname decls
let prefix_with_interface_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_ToSyntax_Env.env* FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun impl  ->
      let uu____552 =
        let uu____555 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____555 in
      match uu____552 with
      | None  -> (env, [impl])
      | Some iface1 ->
          let uu____564 = prefix_one_decl iface1 impl in
          (match uu____564 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____579 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____579 iface2 in
               (env1, impl1))
let interleave_module:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      Prims.bool -> (FStar_ToSyntax_Env.env* FStar_Parser_AST.modul)
  =
  fun env  ->
    fun a  ->
      fun expect_complete_modul  ->
        match a with
        | FStar_Parser_AST.Interface uu____594 -> (env, a)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____603 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____603 with
             | None  -> (env, a)
             | Some iface1 ->
                 let uu____612 =
                   FStar_List.fold_left
                     (fun uu____628  ->
                        fun impl  ->
                          match uu____628 with
                          | (iface2,impls1) ->
                              let uu____644 = prefix_one_decl iface2 impl in
                              (match uu____644 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____612 with
                  | (iface2,impls1) ->
                      let env1 =
                        FStar_ToSyntax_Env.set_iface_decls env l iface2 in
                      let a1 = FStar_Parser_AST.Module (l, impls1) in
                      (match iface2 with
                       | uu____676::uu____677 when expect_complete_modul ->
                           let err1 =
                             let uu____680 =
                               FStar_List.map FStar_Parser_AST.decl_to_string
                                 iface2 in
                             FStar_All.pipe_right uu____680
                               (FStar_String.concat "\n\t") in
                           let uu____683 =
                             let uu____684 =
                               let uu____687 =
                                 let uu____688 = FStar_Ident.string_of_lid l in
                                 FStar_Util.format2
                                   "Some interface elements were not implemented by module %s:\n\t%s"
                                   uu____688 err1 in
                               (uu____687, (FStar_Ident.range_of_lid l)) in
                             FStar_Errors.Error uu____684 in
                           raise uu____683
                       | uu____691 -> (env1, a1))))