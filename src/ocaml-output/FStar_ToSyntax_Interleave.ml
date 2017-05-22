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
               (fun uu____39  ->
                  match uu____39 with
                  | (t,uu____44) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____47 -> false
let definition_lids: FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____53,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____61,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___193_79  ->
                match uu___193_79 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id,uu____85,uu____86,uu____87),uu____88) ->
                    let uu____95 = FStar_Ident.lid_of_ids [id] in [uu____95]
                | uu____96 -> []))
    | uu____100 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____107 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____107
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
           | FStar_Parser_AST.Tycon (uu____138,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___194_155  ->
                       match uu___194_155 with
                       | (FStar_Parser_AST.TyconAbstract uu____159,uu____160)
                           -> true
                       | uu____168 -> false))
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
                 let uu____185 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____185
                  then
                    let uu____193 =
                      let uu____194 =
                        let uu____197 =
                          let uu____198 =
                            let uu____199 =
                              FStar_All.pipe_right def_ids
                                (FStar_List.map FStar_Ident.string_of_lid) in
                            FStar_All.pipe_right uu____199
                              (FStar_String.concat ", ") in
                          FStar_Util.format2
                            "Expected the definition of %s to precede %s"
                            x.FStar_Ident.idText uu____198 in
                        (uu____197, (impl.FStar_Parser_AST.drange)) in
                      FStar_Errors.Error uu____194 in
                    raise uu____193
                  else (iface1, [impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____238) -> ([], iface2)
                    | (uu____244::uu____245,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____263 = aux ys iface_tl1 in
                          (match uu____263 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____281 =
                             let uu____282 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____282 in
                           if uu____281
                           then
                             let uu____289 =
                               let uu____290 =
                                 let uu____293 =
                                   let uu____294 =
                                     FStar_Parser_AST.decl_to_string
                                       iface_hd1 in
                                   let uu____295 =
                                     FStar_Ident.string_of_lid y in
                                   FStar_Util.format2
                                     "%s is out of order with the definition of %s"
                                     uu____294 uu____295 in
                                 (uu____293,
                                   (iface_hd1.FStar_Parser_AST.drange)) in
                               FStar_Errors.Error uu____290 in
                             raise uu____289
                           else aux ys iface2) in
                  let uu____301 = aux mutually_defined_with_x iface_tl in
                  match uu____301 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____318 ->
               let uu____319 = prefix_with_iface_decls iface_tl impl in
               (match uu____319 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____351,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___195_368  ->
                       match uu___195_368 with
                       | (FStar_Parser_AST.TyconAbstract uu____372,uu____373)
                           -> true
                       | uu____381 -> false))
               ->
               raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (hd1.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let uu____387 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____387
               then
                 let uu____388 =
                   let uu____389 =
                     let uu____392 =
                       FStar_Util.format2
                         "'val %s' and 'let %s' cannot both be provided in an interface"
                         x.FStar_Ident.idText x.FStar_Ident.idText in
                     (uu____392, (hd1.FStar_Parser_AST.drange)) in
                   FStar_Errors.Error uu____389 in
                 raise uu____388
               else
                 (let uu____394 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____394
                  then
                    raise
                      (FStar_Errors.Error
                         ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead",
                           (hd1.FStar_Parser_AST.drange)))
                  else ())
           | uu____396 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____401 -> false
            | uu____402 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list* FStar_Parser_AST.decl Prims.list)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____423,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____433 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____433 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____453 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____465 -> true
            | uu____468 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list* FStar_Parser_AST.decl Prims.list)
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____485 -> (iface1, [impl])
      | uu____488 ->
          let uu____489 = FStar_Options.ml_ish () in
          if uu____489
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
          let uu____508 = FStar_Options.ml_ish () in
          if uu____508
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____511 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____511 with
        | Some uu____514 ->
            let uu____517 =
              let uu____518 =
                let uu____521 =
                  let uu____522 = FStar_Ident.string_of_lid mname in
                  FStar_Util.format1
                    "Interface %s has already been processed" uu____522 in
                (uu____521, (FStar_Ident.range_of_lid mname)) in
              FStar_Errors.Error uu____518 in
            raise uu____517
        | None  -> FStar_ToSyntax_Env.set_iface_decls env mname decls
let prefix_with_interface_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_ToSyntax_Env.env* FStar_Parser_AST.decl Prims.list)
  =
  fun env  ->
    fun impl  ->
      let uu____536 =
        let uu____539 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____539 in
      match uu____536 with
      | None  -> (env, [impl])
      | Some iface1 ->
          let uu____548 = prefix_one_decl iface1 impl in
          (match uu____548 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____563 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____563 iface2 in
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
        | FStar_Parser_AST.Interface uu____580 -> (env, a)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____589 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____589 with
             | None  -> (env, a)
             | Some iface1 ->
                 let uu____598 =
                   FStar_List.fold_left
                     (fun uu____607  ->
                        fun impl  ->
                          match uu____607 with
                          | (iface2,impls1) ->
                              let uu____623 = prefix_one_decl iface2 impl in
                              (match uu____623 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____598 with
                  | (iface2,impls1) ->
                      let env1 =
                        FStar_ToSyntax_Env.set_iface_decls env l iface2 in
                      let a1 = FStar_Parser_AST.Module (l, impls1) in
                      (match iface2 with
                       | uu____655::uu____656 when expect_complete_modul ->
                           let err1 =
                             let uu____659 =
                               FStar_List.map FStar_Parser_AST.decl_to_string
                                 iface2 in
                             FStar_All.pipe_right uu____659
                               (FStar_String.concat "\n\t") in
                           let uu____662 =
                             let uu____663 =
                               let uu____666 =
                                 let uu____667 = FStar_Ident.string_of_lid l in
                                 FStar_Util.format2
                                   "Some interface elements were not implemented by module %s:\n\t%s"
                                   uu____667 err1 in
                               (uu____666, (FStar_Ident.range_of_lid l)) in
                             FStar_Errors.Error uu____663 in
                           raise uu____662
                       | uu____670 -> (env1, a1))))