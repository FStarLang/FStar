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
               (fun uu____57  ->
                  match uu____57 with
                  | (t,uu____65) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____70 -> false
let definition_lids: FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____78,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____92,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___295_133  ->
                match uu___295_133 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id,uu____143,uu____144,uu____145),uu____146) ->
                    let uu____159 = FStar_Ident.lid_of_ids [id] in
                    [uu____159]
                | uu____160 -> []))
    | uu____167 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____174 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____174
let rec prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match iface1 with
      | [] -> ([], [impl])
      | iface_hd::iface_tl ->
          (match iface_hd.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____219,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___296_254  ->
                       match uu___296_254 with
                       | (FStar_Parser_AST.TyconAbstract uu____261,uu____262)
                           -> true
                       | uu____277 -> false))
               ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (impl.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let def_ids = definition_lids impl in
               let defines_x = FStar_Util.for_some (id_eq_lid x) def_ids in
               if Prims.op_Negation defines_x
               then
                 let uu____306 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____306
                  then
                    let uu____321 =
                      let uu____322 =
                        let uu____327 =
                          let uu____328 =
                            let uu____329 =
                              FStar_All.pipe_right def_ids
                                (FStar_List.map FStar_Ident.string_of_lid) in
                            FStar_All.pipe_right uu____329
                              (FStar_String.concat ", ") in
                          FStar_Util.format2
                            "Expected the definition of %s to precede %s"
                            x.FStar_Ident.idText uu____328 in
                        (uu____327, (impl.FStar_Parser_AST.drange)) in
                      FStar_Errors.Error uu____322 in
                    FStar_Exn.raise uu____321
                  else (iface1, [impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____396) -> ([], iface2)
                    | (uu____407::uu____408,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____439 = aux ys iface_tl1 in
                          (match uu____439 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____471 =
                             let uu____472 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____472 in
                           if uu____471
                           then
                             let uu____485 =
                               let uu____486 =
                                 let uu____491 =
                                   let uu____492 =
                                     FStar_Parser_AST.decl_to_string
                                       iface_hd1 in
                                   let uu____493 =
                                     FStar_Ident.string_of_lid y in
                                   FStar_Util.format2
                                     "%s is out of order with the definition of %s"
                                     uu____492 uu____493 in
                                 (uu____491,
                                   (iface_hd1.FStar_Parser_AST.drange)) in
                               FStar_Errors.Error uu____486 in
                             FStar_Exn.raise uu____485
                           else aux ys iface2) in
                  let uu____503 = aux mutually_defined_with_x iface_tl in
                  match uu____503 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____534 ->
               let uu____535 = prefix_with_iface_decls iface_tl impl in
               (match uu____535 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____587,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___297_622  ->
                       match uu___297_622 with
                       | (FStar_Parser_AST.TyconAbstract uu____629,uu____630)
                           -> true
                       | uu____645 -> false))
               ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (hd1.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let uu____654 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____654
               then
                 let uu____655 =
                   let uu____656 =
                     let uu____661 =
                       FStar_Util.format2
                         "'val %s' and 'let %s' cannot both be provided in an interface"
                         x.FStar_Ident.idText x.FStar_Ident.idText in
                     (uu____661, (hd1.FStar_Parser_AST.drange)) in
                   FStar_Errors.Error uu____656 in
                 FStar_Exn.raise uu____655
               else
                 (let uu____663 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____663
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead",
                           (hd1.FStar_Parser_AST.drange)))
                  else ())
           | uu____665 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____674 -> false
            | uu____675 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____702,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____719 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____719 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____756 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____777 -> true
            | uu____782 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____809 -> (iface1, [impl])
      | uu____814 ->
          let uu____815 = FStar_Options.ml_ish () in
          if uu____815
          then ml_mode_prefix_with_iface_decls iface1 impl
          else prefix_with_iface_decls iface1 impl
let initialize_interface:
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list -> Prims.unit FStar_ToSyntax_Env.withenv
  =
  fun mname  ->
    fun l  ->
      fun env  ->
        let decls =
          let uu____847 = FStar_Options.ml_ish () in
          if uu____847
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____851 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____851 with
        | FStar_Pervasives_Native.Some uu____860 ->
            let uu____865 =
              let uu____866 =
                let uu____871 =
                  let uu____872 = FStar_Ident.string_of_lid mname in
                  FStar_Util.format1
                    "Interface %s has already been processed" uu____872 in
                (uu____871, (FStar_Ident.range_of_lid mname)) in
              FStar_Errors.Error uu____866 in
            FStar_Exn.raise uu____865
        | FStar_Pervasives_Native.None  ->
            let uu____879 =
              FStar_ToSyntax_Env.set_iface_decls env mname decls in
            ((), uu____879)
let prefix_with_interface_decls:
  FStar_Parser_AST.decl ->
    FStar_Parser_AST.decl Prims.list FStar_ToSyntax_Env.withenv
  =
  fun impl  ->
    fun env  ->
      let uu____896 =
        let uu____901 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____901 in
      match uu____896 with
      | FStar_Pervasives_Native.None  -> ([impl], env)
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____917 = prefix_one_decl iface1 impl in
          (match uu____917 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____943 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____943 iface2 in
               (impl1, env1))
let interleave_module:
  FStar_Parser_AST.modul ->
    Prims.bool -> FStar_Parser_AST.modul FStar_ToSyntax_Env.withenv
  =
  fun a  ->
    fun expect_complete_modul  ->
      fun env  ->
        match a with
        | FStar_Parser_AST.Interface uu____965 -> (a, env)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____980 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____980 with
             | FStar_Pervasives_Native.None  -> (a, env)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____996 =
                   FStar_List.fold_left
                     (fun uu____1020  ->
                        fun impl  ->
                          match uu____1020 with
                          | (iface2,impls1) ->
                              let uu____1048 = prefix_one_decl iface2 impl in
                              (match uu____1048 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____996 with
                  | (iface2,impls1) ->
                      let env1 =
                        FStar_ToSyntax_Env.set_iface_decls env l iface2 in
                      let a1 = FStar_Parser_AST.Module (l, impls1) in
                      (match iface2 with
                       | uu____1105::uu____1106 when expect_complete_modul ->
                           let err1 =
                             let uu____1110 =
                               FStar_List.map FStar_Parser_AST.decl_to_string
                                 iface2 in
                             FStar_All.pipe_right uu____1110
                               (FStar_String.concat "\n\t") in
                           let uu____1115 =
                             let uu____1116 =
                               let uu____1121 =
                                 let uu____1122 = FStar_Ident.string_of_lid l in
                                 FStar_Util.format2
                                   "Some interface elements were not implemented by module %s:\n\t%s"
                                   uu____1122 err1 in
                               (uu____1121, (FStar_Ident.range_of_lid l)) in
                             FStar_Errors.Error uu____1116 in
                           FStar_Exn.raise uu____1115
                       | uu____1127 -> (a1, env1))))