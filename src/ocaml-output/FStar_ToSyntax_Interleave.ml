open Prims
let id_eq_lid: FStar_Ident.ident -> FStar_Ident.lident -> Prims.bool =
  fun i  ->
    fun l  -> i.FStar_Ident.idText = (l.FStar_Ident.ident).FStar_Ident.idText
let is_val: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Val (y,uu____18) ->
          x.FStar_Ident.idText = y.FStar_Ident.idText
      | uu____19 -> false
let is_type: FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon (uu____28,tys) ->
          FStar_All.pipe_right tys
            (FStar_Util.for_some
               (fun uu____63  ->
                  match uu____63 with
                  | (t,uu____71) ->
                      (FStar_Parser_AST.id_of_tycon t) = x.FStar_Ident.idText))
      | uu____76 -> false
let definition_lids: FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.TopLevelLet (uu____85,defs) ->
        FStar_Parser_AST.lids_of_let defs
    | FStar_Parser_AST.Tycon (uu____99,tys) ->
        FStar_All.pipe_right tys
          (FStar_List.collect
             (fun uu___206_140  ->
                match uu___206_140 with
                | (FStar_Parser_AST.TyconAbbrev
                   (id,uu____150,uu____151,uu____152),uu____153) ->
                    let uu____166 = FStar_Ident.lid_of_ids [id] in
                    [uu____166]
                | uu____167 -> []))
    | uu____174 -> []
let is_definition_of:
  FStar_Ident.ident -> FStar_Parser_AST.decl -> Prims.bool =
  fun x  ->
    fun d  ->
      let uu____183 = definition_lids d in
      FStar_Util.for_some (id_eq_lid x) uu____183
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
           | FStar_Parser_AST.Tycon (uu____230,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___207_265  ->
                       match uu___207_265 with
                       | (FStar_Parser_AST.TyconAbstract uu____272,uu____273)
                           -> true
                       | uu____288 -> false))
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
                 let uu____317 =
                   FStar_All.pipe_right def_ids
                     (FStar_Util.for_some
                        (fun y  ->
                           FStar_All.pipe_right iface_tl
                             (FStar_Util.for_some
                                (is_val y.FStar_Ident.ident)))) in
                 (if uu____317
                  then
                    let uu____332 =
                      let uu____333 =
                        let uu____338 =
                          let uu____339 =
                            let uu____340 =
                              FStar_All.pipe_right def_ids
                                (FStar_List.map FStar_Ident.string_of_lid) in
                            FStar_All.pipe_right uu____340
                              (FStar_String.concat ", ") in
                          FStar_Util.format2
                            "Expected the definition of %s to precede %s"
                            x.FStar_Ident.idText uu____339 in
                        (uu____338, (impl.FStar_Parser_AST.drange)) in
                      FStar_Errors.Error uu____333 in
                    FStar_Exn.raise uu____332
                  else (iface1, [impl]))
               else
                 (let mutually_defined_with_x =
                    FStar_All.pipe_right def_ids
                      (FStar_List.filter
                         (fun y  -> Prims.op_Negation (id_eq_lid x y))) in
                  let rec aux mutuals iface2 =
                    match (mutuals, iface2) with
                    | ([],uu____407) -> ([], iface2)
                    | (uu____418::uu____419,[]) -> ([], [])
                    | (y::ys,iface_hd1::iface_tl1) ->
                        if is_val y.FStar_Ident.ident iface_hd1
                        then
                          let uu____450 = aux ys iface_tl1 in
                          (match uu____450 with
                           | (val_ys,iface3) ->
                               ((iface_hd1 :: val_ys), iface3))
                        else
                          (let uu____482 =
                             let uu____483 =
                               FStar_List.tryFind
                                 (is_val y.FStar_Ident.ident) iface_tl1 in
                             FStar_All.pipe_left FStar_Option.isSome
                               uu____483 in
                           if uu____482
                           then
                             let uu____496 =
                               let uu____497 =
                                 let uu____502 =
                                   let uu____503 =
                                     FStar_Parser_AST.decl_to_string
                                       iface_hd1 in
                                   let uu____504 =
                                     FStar_Ident.string_of_lid y in
                                   FStar_Util.format2
                                     "%s is out of order with the definition of %s"
                                     uu____503 uu____504 in
                                 (uu____502,
                                   (iface_hd1.FStar_Parser_AST.drange)) in
                               FStar_Errors.Error uu____497 in
                             FStar_Exn.raise uu____496
                           else aux ys iface2) in
                  let uu____514 = aux mutually_defined_with_x iface_tl in
                  match uu____514 with
                  | (take_iface,rest_iface) ->
                      (rest_iface,
                        (FStar_List.append (iface_hd :: take_iface) [impl])))
           | uu____545 ->
               let uu____546 = prefix_with_iface_decls iface_tl impl in
               (match uu____546 with
                | (iface2,ds) -> (iface2, (iface_hd :: ds))))
let check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    let rec aux iface2 =
      match iface2 with
      | [] -> ()
      | hd1::tl1 ->
          (match hd1.FStar_Parser_AST.d with
           | FStar_Parser_AST.Tycon (uu____599,tys) when
               FStar_All.pipe_right tys
                 (FStar_Util.for_some
                    (fun uu___208_634  ->
                       match uu___208_634 with
                       | (FStar_Parser_AST.TyconAbstract uu____641,uu____642)
                           -> true
                       | uu____657 -> false))
               ->
               FStar_Exn.raise
                 (FStar_Errors.Error
                    ("Interface contains an abstract 'type' declaration; use 'val' instead",
                      (hd1.FStar_Parser_AST.drange)))
           | FStar_Parser_AST.Val (x,t) ->
               let uu____666 = FStar_Util.for_some (is_definition_of x) tl1 in
               if uu____666
               then
                 let uu____667 =
                   let uu____668 =
                     let uu____673 =
                       FStar_Util.format2
                         "'val %s' and 'let %s' cannot both be provided in an interface"
                         x.FStar_Ident.idText x.FStar_Ident.idText in
                     (uu____673, (hd1.FStar_Parser_AST.drange)) in
                   FStar_Errors.Error uu____668 in
                 FStar_Exn.raise uu____667
               else
                 (let uu____675 =
                    FStar_All.pipe_right hd1.FStar_Parser_AST.quals
                      (FStar_List.contains FStar_Parser_AST.Assumption) in
                  if uu____675
                  then
                    FStar_Exn.raise
                      (FStar_Errors.Error
                         ("Interfaces cannot use `assume val x : t`; just write `val x : t` instead",
                           (hd1.FStar_Parser_AST.drange)))
                  else ())
           | uu____677 -> ()) in
    aux iface1;
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.TopLevelModule uu____686 -> false
            | uu____687 -> true))
let rec ml_mode_prefix_with_iface_decls:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelLet (uu____716,defs) ->
          let xs = FStar_Parser_AST.lids_of_let defs in
          let uu____733 =
            FStar_List.partition
              (fun d  ->
                 FStar_All.pipe_right xs
                   (FStar_Util.for_some
                      (fun x  -> is_val x.FStar_Ident.ident d))) iface1 in
          (match uu____733 with
           | (val_xs,rest_iface) ->
               (rest_iface, (FStar_List.append val_xs [impl])))
      | uu____770 -> (iface1, [impl])
let ml_mode_check_initial_interface:
  FStar_Parser_AST.decl Prims.list -> FStar_Parser_AST.decl Prims.list =
  fun iface1  ->
    FStar_All.pipe_right iface1
      (FStar_List.filter
         (fun d  ->
            match d.FStar_Parser_AST.d with
            | FStar_Parser_AST.Val uu____792 -> true
            | uu____797 -> false))
let prefix_one_decl:
  FStar_Parser_AST.decl Prims.list ->
    FStar_Parser_AST.decl ->
      (FStar_Parser_AST.decl Prims.list,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun iface1  ->
    fun impl  ->
      match impl.FStar_Parser_AST.d with
      | FStar_Parser_AST.TopLevelModule uu____826 -> (iface1, [impl])
      | uu____831 ->
          let uu____832 = FStar_Options.ml_ish () in
          if uu____832
          then ml_mode_prefix_with_iface_decls iface1 impl
          else prefix_with_iface_decls iface1 impl
let initialize_interface:
  FStar_Ident.lident ->
    FStar_Parser_AST.decl Prims.list ->
      FStar_ToSyntax_Env.env -> FStar_ToSyntax_Env.env
  =
  fun mname  ->
    fun l  ->
      fun env  ->
        let decls =
          let uu____861 = FStar_Options.ml_ish () in
          if uu____861
          then ml_mode_check_initial_interface l
          else check_initial_interface l in
        let uu____865 = FStar_ToSyntax_Env.iface_decls env mname in
        match uu____865 with
        | FStar_Pervasives_Native.Some uu____870 ->
            let uu____875 =
              let uu____876 =
                let uu____881 =
                  let uu____882 = FStar_Ident.string_of_lid mname in
                  FStar_Util.format1
                    "Interface %s has already been processed" uu____882 in
                (uu____881, (FStar_Ident.range_of_lid mname)) in
              FStar_Errors.Error uu____876 in
            FStar_Exn.raise uu____875
        | FStar_Pervasives_Native.None  ->
            FStar_ToSyntax_Env.set_iface_decls env mname decls
let prefix_with_interface_decls:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.decl ->
      (FStar_ToSyntax_Env.env,FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun impl  ->
      let uu____905 =
        let uu____910 = FStar_ToSyntax_Env.current_module env in
        FStar_ToSyntax_Env.iface_decls env uu____910 in
      match uu____905 with
      | FStar_Pervasives_Native.None  -> (env, [impl])
      | FStar_Pervasives_Native.Some iface1 ->
          let uu____926 = prefix_one_decl iface1 impl in
          (match uu____926 with
           | (iface2,impl1) ->
               let env1 =
                 let uu____952 = FStar_ToSyntax_Env.current_module env in
                 FStar_ToSyntax_Env.set_iface_decls env uu____952 iface2 in
               (env1, impl1))
let interleave_module:
  FStar_ToSyntax_Env.env ->
    FStar_Parser_AST.modul ->
      Prims.bool ->
        (FStar_ToSyntax_Env.env,FStar_Parser_AST.modul)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      fun expect_complete_modul  ->
        match a with
        | FStar_Parser_AST.Interface uu____975 -> (env, a)
        | FStar_Parser_AST.Module (l,impls) ->
            let uu____990 = FStar_ToSyntax_Env.iface_decls env l in
            (match uu____990 with
             | FStar_Pervasives_Native.None  -> (env, a)
             | FStar_Pervasives_Native.Some iface1 ->
                 let uu____1006 =
                   FStar_List.fold_left
                     (fun uu____1030  ->
                        fun impl  ->
                          match uu____1030 with
                          | (iface2,impls1) ->
                              let uu____1058 = prefix_one_decl iface2 impl in
                              (match uu____1058 with
                               | (iface3,impls') ->
                                   (iface3,
                                     (FStar_List.append impls1 impls'))))
                     (iface1, []) impls in
                 (match uu____1006 with
                  | (iface2,impls1) ->
                      let env1 =
                        FStar_ToSyntax_Env.set_iface_decls env l iface2 in
                      let a1 = FStar_Parser_AST.Module (l, impls1) in
                      (match iface2 with
                       | uu____1115::uu____1116 when expect_complete_modul ->
                           let err1 =
                             let uu____1120 =
                               FStar_List.map FStar_Parser_AST.decl_to_string
                                 iface2 in
                             FStar_All.pipe_right uu____1120
                               (FStar_String.concat "\n\t") in
                           let uu____1125 =
                             let uu____1126 =
                               let uu____1131 =
                                 let uu____1132 = FStar_Ident.string_of_lid l in
                                 FStar_Util.format2
                                   "Some interface elements were not implemented by module %s:\n\t%s"
                                   uu____1132 err1 in
                               (uu____1131, (FStar_Ident.range_of_lid l)) in
                             FStar_Errors.Error uu____1126 in
                           FStar_Exn.raise uu____1125
                       | uu____1137 -> (env1, a1))))